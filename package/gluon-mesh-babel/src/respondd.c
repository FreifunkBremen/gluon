/*
   Copyright (c) 2016, Matthias Schiffer <mschiffer@universe-factory.net>
   All rights reserved.

   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice,
   this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation
   and/or other materials provided with the distribution.

   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
   AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
   IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
   DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
   FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
   DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
   SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
   CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
   OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
   */


#include <respondd.h>

#include <iwinfo.h>
#include <json-c/json.h>
#include <libgluonutil.h>
#include <uci.h>
#include <sys/select.h>
#include <linux/rtnetlink.h>
#include <pthread.h>


#include <alloca.h>
#include <glob.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include <arpa/inet.h>
#include <net/if.h>
#include <netinet/in.h>

#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <ifaddrs.h>

#include <linux/ethtool.h>
#include <linux/if_addr.h>
#include <linux/sockios.h>

#include <netdb.h>
#include "errno.h"
#include <libbabelhelper/babelhelper.h>

#include <libubox/blobmsg_json.h>
#include "libubus.h"

#define _STRINGIFY(s) #s
#define STRINGIFY(s) _STRINGIFY(s)
#include <stdlib.h>

#define MAX_INACTIVITY 60000

#define SOCKET_INPUT_BUFFER_SIZE 255
#define BABEL_PORT 33123
#define VPN_INTERFACE "mesh-vpn"
#define l3rdctl "/var/run/l3roamd.sock"

#define PROTOLEN 32

#define UBUS_TIMEOUT 30
#define UBUS_SOCKET "/var/run/ubus.sock"

static struct babelhelper_ctx bhelper_ctx = {};
static struct json_object *babeld_version = NULL;


static char * model = NULL;
static struct json_object * neighbours = NULL;
static pthread_mutex_t neighbours_lock;
static pthread_t babelmonitor;


struct thread_info {
	pthread_t thread_id;
	int       thread_num;
	char     *argv_string;
};

struct kernel_route {
	struct in6_addr prefix;
	struct in6_addr src_prefix;
	struct in6_addr gw;
	int plen;
	int src_plen; /* no source prefix <=> src_plen == 0 */
	int metric;
	int proto;
	unsigned int ifindex;
	unsigned int table;
};

struct nlrtreq {
	struct nlmsghdr nl;
	struct rtmsg rt;
	char buf[1024];
};

#define ROUTE_PROTO 158

#define STRBUFELEMENTLEN 65
#define KERNEL_INFINITY 9999
static char strbuf[STRBUFELEMENTLEN];

static const char *print_ip(const struct in6_addr *addr) {
	return inet_ntop(AF_INET6, &(addr->s6_addr), strbuf, STRBUFELEMENTLEN);
}

static int rtnl_addattr(struct nlmsghdr *n, size_t maxlen, int type, void *data, int datalen) {
	int len = RTA_LENGTH(datalen);
	struct rtattr *rta;
	if (NLMSG_ALIGN(n->nlmsg_len) + len > maxlen)
		return -1;
	rta = (struct rtattr *)(((char *)n) + NLMSG_ALIGN(n->nlmsg_len));
	rta->rta_type = type;
	rta->rta_len = len;
	memcpy(RTA_DATA(rta), data, datalen);
	n->nlmsg_len = NLMSG_ALIGN(n->nlmsg_len) + len;
	return 0;
}

static void rtmgr_rtnl_talk(int fd, struct nlmsghdr *req) {
	struct sockaddr_nl nladdr = {.nl_family = AF_NETLINK};

	struct iovec iov = {req, 0};
	struct msghdr msg = {&nladdr, sizeof(nladdr), &iov, 1, NULL, 0, 0};

	iov.iov_len = req->nlmsg_len;

	if (sendmsg(fd, &msg, 0) < 0) {
		perror("sendmsg on rtmgr_rtnl_talk()");
	}
}

static void get_route(int fd, const int ifindex, struct in6_addr *address, const int prefix_length) {
	struct nlrtreq req = {
		.nl = {
			.nlmsg_type = RTM_GETROUTE,
			.nlmsg_flags = NLM_F_REQUEST,
			.nlmsg_len = NLMSG_LENGTH(sizeof(struct rtmsg)),
		},
		.rt = {
			.rtm_family = AF_INET6,
			.rtm_protocol = ROUTE_PROTO,
			.rtm_scope = RT_SCOPE_UNIVERSE,
			.rtm_type = RTN_UNICAST,
			.rtm_dst_len = prefix_length
		},
	};

	rtnl_addattr(&req.nl, sizeof(req), RTA_DST, (void *)address, sizeof(struct in6_addr));

	if (ifindex > 0 )
		rtnl_addattr(&req.nl, sizeof(req), RTA_OIF, (void *)&ifindex, sizeof(ifindex));

	rtmgr_rtnl_talk(fd, (struct nlmsghdr *)&req);
}

static int parse_kernel_route_rta(struct rtmsg *rtm, int len, struct kernel_route *route) {
	len -= NLMSG_ALIGN(sizeof(*rtm));

	memset(route, 0, sizeof(struct kernel_route));
	route->proto = rtm->rtm_protocol;

	for (struct rtattr *rta = RTM_RTA(rtm); RTA_OK(rta, len); rta = RTA_NEXT(rta, len)) {
		switch (rta->rta_type) {
			case RTA_DST:
				route->plen = rtm->rtm_dst_len;
				memcpy(route->prefix.s6_addr, RTA_DATA(rta), 16);
				break;
			case RTA_SRC:
				route->src_plen = rtm->rtm_src_len;
				memcpy(route->src_prefix.s6_addr, RTA_DATA(rta), 16);
				break;
			case RTA_GATEWAY:
				memcpy(route->gw.s6_addr, RTA_DATA(rta), 16);
				break;
			case RTA_OIF:
				route->ifindex = *(int *)RTA_DATA(rta);
				break;
			case RTA_PRIORITY:
				route->metric = *(int *)RTA_DATA(rta);
				if (route->metric < 0 || route->metric > KERNEL_INFINITY)
					route->metric = KERNEL_INFINITY;
				break;
			default:
				break;
		}
	}

	return 1;
}

static bool handle_kernel_routes(const struct nlmsghdr *nh, struct kernel_route *route) {
	int len = nh->nlmsg_len;
	struct rtmsg *rtm;

	rtm = (struct rtmsg *)NLMSG_DATA(nh);
	len -= NLMSG_LENGTH(0);

	/* Ignore cached routes, advertised by some kernels (linux 3.x). */
	if (rtm->rtm_flags & RTM_F_CLONED)
		return false;

	if (parse_kernel_route_rta(rtm, len, route) < 0)
		return false;

	return true;
}

static bool rtnl_handle_msg(const struct nlmsghdr *nh, struct kernel_route *route) {
	if (nh->nlmsg_type == RTM_NEWROUTE) {
		handle_kernel_routes(nh, route);
		if ( ! (route->plen == 0 && route->metric >= KERNEL_INFINITY))
			return true;
	}
	return false;
}

static struct json_object * get_default_route(void) {

	struct json_object *ret = json_object_new_object();
	int nlfd = socket(AF_NETLINK, SOCK_RAW, NETLINK_ROUTE);
	if (nlfd < 0) {
		perror("can't open RTNL socket");
		return NULL;
	}
	struct sockaddr_nl snl = {
		.nl_family = AF_NETLINK, .nl_groups = RTMGRP_IPV6_ROUTE,
	};

	if (bind(nlfd, (struct sockaddr *)&snl, sizeof(snl)) < 0)
		perror("can't bind RTNL socket");

	struct in6_addr addr = { };
	inet_pton(AF_INET6, "2000::/3", &addr);

	get_route(nlfd, 0, &addr, 3);

	uint8_t readbuffer[8192];
	int count = recv(nlfd, readbuffer, sizeof(readbuffer), 0);

	struct nlmsghdr *nh;
	struct nlmsgerr *ne;
	struct kernel_route route;

	nh = (struct nlmsghdr *)readbuffer;
	if (NLMSG_OK(nh, count)) {
		switch (nh->nlmsg_type) {
			case NLMSG_DONE:
				break;
			case NLMSG_ERROR:
				perror("handling netlink error-message");
				ne = NLMSG_DATA(nh);
				if (ne->error <= 0)
					break;
				/* Falls through. */
			default:
				if (rtnl_handle_msg(nh, &route) == true) {
					json_object_object_add(ret, "src", json_object_new_string(print_ip(&route.src_prefix)));
					json_object_object_add(ret, "via", json_object_new_string(print_ip(&route.gw)));
					char ifname[IFNAMSIZ];
					json_object_object_add(ret, "interface", json_object_new_string(if_indextoname(route.ifindex, ifname)));
				}
				break;
		}
	}

	close(nlfd);
	return ret;
}

static int babeld_connect() {
	int fd=-1;
	fd_set rfds;
	FD_ZERO(&rfds);

	printf("connecting to babeld\n");

	do {
		fd = babelhelper_babel_connect(BABEL_PORT);
		if (fd < 0) {
			fprintf(stderr, "Connecting to babel socket failed. Retrying.\n");
			usleep(1000000);
		}
	} while (fd < 0);

	FD_SET(fd, &rfds);

	// receive and ignore babel header
	while (true) {
		if ( babelhelper_input_pump(&bhelper_ctx, fd, NULL, babelhelper_discard_response))
			break;

		if (select(fd +1, &rfds, NULL, NULL, NULL) < 0) {
			perror("select (babel header):");
		};
	}


	int amount = 0;
	while (amount != 8 ) {
		amount = babelhelper_sendcommand(&bhelper_ctx, fd, "monitor\n");
	}

	return fd;
}

static void obtain_if_addr(const char *ifname, char *lladdr) {
	struct ifaddrs *ifaddr, *ifa;
	int family, n;

	if (getifaddrs(&ifaddr) == -1) {
		perror("getifaddrs");
		exit(EXIT_FAILURE);
	}

	for (ifa = ifaddr, n = 0; ifa != NULL; ifa = ifa->ifa_next, n++) {
		if (ifa->ifa_addr == NULL)
			continue;

		family = ifa->ifa_addr->sa_family;

		if ( (family == AF_INET6) && ( ! strncmp(ifname, ifa->ifa_name, strlen(ifname)) ) ) {
			char lhost[INET6_ADDRSTRLEN];
			struct in6_addr *address = &((struct sockaddr_in6*)ifa->ifa_addr)->sin6_addr;
			if (inet_ntop(AF_INET6, address, lhost, INET6_ADDRSTRLEN) == NULL) {
				fprintf(stderr, "obtain_if_addr: could not convert ip to string\n");
				goto cleanup;
			}

			if (! strncmp("fe80:", lhost, 5) ) {
				snprintf( lladdr, NI_MAXHOST, "%s", lhost );
				goto cleanup;
			}
		}
	}

cleanup:
	freeifaddrs(ifaddr);
}


static void add_neighbour(char **data) {
	struct json_object *neigh = json_object_new_object();

	if (data[RXCOST])
		json_object_object_add(neigh, "rxcost", json_object_new_int(atoi(data[RXCOST])));
	if (data[TXCOST])
		json_object_object_add(neigh, "txcost", json_object_new_int(atoi(data[TXCOST])));
	if (data[COST])
		json_object_object_add(neigh, "cost", json_object_new_int(atoi(data[COST])));
	if (data[REACH])
		json_object_object_add(neigh, "reachability", json_object_new_double(strtod(data[REACH], NULL)));

	struct json_object *nif = 0;

	if (data[IF] && !json_object_object_get_ex(neighbours, data[IF], &nif)) {
		char str_ip[NI_MAXHOST] = {};
		obtain_if_addr( (const char*)data[IF], str_ip );

		nif = json_object_new_object();

		json_object_object_add(nif, "ll-addr", json_object_new_string(str_ip));
		json_object_object_add(nif, "protocol", json_object_new_string("babel"));
		json_object_object_add(neighbours, data[IF], nif);
	}

	struct json_object *nif_neighbours = 0;
	if (!json_object_object_get_ex(nif, "neighbours", &nif_neighbours)) {
		nif_neighbours = json_object_new_object();
		json_object_object_add(nif, "neighbours", nif_neighbours);
	}

	json_object_object_add(nif_neighbours, data[ADDRESS], neigh);
}

static void del_neighbour(char **data) {
	struct json_object *nif = 0;
	if (json_object_object_get_ex(neighbours, data[IF], &nif)) {
		struct json_object *neighbour = 0;
		if (json_object_object_get_ex(nif, "neighbours", &neighbour)) {
			json_object_object_del(neighbour, data[ADDRESS]);
		}
	}
}


static bool handle_neighbour(char **data, void *obj) {
	pthread_mutex_lock(&neighbours_lock);
	if (data[NEIGHBOUR]) {
		if (strncmp(data[VERB], "add", 3) == 0 ) {
			del_neighbour(data);
			add_neighbour(data);
		} else if (strncmp(data[VERB], "del", 3) == 0 ) {
			del_neighbour(data);
		} else if (strncmp(data[VERB], "change", 6) == 0 ) {
			del_neighbour(data);
			add_neighbour(data);
		}
	}
	pthread_mutex_unlock(&neighbours_lock);

	return false;
}

static bool babel_lineprocessor(char **data, void *object) {
	return handle_neighbour(data, object);
}

static void *babeld_monitor_thread_start(void *arg) {
	printf("created babel monitor thread\n");
	while (true) {
		int babelfd = babeld_connect();

		fd_set rfds;
		FD_ZERO(&rfds);
		FD_SET(babelfd, &rfds);

		while (true) {
			if ( babelhelper_input_pump(&bhelper_ctx, babelfd, NULL, babel_lineprocessor) < 0 ) {
				perror("input pump");
				break;
			}

			if (select(babelfd + 1, &rfds, NULL, NULL, NULL) < 0) {
				perror("select (babel data):");
				break;
			};
		}
		close(babelfd);
	}
	return NULL;
}

static char*  get_line_from_run(const char* command) {
	FILE *fp;
	char *line = NULL;
	size_t len = 0;

	fp = popen(command, "r");

	if (fp != NULL) {
		ssize_t r = getline(&line, &len, fp);
		if (r >= 0) {
			len = strlen(line);

			if (len && line[len-1] == '\n')
				line[len-1] = 0;
		}
		else {
			free(line);
			line = NULL;
		}

		pclose(fp);
	}
	return line;
}

__attribute__((constructor)) static void init(void) {

	if (pthread_mutex_init(&neighbours_lock, NULL) != 0) {
		perror("mutex init failed for neighbours");
	}

	neighbours = json_object_new_object();

	char *version = get_line_from_run("exec babeld -V 2>&1");
	babeld_version = gluonutil_wrap_string(version);
	free(version);

        model = gluonutil_read_line("/tmp/sysinfo/model");

	if (pthread_create(&babelmonitor, NULL, &babeld_monitor_thread_start, NULL) < 0 ) {
		perror("error on pthread_create for babel monitor");
	}
}

__attribute__((destructor)) static void deinit(void) {
	pthread_join(babelmonitor, NULL);
	pthread_mutex_destroy(&neighbours_lock);
}

static struct json_object * get_addresses(void) {
	char *primarymac = gluonutil_get_sysconfig("primary_mac");
	char *address = malloc(INET6_ADDRSTRLEN+1);

	if (!address) {
		fprintf(stderr, "Could not allocate memory for ipv6 address, not adding addresses to json data.\n");
		goto free;
	}

	char node_prefix_str[INET6_ADDRSTRLEN+1];
	struct in6_addr node_prefix = {};
	struct json_object *retval = json_object_new_array();

	if (!gluonutil_get_node_prefix6(&node_prefix)) {
		fprintf(stderr, "get_addresses: could not obtain mesh-prefix from site.conf. Not adding addresses to json data\n");
		goto free;
	}

	if (inet_ntop(AF_INET6, &(node_prefix.s6_addr), node_prefix_str, INET6_ADDRSTRLEN) == NULL) {
		fprintf(stderr, "get_addresses: could not convert mesh-prefix from site.conf to string\n");
		goto free;
	}

	char *prefix_addresspart = strndup(node_prefix_str, INET6_ADDRSTRLEN);
	if (!prefix_addresspart) {
		fprintf(stderr, "could not allocate memory to hold node_prefix_str. Not adding address to json data\n");
		goto free;
	}

	if (! babelhelper_generateip_str(address, primarymac, prefix_addresspart) ) {
		fprintf(stderr, "IP-address could not be generated by babelhelper\n");
		goto free;
	}

	json_object_array_add(retval, json_object_new_string(address));

free:
	free(prefix_addresspart);
	free(address);
	free(primarymac);

	return retval;
}

static bool interface_file_exists(const char *ifname, const char *name) {
	const char *format = "/sys/class/net/%s/%s";
	char path[strlen(format) + strlen(ifname) + strlen(name)+1];
	snprintf(path, sizeof(path), format, ifname, name);

	return !access(path, F_OK);
}

static void mesh_add_if(const char *ifname, struct json_object *wireless,
		struct json_object *tunnel, struct json_object *other) {
	char str_ip[NI_MAXHOST] = {};

	obtain_if_addr(ifname, str_ip);

	struct json_object *address = json_object_new_string(str_ip);

	if (interface_file_exists(ifname, "wireless"))
		json_object_array_add(wireless, address);
	else if (interface_file_exists(ifname, "tun_flags"))
		json_object_array_add(tunnel, address);
	else
		json_object_array_add(other, address);
}

static void blobmsg_handle_list(struct blob_attr *attr, int len, bool array, struct json_object *wireless, struct json_object *tunnel, struct json_object *other);

static void blobmsg_handle_element(struct blob_attr *attr, bool head, char **ifname, char **proto, struct json_object *wireless, struct json_object *tunnel, struct json_object *other) {
	void *data;

	if (!blobmsg_check_attr(attr, false))
		return;

	data = blobmsg_data(attr);

	switch (blob_id(attr)) {
		case  BLOBMSG_TYPE_STRING:
			if (!strncmp(blobmsg_name(attr),"device", 6)) {
				free(*ifname);
				*ifname = strndup(data, IFNAMSIZ);
			} else if (!strncmp(blobmsg_name(attr), "proto", 5)) {
				free(*proto);
				*proto = strndup(data, PROTOLEN);
			}
			return;
		case BLOBMSG_TYPE_ARRAY:
			blobmsg_handle_list(data, blobmsg_data_len(attr), true, wireless, tunnel, other);
			return;
		case BLOBMSG_TYPE_TABLE:
			blobmsg_handle_list(data, blobmsg_data_len(attr), false, wireless, tunnel, other);
	}
}

static void blobmsg_handle_list(struct blob_attr *attr, int len, bool array, struct json_object *wireless, struct json_object *tunnel, struct json_object *other) {
	struct blob_attr *pos;
	int rem = len;

	char *ifname = NULL;
	char *proto = NULL;

	__blob_for_each_attr(pos, attr, rem) {
		blobmsg_handle_element(pos, array, &ifname, &proto, wireless, tunnel, other);
	}

	if (ifname && proto) {
		if (!strncmp(proto, "gluon_mesh", 10)) {
			mesh_add_if(ifname, wireless, tunnel, other);
		}
	}
	free(ifname);
	free(proto);
}

static void receive_call_result_data(struct ubus_request *req, int type, struct blob_attr *msg) {
	struct json_object *ret = json_object_new_object();
	struct json_object *wireless = json_object_new_array();
	struct json_object *tunnel = json_object_new_array();
	struct json_object *other = json_object_new_array();

	if (!ret || !wireless || !tunnel || !other) {
		json_object_put(wireless);
		json_object_put(tunnel);
		json_object_put(other);
		json_object_put(ret);
		return;
	}

	if (!msg) {
		printf("empty message\n");
		return;
	}

	blobmsg_handle_list(blobmsg_data(msg), blobmsg_data_len(msg), false, wireless, tunnel, other);

	json_object_object_add(ret, "wireless", wireless);
	json_object_object_add(ret, "tunnel", tunnel);
	json_object_object_add(ret, "other", other);

	*((struct json_object**)(req->priv)) = ret;
}

static struct json_object * get_mesh_ifs() {
	struct ubus_context *ubus_ctx;
	struct json_object *ret = NULL;
	struct blob_buf b = {};

	unsigned int id=8;

	ubus_ctx = ubus_connect(UBUS_SOCKET);
	if (!ubus_ctx) {
		fprintf(stderr,"could not connect to ubus, not providing mesh-data\n");
		goto end;
	}

	blob_buf_init(&b, 0);
	ubus_lookup_id(ubus_ctx, "network.interface", &id);
	int uret = ubus_invoke(ubus_ctx, id, "dump", b.head, receive_call_result_data, &ret, UBUS_TIMEOUT * 1000);

	if (uret > 0)
		fprintf(stderr, "ubus command failed: %s\n", ubus_strerror(uret));
	else if (uret == -2)
		fprintf(stderr, "invalid call, exiting\n");

	blob_buf_free(&b);

end:
	ubus_free(ubus_ctx);
	return ret;
}

static struct json_object * get_mesh(void) {
	struct json_object *ret = json_object_new_object();
	struct json_object *interfaces = NULL;
	interfaces = json_object_new_object();
	json_object_object_add(interfaces, "interfaces", get_mesh_ifs());
	json_object_object_add(ret, "babel", interfaces);
	return ret;
}


static struct json_object * get_babeld_version(void) {
	return babeld_version ? json_object_get(babeld_version) : json_object_new_string("unknown");
}

static struct json_object * respondd_provider_nodeinfo(void) {
	bhelper_ctx.debug = false;
	struct json_object *ret = json_object_new_object();

	struct json_object *network = json_object_new_object();
	json_object_object_add(network, "addresses", get_addresses());
	json_object_object_add(network, "mesh", get_mesh());
	json_object_object_add(ret, "network", network);

	struct json_object *software = json_object_new_object();
	struct json_object *software_babeld = json_object_new_object();
	json_object_object_add(software_babeld, "version", get_babeld_version());
	json_object_object_add(software, "babeld", software_babeld);
	json_object_object_add(ret, "software", software);

	return ret;
}

static uint64_t getnumber(const char *ifname, const char *stat) {
	const char *format = "/sys/class/net/%s/statistics/%s";
	char path[strlen(format) + strlen(ifname) + strlen(stat) + 1];
	snprintf(path, sizeof(path), format, ifname, stat);
	if (! access(path, F_OK)) {
		char *line=gluonutil_read_line(path);
		long long i=0;
		if (line)
			i = atoll(line);
		free(line);
		return(i);
	}
	return 0;
}

static struct json_object * get_traffic_if(char *ifname) {
	struct json_object *ret = NULL;
	struct json_object *rx = json_object_new_object();
	struct json_object *tx = json_object_new_object();

	json_object_object_add(rx, "packets", json_object_new_int64(getnumber(ifname, "rx_packets")));
	json_object_object_add(rx, "bytes", json_object_new_int64(getnumber(ifname, "rx_bytes")));
	json_object_object_add(rx, "dropped", json_object_new_int64(getnumber(ifname, "rx_dropped")));
	json_object_object_add(tx, "packets", json_object_new_int64(getnumber(ifname, "tx_packets")));
	json_object_object_add(tx, "dropped", json_object_new_int64(getnumber(ifname, "tx_dropped")));
	json_object_object_add(tx, "bytes", json_object_new_int64(getnumber(ifname, "tx_bytes")));

	ret = json_object_new_object();
	json_object_object_add(ret, "rx", rx);
	json_object_object_add(ret, "tx", tx);
	return ret;
}

static struct json_object * get_traffic(void) {
	struct json_object *ret = get_traffic_if("br-client"); // keep for compatibility
	json_object_object_add(ret, "local-node", get_traffic_if("local-node"));
	json_object_object_add(ret, "br-client", get_traffic_if("br-client"));

	// TODO: add traffic stats for all mesh interfaces

	return ret;
}

static void count_iface_stations(size_t *wifi24, size_t *wifi5, const char *ifname) {
	const struct iwinfo_ops *iw = iwinfo_backend(ifname);
	if (!iw)
		return;

	int freq;
	if (iw->frequency(ifname, &freq) < 0)
		return;

	size_t *wifi;
	if (freq >= 2400 && freq < 2500)
		wifi = wifi24;
	else if (freq >= 5000 && freq < 6000)
		wifi = wifi5;
	else
		return;

	int len;
	char buf[IWINFO_BUFSIZE];
	if (iw->assoclist(ifname, buf, &len) < 0)
		return;

	struct iwinfo_assoclist_entry *entry;
	for (entry = (struct iwinfo_assoclist_entry *)buf; (char*)(entry+1) <= buf + len; entry++) {
		if (entry->inactive > MAX_INACTIVITY)
			continue;

		(*wifi)++;
	}
}

static void count_stations(size_t *wifi24, size_t *wifi5) {
	struct uci_context *ctx = uci_alloc_context();
	ctx->flags &= ~UCI_FLAG_STRICT;


	struct uci_package *p;
	if (uci_load(ctx, "wireless", &p))
		goto end;


	struct uci_element *e;
	uci_foreach_element(&p->sections, e) {
		struct uci_section *s = uci_to_section(e);
		if (strcmp(s->type, "wifi-iface"))
			continue;

		const char *network = uci_lookup_option_string(ctx, s, "network");
		if (!network || strcmp(network, "client"))
			continue;

		const char *mode = uci_lookup_option_string(ctx, s, "mode");
		if (!mode || strcmp(mode, "ap"))
			continue;

		const char *ifname = uci_lookup_option_string(ctx, s, "ifname");
		if (!ifname)
			continue;

		count_iface_stations(wifi24, wifi5, ifname);
	}

end:
	uci_free_context(ctx);
}

static int json_parse_get_clients(json_object * object) {
	if (object) {
		json_object_object_foreach(object, key, val) {
			if (! strncmp("clients", key, 7)) {
				return(json_object_get_int(val));
			}
		}
	}
	return(-1);
}

static int ask_l3roamd_for_client_count() {
	struct sockaddr_un addr;
	const char *socket_path = "/var/run/l3roamd.sock";
	int fd;
	int clients = -1;
	char *buf = NULL;
	int already_read = 0;

	if ((fd = socket(AF_UNIX, SOCK_STREAM, 0)) == -1) {
		fprintf(stderr, "could not setup l3roamd-control-socket\n");
		return(-1);
	}

	memset(&addr, 0, sizeof(addr));
	addr.sun_family = AF_UNIX;
	strncpy(addr.sun_path, socket_path, sizeof(addr.sun_path)-1);

	if (connect(fd, (struct sockaddr*)&addr, sizeof(addr)) == -1) {
		fprintf(stderr, "connect error\n");
		return(-1);
	}

	if (write(fd,"get_clients\n",12) != 12) {
		perror("could not send command to l3roamd socket: get_clients");
		goto end;
	}

	int rc = 0;
	do {
		char *buf_tmp = realloc(buf, already_read + SOCKET_INPUT_BUFFER_SIZE + 1);
		if (buf_tmp == NULL) {
			fprintf(stderr, "could not allocate memory for buffer\n");
			goto end;
		}
		buf = buf_tmp;

		rc = read(fd, &buf[already_read], SOCKET_INPUT_BUFFER_SIZE);
		already_read+=rc;
		if (rc < 0) {
			perror("error on read in ask_l3roamd_for_client_count():");
			goto end;
		}
		buf[already_read]='\0';
	} while (rc == SOCKET_INPUT_BUFFER_SIZE);

	json_object * jobj = json_tokener_parse(buf);
	clients = json_parse_get_clients(jobj);
	json_object_put(jobj);

end:
	free(buf);
	close(fd);

	return clients;
}

static struct json_object * get_clients(void) {
	size_t wifi24 = 0, wifi5 = 0;

	count_stations(&wifi24, &wifi5);

	int total = ask_l3roamd_for_client_count();

	size_t wifi = wifi24 + wifi5;
	struct json_object *ret = json_object_new_object();

	if (total >= 0)
		json_object_object_add(ret, "total", json_object_new_int(total));

	json_object_object_add(ret, "wifi", json_object_new_int(wifi));
	json_object_object_add(ret, "wifi24", json_object_new_int(wifi24));
	json_object_object_add(ret, "wifi5", json_object_new_int(wifi5));
	return ret;
}

static struct json_object * respondd_provider_statistics(void) {
	struct json_object *ret = json_object_new_object();

	json_object_object_add(ret, "clients", get_clients());
	json_object_object_add(ret, "traffic", get_traffic());
	json_object_object_add(ret, "gateway_nexthop", get_default_route());

	return ret;
}

static struct json_object * get_wifi_neighbours(const char *ifname) {
	const struct iwinfo_ops *iw = iwinfo_backend(ifname);
	if (!iw)
		return NULL;

	int len;
	char buf[IWINFO_BUFSIZE];
	if (iw->assoclist(ifname, buf, &len) < 0)
		return NULL;

	struct json_object *wifi_neighbours = json_object_new_object();

	struct iwinfo_assoclist_entry *entry;
	for (entry = (struct iwinfo_assoclist_entry *)buf; (char*)(entry+1) <= buf + len; entry++) {
		if (entry->inactive > MAX_INACTIVITY)
			continue;

		struct json_object *obj = json_object_new_object();

		json_object_object_add(obj, "signal", json_object_new_int(entry->signal));
		json_object_object_add(obj, "noise", json_object_new_int(entry->noise));
		json_object_object_add(obj, "inactive", json_object_new_int(entry->inactive));

		char mac[18];
		snprintf(mac, sizeof(mac), "%02x:%02x:%02x:%02x:%02x:%02x",
				entry->mac[0], entry->mac[1], entry->mac[2],
				entry->mac[3], entry->mac[4], entry->mac[5]);

		json_object_object_add(wifi_neighbours, mac, obj);
	}

	struct json_object *ret = json_object_new_object();

	if (json_object_object_length(wifi_neighbours))
		json_object_object_add(ret, "neighbours", wifi_neighbours);
	else
		json_object_put(wifi_neighbours);

	return ret;
}

static struct json_object * get_wifi(void) {

	struct uci_context *ctx = uci_alloc_context();
	ctx->flags &= ~UCI_FLAG_STRICT;

	struct json_object *ret = json_object_new_object();

	struct uci_package *p;
	if (uci_load(ctx, "network", &p))
		goto end;


	struct uci_element *e;
	uci_foreach_element(&p->sections, e) {
		struct uci_section *s = uci_to_section(e);
		if (strcmp(s->type, "interface"))
			continue;

		const char *proto = uci_lookup_option_string(ctx, s, "proto");
		if (!proto || strncmp(proto, "gluon_mesh", 10))
			continue;

		const char *ifname = uci_lookup_option_string(ctx, s, "ifname");
		if (!ifname)
			continue;

		char *ifaddr = gluonutil_get_interface_address(ifname);
		if (!ifaddr)
			continue;

		struct json_object *wifi_neighbours = get_wifi_neighbours(ifname);
		if (wifi_neighbours)
			json_object_object_add(ret, ifaddr, wifi_neighbours);

		free(ifaddr);
	}

end:
	uci_free_context(ctx);
	return ret;
}

static struct json_object * respondd_provider_neighbours(void) {
	struct json_object *ret = json_object_new_object();

	if (neighbours) {
		pthread_mutex_lock(&neighbours_lock);
		json_object_object_add(ret, "babel", json_object_get(neighbours));
		pthread_mutex_unlock(&neighbours_lock);
	}

	struct json_object *wifi = get_wifi();
	if (wifi)
		json_object_object_add(ret, "wifi", wifi);

	return ret;
}


const struct respondd_provider_info respondd_providers[] = {
	{"nodeinfo", respondd_provider_nodeinfo},
	{"statistics", respondd_provider_statistics},
	{"neighbours", respondd_provider_neighbours},
	{}
};
