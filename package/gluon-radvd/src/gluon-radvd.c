/*
  Copyright (c) 2014, Matthias Schiffer <mschiffer@universe-factory.net>
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


#define _GNU_SOURCE

#include <errno.h>
#include <error.h>
#include <ifaddrs.h>
#include <fcntl.h>
#include <poll.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <arpa/inet.h>

#include <linux/netlink.h>
#include <linux/rtnetlink.h>

#include <net/ethernet.h>
#include <net/if.h>

#include <netinet/in.h>
#include <netinet/icmp6.h>

#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/uio.h>
#include <sys/stat.h>

#include "batadv_query.h"


#define MAX_PREFIXES 8
#define MAX_ROUTES 16
#define MAX_INTERFACES 2

/* These are in seconds */
#define AdvValidLifetime 86400u
#define AdvPreferredLifetime 14400u
#define AdvDefaultLifetime 0u
#define AdvCurHopLimit 64u

#define MinRtrAdvInterval 200u
#define MaxRtrAdvInterval 600u

/* And these in milliseconds */
#define MAX_RA_DELAY_TIME 500u
#define MIN_DELAY_BETWEEN_RAS 3000u


struct icmpv6_opt {
	uint8_t type;
	uint8_t length;
	uint8_t data[6];
};


struct iface {
	bool ok;
	unsigned int ifindex;
	struct in6_addr ifaddr;
	uint8_t mac[6];
};


struct prefix {
	struct in6_addr addr;
	uint32_t preferred_time;
	uint32_t valid_time;
	uint8_t len;
	bool onlink;
	bool manual;
};

struct route {
	struct in6_addr gateway;
	struct prefix *from;
	uint32_t preferred_time;
	uint32_t valid_time;
	uint32_t metric;
	int iface_index;
};


static struct global {
	struct iface iface;

	struct timespec time;
	struct timespec next_advert;
	struct timespec last_advert;

	size_t n_client_ifs;
	int icmp_socks_client[MAX_INTERFACES];
	int icmp_sock_server;
	int rtnl_sock;

	int rtable;
	const char *mesh_iface;

	const char *ifnames_client[MAX_INTERFACES];
	const char *ifname_server;

	size_t n_prefixes;
	struct prefix prefixes[MAX_PREFIXES];
	size_t n_routes;
	struct route routes[MAX_ROUTES];
} G = {
	.rtable = -1,
	.mesh_iface = "bat0",
};


static inline void exit_errno(const char *message) {
	error(1, errno, "error: %s", message);
}

static inline void warn_errno(const char *message) {
	error(0, errno, "warning: %s", message);
}


static inline void update_time(void) {
	clock_gettime(CLOCK_MONOTONIC, &G.time);
}

/* Compares two timespecs and returns true if tp1 is after tp2 */
static inline bool timespec_after(const struct timespec *tp1, const struct timespec *tp2) {
	return (tp1->tv_sec > tp2->tv_sec ||
		(tp1->tv_sec == tp2->tv_sec && tp1->tv_nsec > tp2->tv_nsec));
}

/* Returns (tp1 - tp2) in milliseconds  */
static inline int timespec_diff(const struct timespec *tp1, const struct timespec *tp2) {
	return ((tp1->tv_sec - tp2->tv_sec))*1000 + (tp1->tv_nsec - tp2->tv_nsec)/1e6;
}

static inline void timespec_add(struct timespec *tp, unsigned int ms) {
	tp->tv_sec += ms/1000;
	tp->tv_nsec += (ms%1000) * 1e6;

	if (tp->tv_nsec >= 1e9) {
		tp->tv_nsec -= 1e9;
		tp->tv_sec++;
	}
}

static inline void diff_max_zero(unsigned int *minuend, unsigned int subtrahend) {
	if (*minuend < subtrahend)
		*minuend = 0;
	else
		*minuend -= subtrahend;
}


static uint8_t get_tq_from_ipv6(const struct in6_addr *addr) {
	struct ether_addr *originator;
	struct ether_addr mac;
	if (strcmp(G.mesh_iface, "none") != 0) {
		if (ipv6_to_mac(addr, &mac) >= 0) {
			originator = translate_mac(G.mesh_iface,
						(struct ether_addr *)&mac);
			if (originator)
				return get_tq(G.mesh_iface, originator);
			else
				return 0;
		}
	}
	return 255;
}


static inline int setsockopt_int(int socket, int level, int option, int value) {
	return setsockopt(socket, level, option, &value, sizeof(value));
}


static void init_random(void) {
	unsigned int seed;
	int fd = open("/dev/urandom", O_RDONLY);
	if (fd < 0)
		exit_errno("can't open /dev/urandom");

	if (read(fd, &seed, sizeof(seed)) != sizeof(seed))
		exit_errno("can't read from /dev/urandom");

	close(fd);

	srandom(seed);
}

static inline int rand_range(int min, int max) {
	unsigned int r = (unsigned int)random();
	return (r%(max-min) + min);
}

static int init_icmp_socket(int code) {
	int sock = socket(AF_INET6, SOCK_RAW|SOCK_NONBLOCK, IPPROTO_ICMPV6);
	if (sock < 0)
		exit_errno("can't open ICMP socket");

	setsockopt_int(sock, IPPROTO_RAW, IPV6_CHECKSUM, 2);

	setsockopt_int(sock, IPPROTO_IPV6, IPV6_MULTICAST_HOPS, 255);
	setsockopt_int(sock, IPPROTO_IPV6, IPV6_MULTICAST_LOOP, 1);

	setsockopt_int(sock, IPPROTO_IPV6, IPV6_RECVHOPLIMIT, 1);

	struct icmp6_filter filter;
	ICMP6_FILTER_SETBLOCKALL(&filter);
	ICMP6_FILTER_SETPASS(code, &filter);
	setsockopt(G.icmp_sock_server, IPPROTO_ICMPV6, ICMP6_FILTER, &filter, sizeof(filter));

	return sock;
}

static void init_icmp_server(void) {
	G.icmp_sock_server = init_icmp_socket(ND_ROUTER_SOLICIT);
}

static void init_icmp_client(void) {
	size_t i = 0;
	for (i = 0; i < G.n_client_ifs; i++) {
		G.icmp_socks_client[i] = init_icmp_socket(ND_ROUTER_ADVERT);
		setsockopt(G.icmp_socks_client[i], SOL_SOCKET, SO_BINDTODEVICE, G.ifnames_client[i], strnlen(G.ifnames_client[i], IFNAMSIZ-1));
	}
}

static void init_rtnl(void) {
	G.rtnl_sock = socket(AF_NETLINK, SOCK_DGRAM|SOCK_NONBLOCK, NETLINK_ROUTE);
	if (G.rtnl_sock < 0)
		exit_errno("can't open RTNL socket");

	struct sockaddr_nl snl = {
		.nl_family = AF_NETLINK,
		.nl_groups = RTMGRP_LINK | RTMGRP_IPV6_IFADDR,
	};
	if (bind(G.rtnl_sock, (struct sockaddr *)&snl, sizeof(snl)) < 0)
		exit_errno("can't bind RTNL socket");
}


static void schedule_advert(bool nodelay) {
	struct timespec t = G.time, next_advert_earliest = G.last_advert;

	if (nodelay)
		timespec_add(&t, rand_range(0, MAX_RA_DELAY_TIME));
	else
		timespec_add(&t, rand_range(MinRtrAdvInterval*1000, MaxRtrAdvInterval*1000));

	timespec_add(&next_advert_earliest, MIN_DELAY_BETWEEN_RAS);
	if (timespec_after(&next_advert_earliest, &t))
		t = next_advert_earliest;

	if (!nodelay || timespec_after(&G.next_advert, &t))
		G.next_advert = t;
}


static int join_multicast(void) {
	struct ipv6_mreq mreq = {
		.ipv6mr_multiaddr = {
			.s6_addr = {
				/* all-routers address */
				0xff, 0x02, 0x00, 0x00,
				0x00, 0x00, 0x00, 0x00,
				0x00, 0x00, 0x00, 0x00,
				0x00, 0x00, 0x00, 0x02,
			}
		},
		.ipv6mr_interface = G.iface.ifindex,
	};

	if (setsockopt(G.icmp_sock_server, IPPROTO_IPV6, IPV6_ADD_MEMBERSHIP, &mreq, sizeof(mreq)) == 0) {
		return 2;
	}
	else if (errno != EADDRINUSE) {
		warn_errno("can't join multicast group");
		return 0;
	}

	return 1;
}

static void update_interface(void) {
	struct iface old;

	memcpy(&old, &G.iface, sizeof(struct iface));
	memset(&G.iface, 0, sizeof(struct iface));

	/* Update ifindex */
	G.iface.ifindex = if_nametoindex(G.ifname_server);
	if (!G.iface.ifindex)
		return;

	/* Update MAC address */
	struct ifreq ifr = {};
	strncpy(ifr.ifr_name, G.ifname_server, sizeof(ifr.ifr_name)-1);
	if (ioctl(G.icmp_sock_server, SIOCGIFHWADDR, &ifr) < 0)
		return;

	memcpy(G.iface.mac, ifr.ifr_hwaddr.sa_data, sizeof(G.iface.mac));

	struct ifaddrs *addrs, *addr;
	if (getifaddrs(&addrs) < 0) {
		warn_errno("getifaddrs");
		return;
	}

	memset(&G.iface.ifaddr, 0, sizeof(G.iface.ifaddr));

	for (addr = addrs; addr; addr = addr->ifa_next) {
		if (!addr->ifa_addr || addr->ifa_addr->sa_family != AF_INET6)
			continue;

		const struct sockaddr_in6 *in6 = (const struct sockaddr_in6 *)addr->ifa_addr;
		if (!IN6_IS_ADDR_LINKLOCAL(&in6->sin6_addr))
			continue;

		if (strncmp(addr->ifa_name, G.ifname_server, IFNAMSIZ-1) != 0)
			continue;

		G.iface.ifaddr = in6->sin6_addr;
	}

	freeifaddrs(addrs);

	if (IN6_IS_ADDR_UNSPECIFIED(&G.iface.ifaddr))
		return;

	int joined = join_multicast();
	if (!joined)
		return;

	setsockopt(G.icmp_sock_server, SOL_SOCKET, SO_BINDTODEVICE, G.ifname_server, strnlen(G.ifname_server, IFNAMSIZ-1));

	G.iface.ok = true;

	if (memcmp(&old, &G.iface, sizeof(struct iface)) != 0 || joined == 2)
		schedule_advert(true);
}


static bool handle_rtnl_link(uint16_t type, const struct ifinfomsg *msg) {
	switch (type) {
	case RTM_NEWLINK:
		if (!G.iface.ok)
			return true;

		break;

	case RTM_SETLINK:
		if ((unsigned)msg->ifi_index == G.iface.ifindex)
			return true;

		if (!G.iface.ok)
			return true;

		break;

	case RTM_DELLINK:
		if (G.iface.ok && (unsigned)msg->ifi_index == G.iface.ifindex)
			return true;
	}

	return false;
}

static bool handle_rtnl_addr(uint16_t type, const struct ifaddrmsg *msg) {
	switch (type) {
	case RTM_NEWADDR:
		if (!G.iface.ok && (unsigned)msg->ifa_index == G.iface.ifindex)
			return true;

		break;

	case RTM_DELADDR:
		if (G.iface.ok && (unsigned)msg->ifa_index == G.iface.ifindex)
			return true;
	}

	return false;
}

static bool handle_rtnl_msg(uint16_t type, const void *data) {
	switch (type) {
	case RTM_NEWLINK:
	case RTM_DELLINK:
	case RTM_SETLINK:
		return handle_rtnl_link(type, data);

	case RTM_NEWADDR:
	case RTM_DELADDR:
		return handle_rtnl_addr(type, data);

	default:
		return false;
	}
}

static void handle_rtnl(void) {
	char buffer[4096];

	ssize_t len = recv(G.rtnl_sock, buffer, sizeof(buffer), 0);
	if (len < 0) {
		warn_errno("recv");
		return;
	}

	const struct nlmsghdr *nh;
	for (nh = (struct nlmsghdr *)buffer; NLMSG_OK(nh, len); nh = NLMSG_NEXT(nh, len)) {
		switch (nh->nlmsg_type) {
		case NLMSG_DONE:
			return;

		case NLMSG_ERROR:
			error(1, 0, "error: netlink error");

		default:
			if (handle_rtnl_msg(nh->nlmsg_type, NLMSG_DATA(nh))) {
				update_interface();
				return;
			}
		}
	}
}

static void add_pktinfo(struct msghdr *msg) {
	struct cmsghdr *cmsg = (struct cmsghdr*)((char*)msg->msg_control + msg->msg_controllen);

	cmsg->cmsg_level = IPPROTO_IPV6;
	cmsg->cmsg_type = IPV6_PKTINFO;
	cmsg->cmsg_len = CMSG_LEN(sizeof(struct in6_pktinfo));

	msg->msg_controllen += cmsg->cmsg_len;

	struct in6_pktinfo pktinfo = {
		.ipi6_addr = G.iface.ifaddr,
		.ipi6_ifindex = G.iface.ifindex,
	};

	memcpy(CMSG_DATA(cmsg), &pktinfo, sizeof(pktinfo));
}


static void insert_route(const struct route *route) {
	// TODO
}

static void update_routes(void) {
	size_t i;
	for (i = 0; i < G.n_routes; i++) {
		insert_route(&(G.routes[i]));
	}
}


static void handle_icmp_solicit(const struct msghdr *msg) {
	uint8_t *buffer = msg->msg_iov->iov_base;
	struct sockaddr_in6 *addr = msg->msg_name;
	const struct nd_opt_hdr *opt = (struct nd_opt_hdr *)(buffer + sizeof(struct nd_router_solicit)),
				*end = (struct nd_opt_hdr *)(buffer + msg->msg_iov->iov_len);

	// validate packet according to RFC 4861 section 6.1.1
	for (; opt < end; opt += opt->nd_opt_len) {
		if (opt+1 < end)
			return;

		if (!opt->nd_opt_len)
			return;

		if (opt+opt->nd_opt_len < end)
			return;

		if (opt->nd_opt_type == ND_OPT_SOURCE_LINKADDR && IN6_IS_ADDR_UNSPECIFIED(&(addr->sin6_addr)))
			return;
	}

	if (opt != end)
		return;

	schedule_advert(true);
}

static void handle_icmp_advert(const struct msghdr *msg, int iface_index) {
	struct nd_router_advert *buffer = msg->msg_iov->iov_base;
	struct sockaddr_in6 *addr = msg->msg_name;
	uint32_t metric = 512u;
	size_t n_prefixes;
	struct prefix prefixes[MAX_PREFIXES];
	const struct nd_opt_prefix_info *opt = (struct nd_opt_prefix_info *)(buffer + sizeof(struct nd_router_advert)),
					*end = (struct nd_opt_prefix_info *)(buffer + msg->msg_iov->iov_len);

	// gather routes
	for (; opt < end; opt += opt->nd_opt_pi_len) {
		// validate packet according to RFC 4861 section 6.1.1
		if (opt+1 < end)
			return;

		if (!opt->nd_opt_pi_len)
			return;

		if (opt+opt->nd_opt_pi_len < end)
			return;

		if (opt->nd_opt_pi_type != ND_OPT_PREFIX_INFORMATION)
			continue;

		if (opt->nd_opt_pi_len != sizeof(struct nd_opt_prefix_info))
			return;

		if (opt->nd_opt_pi_prefix_len < 64)
			continue;

		if (!(opt->nd_opt_pi_flags_reserved & ND_OPT_PI_FLAG_AUTO))
			continue;

		if (n_prefixes >= MAX_PREFIXES)
			// we cannot store any more prefixes, but need to
			// validate the rest of the packet, thus no break
			// TODO: warn to syslog
			continue;

		prefixes[n_prefixes] = (struct prefix){
			.addr = opt->nd_opt_pi_prefix,
			.len = opt->nd_opt_pi_prefix_len,
			.onlink = opt->nd_opt_pi_flags_reserved & ND_OPT_PI_FLAG_ONLINK,
			.preferred_time = ntohl(opt->nd_opt_pi_preferred_time),
			.valid_time = ntohl(opt->nd_opt_pi_valid_time),
		};
		n_prefixes++;
	}

	if (opt != end)
		return;


	// determine router preference (RFC 4191)
	switch((buffer->nd_ra_hdr.icmp6_data8[1] & 0x16) >> 3) {
		case 0x01: // high (01b)
			metric -= 128;
			break;
		case 0x03: // low (11b)
			metric += 128;
			break;
	}
	// determine quality of connection to originator
	metric -= get_tq_from_ipv6(&(addr->sin6_addr));
	
	// insert routes
	size_t i, j;
	for (i = 0; i < n_prefixes; i++) {
		for (j = 0; j < G.n_prefixes; j++) {
			if (memcmp(&G.prefixes[j].addr, &(prefixes[i].addr), sizeof(struct in6_addr)))
				continue;

			if (G.prefixes[j].len != prefixes[i].len)
				continue;

			if (!G.prefixes[j].manual) {
				if (G.prefixes[j].valid_time < prefixes[i].valid_time)
					G.prefixes[j].valid_time = prefixes[i].valid_time;

				if (G.prefixes[j].preferred_time < prefixes[i].preferred_time)
					G.prefixes[j].preferred_time = prefixes[i].preferred_time;
			}

			break;
		}
		if (j == G.n_prefixes) {
			if (G.n_prefixes == MAX_PREFIXES)
				// TODO: warn to syslog
				continue;
			memcpy(&(G.prefixes[G.n_prefixes]), &prefixes[i], sizeof(struct prefix));
			G.n_prefixes++;
		}

		struct route route = {
			.from = &G.prefixes[j],
			.metric = metric,
			.preferred_time = prefixes[i].preferred_time,
			.valid_time = prefixes[i].valid_time,
			.iface_index = iface_index,
		};
		memcpy(&route.gateway, &(addr->sin6_addr), sizeof(struct in6_addr));
		for (j = 0; j < G.n_routes; j++) {
			if (memcmp(&G.routes[j].gateway, &route.gateway, sizeof(struct in6_addr)))
				continue;

			if (G.routes[j].from != route.from)
				continue;

			if (G.routes[j].iface_index != route.iface_index)
				continue;

			break;
		}
		if (j == G.n_routes) {
			if (G.n_routes == MAX_ROUTES)
				// TODO: warn to syslog
				continue;
			G.n_routes++;
		}
		memcpy(&(G.routes[j]), &route, sizeof(struct route));
	}

	update_routes();
	schedule_advert(true);
}

static void handle_icmp(int sock, int iface_index) {
	struct sockaddr_in6 addr;

	uint8_t buffer[1500] __attribute__((aligned(8)));
	struct iovec vec = { .iov_base = buffer, .iov_len = sizeof(buffer) };

	uint8_t cbuf[1024] __attribute__((aligned(8)));


	struct msghdr msg = {
		.msg_name = &addr,
		.msg_namelen = sizeof(addr),
		.msg_iov = &vec,
		.msg_iovlen = 1,
		.msg_control = cbuf,
		.msg_controllen = sizeof(cbuf),
	};

	ssize_t len = recvmsg(sock, &msg, 0);

	if (len < (ssize_t)sizeof(struct nd_router_solicit) && len < (ssize_t)sizeof(struct nd_router_advert)) {
		if (len < 0)
			warn_errno("recvmsg");

		return;
	}

	struct cmsghdr *cmsg;
	for (cmsg = CMSG_FIRSTHDR(&msg); cmsg != NULL; cmsg = CMSG_NXTHDR(&msg, cmsg)) {
		if (cmsg->cmsg_level != IPPROTO_IPV6)
			continue;

		if (cmsg->cmsg_type != IPV6_HOPLIMIT)
			continue;

		if (*(int*)CMSG_DATA(cmsg) != 255)
			return;

		break;
	}

	const struct icmp6_hdr *s = (struct icmp6_hdr *)buffer;
	if (s->icmp6_code != 0)
		return;

	switch (s->icmp6_type) {
		case ND_ROUTER_SOLICIT:
			handle_icmp_solicit(&msg);
			break;
		case ND_ROUTER_ADVERT:
			handle_icmp_advert(&msg, iface_index);
			break;
	}
}

static void update_lifetimes(unsigned int elapsed) {
	size_t i;
	for (i = 0; i < G.n_prefixes; i++) {
		if (G.prefixes[i].manual)
			continue;
		diff_max_zero(&G.prefixes[i].valid_time, elapsed);
		diff_max_zero(&G.prefixes[i].preferred_time, elapsed);
	}
	for (i = 0; i < G.n_routes; i++) {
		diff_max_zero(&G.routes[i].valid_time, elapsed);
		diff_max_zero(&G.routes[i].preferred_time, elapsed);
	}
}


static void send_advert(void) {
	if (!G.iface.ok)
		return;

	update_lifetimes(timespec_diff(&G.time, &G.last_advert) / 1000);

	struct nd_router_advert advert = {
		.nd_ra_hdr = {
			.icmp6_type = ND_ROUTER_ADVERT,
			.icmp6_dataun.icmp6_un_data8 = {AdvCurHopLimit, 0 /* Flags */, (AdvDefaultLifetime>>8) & 0xff, AdvDefaultLifetime & 0xff },
		},
	};

	struct icmpv6_opt lladdr = {ND_OPT_SOURCE_LINKADDR, 1, {}};
	memcpy(lladdr.data, G.iface.mac, sizeof(G.iface.mac));

	struct nd_opt_prefix_info prefixes[G.n_prefixes];

	size_t i;
	for (i = 0; i < G.n_prefixes; i++) {
		uint8_t flags = ND_OPT_PI_FLAG_AUTO;

		if (G.prefixes[i].onlink)
			flags |= ND_OPT_PI_FLAG_ONLINK;

		prefixes[i] = (struct nd_opt_prefix_info){
			.nd_opt_pi_type = ND_OPT_PREFIX_INFORMATION,
			.nd_opt_pi_len = 4,
			.nd_opt_pi_prefix_len = G.prefixes[i].len,
			.nd_opt_pi_flags_reserved = flags,
			.nd_opt_pi_valid_time = htonl(G.prefixes[i].valid_time),
			.nd_opt_pi_preferred_time = htonl(G.prefixes[i].preferred_time),
			.nd_opt_pi_prefix = G.prefixes[i].addr,
		};
	}

	struct iovec vec[3] = {
		{ .iov_base = &advert, .iov_len = sizeof(advert) },
		{ .iov_base = &lladdr, .iov_len = sizeof(lladdr) },
		{ .iov_base = prefixes, .iov_len = sizeof(prefixes) },
	};

	struct sockaddr_in6 addr = {
		.sin6_family = AF_INET6,
		.sin6_addr = {
			.s6_addr = {
				/* all-nodes address */
				0xff, 0x02, 0x00, 0x00,
				0x00, 0x00, 0x00, 0x00,
				0x00, 0x00, 0x00, 0x00,
				0x00, 0x00, 0x00, 0x01,
			}
		},
		.sin6_scope_id = G.iface.ifindex,
	};

	uint8_t cbuf[1024] __attribute__((aligned(8))) = {};

	struct msghdr msg = {
		.msg_name = &addr,
		.msg_namelen = sizeof(addr),
		.msg_iov = vec,
		.msg_iovlen = 3,
		.msg_control = cbuf,
		.msg_controllen = 0,
		.msg_flags = 0,
	};

	add_pktinfo(&msg);

	if (sendmsg(G.icmp_sock_server, &msg, 0) < 0) {
		G.iface.ok = false;
		return;
	}

	G.last_advert = G.time;

	schedule_advert(false);
}


static void usage(void) {
	fprintf(stderr, "Usage: gluon-radvd [-h] -i <interface> -m <mesh_iface> -t <routing table> -a/-p <prefix> [ -a/-p <prefix> ... ]\n");
}

static void add_prefix(const char *prefix, bool adv_onlink) {
	if (G.n_prefixes == MAX_PREFIXES)
		error(1, 0, "maximum number of prefixes is %i.", MAX_PREFIXES);

	const size_t len = strlen(prefix)+1;
	char prefix2[len];
	memcpy(prefix2, prefix, len);

	char *slash = strchr(prefix2, '/');
	if (slash) {
		*slash = 0;
		if (strcmp(slash+1, "64") != 0)
			goto error;
	}

	if (inet_pton(AF_INET6, prefix2, &G.prefixes[G.n_prefixes].addr) != 1)
		goto error;

	static const uint8_t zero[8] = {};
	if (memcmp(&G.prefixes[G.n_prefixes].addr + 8, zero, 8) != 0)
		goto error;

	G.prefixes[G.n_prefixes] = (struct prefix){
		.manual = true,
		.onlink = adv_onlink,
		.preferred_time = AdvPreferredLifetime,
		.valid_time = AdvValidLifetime,
	};

	G.n_prefixes++;
	return;

  error:
	error(1, 0, "invalid prefix %s (only prefixes of length 64 are supported).", prefix);
}

static void parse_cmdline(int argc, char *argv[]) {
	int c;
	while ((c = getopt(argc, argv, "i:a:p:h")) != -1) {
		switch(c) {
		case 'i':
			if (G.ifname_server)
				error(1, 0, "multiple server interfaces are not supported.");

			G.ifname_server = optarg;

			break;

		case 'a':
			add_prefix(optarg, false);
			break;

		case 'l':
			if (G.n_client_ifs >= MAX_INTERFACES)
				error(1, 0, "maximal number of client interfaces reached.");

			G.ifnames_client[G.n_client_ifs++] = optarg;
			break;

		case 'p':
			add_prefix(optarg, true);
			break;

		case 'h':
			usage();
			exit(0);

		case 't':
			G.rtable = atoi(optarg);
			break;

		case 'm':
			G.mesh_iface = optarg;
			break;

		default:
			usage();
			exit(1);
		}
	}
}

int main(int argc, char *argv[]) {
	size_t i;
	parse_cmdline(argc, argv);

	if (!G.ifname_server || !G.n_prefixes)
		error(1, 0, "interface and prefix arguments are required.");

	init_random();
	init_icmp_server();
	init_icmp_client();
	init_rtnl();

	update_time();
	G.next_advert = G.time;

	update_interface();

	while (true) {
		struct pollfd fds[2+G.n_client_ifs];
		fds[0] = (struct pollfd){ .fd = G.icmp_sock_server, .events = POLLIN };
		fds[1] = (struct pollfd){ .fd = G.rtnl_sock, .events = POLLIN };
		for (i = 0; i < G.n_client_ifs; i++)
			fds[i+2] = (struct pollfd){ .fd = G.icmp_socks_client[i], .events = POLLIN };

		int timeout = -1;

		if (G.iface.ok) {
			timeout = timespec_diff(&G.next_advert, &G.time);

			if (timeout < 0)
				timeout = 0;
		}

		int ret = poll(fds, 2+G.n_client_ifs, timeout);
		if (ret < 0)
			exit_errno("poll");

		update_time();

		if (fds[0].revents & POLLIN)
			handle_icmp(fds[0].fd, -1);
		if (fds[1].revents & POLLIN)
			handle_rtnl();
		for (i = 0; i < G.n_client_ifs; i++) {
			if (fds[i+2].revents & POLLIN)
				handle_icmp(fds[i+2].fd, i);
		}

		if (timespec_after(&G.time, &G.next_advert))
			send_advert();
	}
}
