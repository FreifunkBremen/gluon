all: gluon-radvd

gluon-radvd: gluon-radvd.c batadv_query.c debugfs.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -Wall -o $@ $^ $(LDLIBS) -lrt
