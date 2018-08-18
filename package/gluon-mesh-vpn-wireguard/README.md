# gluon-mesh-vpn-wireguard

This package will allow wireguard [1] to be used in gluon. Wireguard being a
VPN on OSI layer 3 is useful for mesh protocols that operate on layer 3.

[1] https://wireguard.io

## including servers via site.conf
This is similar to the fastd-based mesh_vpn structure.

```
          mesh_vpn = {
                  mtu = 1374,

                  wireguard = {
                          enabled = true,
                          groups = {
                                  backbone = {
                                          limit = '2', -- currently unused
                                          peers = {
                                                  gw02 = {
                                                          enabled = true,
                                                          key = 'bog2DzyiC0Os7y1GloEw0afb8bLdZ9SzVQCd44Eock4=',
                                                          remote = 'gw02.babel.ffm.freifunk.net',
                                                          broker_port = 40000,
                                                  },
                                          },
                                  },
                          },
                  },
          },

```

## serverside actions
* The wireguard private key must be deployed, and the derived Public Key has to be in site.conf
* The wg-broker-server script must be running on the server

