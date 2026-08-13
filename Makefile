CC ?= cc
CFLAGS ?= -O2 -march=native -Wall -Wextra -std=c11

all: efx_verify efx/efx.so

efx_verify: efx/verifier.c
	$(CC) $(CFLAGS) -DEFX_MAIN -o $@ $<

efx/efx.so: efx/verifier.c
	$(CC) $(CFLAGS) -shared -fPIC -o $@ $<

test: all
	python3 efx/crosscheck.py

clean:
	rm -f efx_verify efx/efx.so

.PHONY: all test clean
