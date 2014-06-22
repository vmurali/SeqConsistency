IGNORE:=Test

CACHESVS:=$(wildcard Caches/*.v)
CACHESVS:=$(filter-out $(IGNORE:%=%.v),$(CACHESVS))

VS:=$(wildcard *.v)
VS:=$(filter-out $(IGNORE:%=%.v),$(VS))

.PHONY: coq clean

ARGS := -R . SeqConsistency

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	echo Cchefef [$(CACHESVS)]
	coq_makefile $(ARGS) $(CACHESVS) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
