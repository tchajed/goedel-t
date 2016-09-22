default: Makefile.coq
	$(MAKE) -f Makefile.coq SystemT.vo Examples.vo

all: Makefile.coq
	$(MAKE) -f Makefile.coq all

extract: Makefile.coq
	$(MAKE) -f Makefile.coq Extraction.vo

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq eval.hs

.PHONY: all default extract clean
