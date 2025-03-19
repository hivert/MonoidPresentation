.PHONY: all clean install

all clean install: Makefile.coq
	$(MAKE) -f $< $@

%.vo: Makefile.coq %.v
	$(MAKE) -f $< $@

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@
