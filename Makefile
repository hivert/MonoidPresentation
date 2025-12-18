.PHONY: all clean install clean-database

all clean install: Makefile.coq
	$(MAKE) -f $< $@

%.vo: Makefile.coq %.v
	$(MAKE) -f $< $@

Makefile.coq: _CoqProject
	if ! command -v "$(COQBIN)rocq" >/dev/null 2>&1; \
	then \
		$(COQBIN)coq_makefile -f $< -o $@; \
	else \
		$(COQBIN)rocq makefile -f $< -o $@; \
	fi

database/rocq:
	echo Building the Rocq database... This may take a long time
	cd database && ./to_rocq_proof.py -b 2000 && cd ..

database: database/rocq
	rm -f _CoqProject
	cp -f _CoqProject-with-database _CoqProject

clean-database:
	rm -rf database/rocq
	rm -f _CoqProject
	cp -f _CoqProject-no-database _CoqProject
