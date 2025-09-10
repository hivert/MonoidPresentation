.PHONY: all clean install clean-database

all clean install: Makefile.coq
	$(MAKE) -f $< $@

%.vo: Makefile.coq %.v
	$(MAKE) -f $< $@

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

database/rocq:
	echo Building the Rocq database... This may take a long time
	cd database && ./to_rocq_proof.py -b 2000 && cd ..

database: database/rocq
	mv _CoqProject _CoqProject-no-database
	cp -f _CoqProject-with-database _CoqProject

clean-database:
	rm -rf database/rocq
	cp -f _CoqProject-no-database _CoqProject


