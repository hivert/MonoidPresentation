Certifying the decidability of the word problem in monoids at large
===================================================================

R. Cirpons, F. Hivert, A. Mahboubi, G. Melquiond, J. Mitchell, F. Smith

Work presented at CPP-2026, Sun 11 - Sat 17 January 2026, Rennes, France.

https://doi.org/10.1145/3779031.3779101


While the word problem for monoids is undecidable in general, having a
decision procedure for some finitely presented monoid of interest has numerous
applications. The repository contains a toolbox for the Rocq proof assistant that
can be used to verify the decidability of the word problem for a given monoid
and, in some cases, to produce the corresponding decision procedure. As this
verification can be computationally intensive, the toolbox heavily relies on
proofs by reflection guided by an external oracle. This approach has been
successfully used on several large presentations from the literature, as well
as on a database of one million $1$-relation monoids. The huge size of this
database forced some unusual considerations onto the Rocq formalization, so
that the formal proofs could be checked in a reasonable amount of time.

Contents
========

This repository contains two components:

- `theory` : a rocq infrastructure to deal with word problem
- `database` : a database of proof of the decidabilitiy of the word problem for
             1-relation monoids

# Requirements:

- Coq version `9.0.0` with `coq-native` enabled (this can be done on `opam` by
  installing the pseudo package `coq-native`)
- Mathematical components library version `2.5.0`
  (`opam` packages `rocq-mathcomp-boot` and `rocq-mathcomp-algebra`)
- Hierarchy builder library version `1.10.1`
  (`opam` package `rocq-hierarchy-builder`)
- Python at least version `3.9`

# Building:

This is done in two steps:
- `make database` extract the database to Rocq (takes about 15min)
- `make` rocq check the database (takes about 6h on one core)

If the database is not extracted then
- `make` only compile the infrastructure (takes about 2min)

When the database is extracted
- `make clean-database` revert back to the infrastructure only repository

One can compile with several core by `make -j12` but
WARNING: compiling the database can be very memory consuming. Some files take
7GB of memory to compile. You shouldn't try wo check the database with more
than 'j4' if you have only 16GB.

# Checking the database with Python / C++

See also `database/README.md`. There are two possibilities

- either run `check_proofs.py` in the `database` directory : this will launch a
  Python only checker. No additional dependencies are needed to run this checker.
- or run `check_proofs.py -l` in the `database` directory : this will launch a
  faster Python / C++ checker based on `libsemigroups`. To be able to run this
  second checker you need to install the Python package `libsemigroups_pybind11`.
