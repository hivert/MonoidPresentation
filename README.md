Certifying the word problem in monoids
======================================

This repository contains two components:

- `theory` : a rocq infrastructure to deal with word problem
- `database` : a database of proof of the decidabilitiy of the word problem for
             1-relation monoids

# Requirements:

- Coq version `9.0.0` with `coq-native` enabled (this can be done on `opam` by
  installing the pseudo package `coq-native`)
- Mathematical Component version `2.5.0`
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
