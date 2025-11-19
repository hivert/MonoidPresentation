# Standalone 1-relation monoid proof tools

This directory contains data and helper scripts pertaining to the Certified
Programs and Proofs (CPP) 2026 conference submission "Certifying the
decidability of the word problem in monoids at large".

## Data

The file `database.db` contains the 1-relation monoid word problem proof
database. The database consists of proofs in the SA certificate. This database
is used to generate ROCQ proofs certifying the decidability of the word problem
using the accompanying tools as described below.

The subdirectory `rocq_proofs/` contains ROCQ proofs certifying the decidability
of the word problem for a subset of the proofs found in `database.db` that are
currently implemented in ROCQ. The proofs in this subdirectory were produced
by using the `to_rocq_proof.py` script from `database.db`.

## Tools

There are two tools included in this directory. The `to_rocq_proof.py` script
is a tool for converting the SA oracle produced proof format to a ROCQ
proof. The `check_proofs.py` script is a tool for running python "proof
checkers" on the SA certificate format directly. Passing the `-l` option to the
script toggles the use of the `libsemigroups_pybind11` library.

Note that the `to_rocq_proof.py` script requires an output directory (defaults
to `rocq/`) to be completely empty before being run.

In order to run the `check_proofs.py` script, installing the python packaged from
`requirements.txt` may be necessary (e.g. by running
`python3 -m pip install -r requirements.txt`). The `check_proofs.py` script is
mainly intended as a timing benchmark.
