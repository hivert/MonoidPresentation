#!/usr/bin/env python3

"""
This script runs a Python proof checker over the database of proofs for
comparison purposes with the ROCQ implementation.
"""

import sqlite3
from ast import literal_eval

from checker_libsemigroups_pybind11 import (
    proof_evaluator as proof_checker_libsemigroups_pybind11,
)

if __name__ == "__main__":

    proof_checker = proof_checker_libsemigroups_pybind11

    con = sqlite3.connect("database.db")
    cur = con.cursor()

    all_proof_steps = []
    good_presentation_ids = set()

    print("Gathering non-recursive proof steps . . .")
    for presentation_id, proof_steps_string in cur.execute(
        "SELECT presentation_id, proof_steps FROM proof_table WHERE proof_type != 'recursive' AND proof_type != 'is_complete_adian_rws'"
    ):
        proof_steps = literal_eval(proof_steps_string)
        if proof_steps[-1][1] == "is_complete_rws" and proof_steps[-1][3] == "cpf":
            continue
        all_proof_steps.append(proof_steps)
        good_presentation_ids.add(presentation_id)

    print("Gathering recursive proof steps . . .")
    recursive_join_query = """
SELECT rec.conditional_presentation_id, rec.proof_steps
FROM proof_table rec, proof_table base
WHERE rec.conditional_presentation_id == base.presentation_id
GROUP BY rec.id
    """
    for conditional_presentation_id, proof_steps_string in cur.execute(
        recursive_join_query
    ):
        if conditional_presentation_id not in good_presentation_ids:
            continue
        all_proof_steps.append(literal_eval(proof_steps_string))

    print("Total proofs:", len(all_proof_steps))
    print("Starting validation . . .")
    for proof_steps in all_proof_steps:
        assert proof_checker(proof_steps)
    print("Done!")
