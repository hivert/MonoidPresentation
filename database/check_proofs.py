#!/usr/bin/env python3

"""
(c) Copyright 2025 Reinis Cirpons and Finn Smith.
Distributed under the terms of CeCILL-B.

This script runs a Python proof checker over the database of proofs for
comparison purposes with the ROCQ implementation.
"""

import sqlite3
from ast import literal_eval
from argparse import ArgumentParser

_HAS_LIBSEMIGROUPS_PYBIND11 = True
try:
    from checker_libsemigroups_pybind11 import (
        proof_evaluator as proof_checker_libsemigroups_pybind11,
    )

    def main_libsemigroups_pybind11():
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

except ImportError:
    _HAS_LIBSEMIGROUPS_PYBIND11 = False

from checker_independent import (
    normalize,
    proof_evaluator as proof_checker_independent,
    _step_name,
    _step_parameters,
    _step_presentation,
    VERIFIED_DECIDABLE_PRESENTATIONS,
)


def _should_ignore(proof, conditional_id, ignored_and_consequences):
    return (
        _step_name(proof[-1]) == "is_complete_adian_rws"
        or (
            _step_name(proof[-1]) == "is_complete_rws"
            and _step_parameters(proof[-1])[1]
        )
        == "cpf"
        or _step_name(proof[-1]) == "recursive"
        and conditional_id in ignored_and_consequences
    )


def main_independent():
    recursive_proofs = set()
    incorrect_proofs = set()
    ignored_and_consequences = set()
    connection = sqlite3.connect("database.db")
    cursor = connection.cursor()

    ignored_count = 0
    count = 0

    print("Checking non-recursive proofs")
    print("=============================")

    query = "SELECT id, proof_steps, presentation_id, conditional_presentation_id FROM proof_table"
    for id, proof, presentation_id, conditional_id in cursor.execute(query):
        proof = literal_eval(proof)
        if _should_ignore(proof, conditional_id, ignored_and_consequences):
            ignored_and_consequences.add(presentation_id)
            ignored_count += 1
            continue
        if _step_name(proof[-1]) == "recursive":
            recursive_proofs.add(
                (
                    id,
                    tuple(proof),
                    presentation_id,
                    conditional_id,
                    normalize(_step_presentation(proof[-1])),
                )
            )
            continue
        count += 1
        if count % 10000 == 0:
            print(f"On proof {count}")
        if proof_checker_independent(proof):
            VERIFIED_DECIDABLE_PRESENTATIONS.add(
                normalize(_step_presentation(proof[0]))
            )
        else:
            incorrect_proofs.add(tuple(proof))
            print(f"proof verification failed for proof {id}")

    print("Checking recursive proofs")
    print("=========================")
    # for simplicity, we can get away with just repeatedly checking all the recursives
    changed = True
    depth = 0
    while changed:
        new_resolved_proofs = set()
        changed = False
        depth += 1
        print(f"Recursive Depth {depth}")
        print("-------------------------")
        for id, proof, presentation_id, conditional_id, normal in recursive_proofs:
            if normal in VERIFIED_DECIDABLE_PRESENTATIONS:
                count += 1
                if count % 10000 == 0:
                    print(f"On proof {count}")
                new_resolved_proofs.add(
                    (id, proof, presentation_id, conditional_id, normal)
                )
                if proof_checker_independent(proof):
                    VERIFIED_DECIDABLE_PRESENTATIONS.add(
                        normalize(_step_presentation(proof[0]))
                    )
                else:
                    incorrect_proofs.add(tuple(proof))
                    print(f"proof verification failed for proof {id}")
            elif conditional_id in ignored_and_consequences:
                new_resolved_proofs.add(
                    (id, proof, presentation_id, conditional_id, normal)
                )
                ignored_and_consequences.add(presentation_id)
                ignored_count += 1
                continue
        changed = len(new_resolved_proofs) > 1
        recursive_proofs -= new_resolved_proofs

    print("Finished with:")
    print(f"{count - len(incorrect_proofs)} correct proofs;")
    print(f"{len(incorrect_proofs)} incorrect proofs;")
    print(f"{len(recursive_proofs)} unresolved recursions; and")
    print(f"{ignored_count} proofs ignored in the database.")


if __name__ == "__main__":
    parser = ArgumentParser(
        prog="check_proofs.py",
        description="Check the SA certificate database for well-formedness",
    )
    parser.add_argument(
        "-l",
        "--libsemigroups-pybind11",
        help="If present, runs the libsemigroups_pybind11 based checker (default: False). "
        "libsemigroups_pybind11 must be installed for this option to work.",
        action="store_true",
    )
    arguments = parser.parse_args()
    if arguments.libsemigroups_pybind11 and _HAS_LIBSEMIGROUPS_PYBIND11:
        main_libsemigroups_pybind11()
    else:
        if arguments.libsemigroups_pybind11:
            print(
                "libsemigroups_pybind11 not installed, using independent checker instead."
            )
        main_independent()
