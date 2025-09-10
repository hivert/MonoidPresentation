#!/usr/bin/env python3

import sqlite3
import argparse
from pathlib import Path
from collections import Counter
from typing import NamedTuple, Iterable
from ast import literal_eval
from proof_parser import (
    ElementaryRewrite,
    Presentation,
    ProofStep,
    ProofStepEqualNumberOfOccurrencesOf,
    ProofStepIsC3Monoid,
    ProofStepIsC4Monoid,
    ProofStepIsWatier1,
    ProofStepReverse,
    ProofStepRecursive,
    ProofStepTietzeAddGenerator,
    ProofStepTietzeAddRelation,
    ProofStepTietzeRmRelation,
    ProofStepIsCompleteRws,
    ProofStepStronglyCompress,
    ProofStepReduceTo2Generators,
    ProofStepFlipAllRelations,
    ProofStepAlphabetIsomorphism,
    ProofStepReorderAlphabet,
    parse_proof_tuple,
)


## Formatting output


class Indent(NamedTuple):
    level: int | None = None


class Dedent(NamedTuple):
    level: int | None = None


Layout = list[Indent | Dedent | str]


def layout_to_str(layout: Layout | str, default_indent: int = 2) -> str:
    if isinstance(layout, str):
        return layout
    indent_level = 0
    result = []
    for command_or_str in layout:
        if isinstance(command_or_str, Indent):
            if command_or_str.level is None:
                indent_level += default_indent
            else:
                assert command_or_str.level > 0
                indent_level += command_or_str.level
        elif isinstance(command_or_str, Dedent):
            if command_or_str.level is None:
                indent_level -= default_indent
            else:
                assert command_or_str.level > 0
                indent_level -= command_or_str.level
            assert indent_level >= 0
        else:
            assert isinstance(command_or_str, str)
            # Need to handle newlines here to work with breaking arbitrary nested
            # expressions
            lines = command_or_str.split("\n")
            for line in lines[:-1]:
                result.append(line + "\n" + " " * indent_level)
            result.append(lines[-1])
    assert indent_level == 0
    return "".join(result)


## Generating rocq code


def to_rocq_list(seq: Iterable[Layout | str], sep: str = ";") -> Layout:
    pref = "[:: "
    suff = "]"
    result: Layout = [pref, Indent(len(pref))]
    first = True
    for x in seq:
        if first:
            first = False
        else:
            result.append(sep)

        if isinstance(x, list):
            result.extend(x)
        else:
            assert isinstance(x, str)
            result.append(x)
    result.extend([Dedent(len(pref)), suff])
    return result


def to_rocq_char(c: str) -> str:
    assert len(c) == 1
    return str(ord(c) - ord("a"))


def to_rocq_word(s: str) -> Layout:
    return to_rocq_list(map(to_rocq_char, s), sep=";")


def to_rocq_bool(b: bool) -> str:
    return "true" if b else "false"


def to_rocq_elementary_rewrite(
    e: ElementaryRewrite, relations: tuple[tuple[str, str], ...]
) -> str:
    assert e.lhs.prefix == e.rhs.prefix and e.lhs.suffix == e.rhs.suffix
    start_position = len(e.lhs.prefix)
    relation = (e.lhs.match, e.rhs.match)
    if relation in relations:
        relation_number = relations.index(relation)
        direction = True
    elif relation[::-1] in relations:
        relation_number = relations.index(relation[::-1])
        direction = False
    else:
        assert False, (
            f"Neither relation nor reversal in relations, "
            f"relation={relation}, relations={relations}"
        )
    return f"RTriple {relation_number} {start_position} {to_rocq_bool(direction)}"


def to_rocq_elementary_sequence(
    lhs: str,
    rhs: str,
    s: tuple[ElementaryRewrite, ...],
    relations: tuple[tuple[str, str], ...],
) -> Layout:
    if lhs == rhs:
        return to_rocq_list(())
    return to_rocq_list(
        [
            to_rocq_elementary_rewrite(elementary_rewrite, relations)
            for elementary_rewrite in s
        ],
        sep=";\n",
    )


def to_rocq_presentation(presentation: Presentation) -> Layout:
    result: Layout = [f"make_pres "]
    result.extend(to_rocq_word(presentation.gens))
    result.extend([Indent(), "\n"])
    relation_layouts = []
    for lhs, rhs in presentation.relations:
        relation_layouts.append([])
        relation_layouts[-1].append("(")
        relation_layouts[-1].extend(to_rocq_word(lhs))
        relation_layouts[-1].append(", ")
        relation_layouts[-1].extend(to_rocq_word(rhs))
        relation_layouts[-1].append(")")
    result.extend(to_rocq_list(relation_layouts, sep=";\n"))
    result.append(Dedent())
    return result


def to_rocq_cert_name(presentation: Presentation) -> str:
    return "_".join(
        (presentation.gens,)
        + tuple(
            rel_word for relation in presentation.relations for rel_word in relation
        )
    ).upper()


def to_rocq_tietze_add_generator(proof_step: ProofStepTietzeAddGenerator) -> Layout:
    result: Layout = [f"add_gen {to_rocq_char(proof_step.args.letter)} "]
    result.extend(to_rocq_word(proof_step.args.word))
    return result


def to_rocq_tietze_add_relation(proof_step: ProofStepTietzeAddRelation) -> Layout:
    result: Layout = [f"add_rel "]
    result.extend(to_rocq_word(proof_step.args.lhs))
    result.append(" ")
    result.extend(to_rocq_word(proof_step.args.rhs))
    result.extend([Indent(), "\n"])
    result.extend(
        to_rocq_elementary_sequence(
            proof_step.args.lhs,
            proof_step.args.rhs,
            proof_step.args.elementary_sequence,
            proof_step.current_presentation.relations,
        )
    )
    result.append(Dedent())
    return result


def to_rocq_tietze_rm_relation(proof_step: ProofStepTietzeRmRelation) -> Layout:
    idx = proof_step.current_presentation.relations.index(
        (proof_step.args.lhs, proof_step.args.rhs)
    )
    result: Layout = [
        f"rm_rel {idx}\n",
    ]
    result.extend(
        to_rocq_elementary_sequence(
            proof_step.args.lhs,
            proof_step.args.rhs,
            proof_step.args.elementary_sequence,
            proof_step.current_presentation.relations[:idx]
            + proof_step.current_presentation.relations[idx + 1 :],
        )
    )
    return result


def to_rocq_is_complete_rws_lenlex(proof_step: ProofStepIsCompleteRws) -> Layout:
    assert proof_step.args.termination_method == "lenlex"
    return to_rocq_word(proof_step.args.termination_certificate)


def to_rocq_equal_number_of_occurences_of(
    proof_step: ProofStepEqualNumberOfOccurrencesOf,
) -> Layout:
    return [to_rocq_char(proof_step.args.letter)]


def to_rocq_is_watier1(
    proof_step: ProofStepIsWatier1,
) -> Layout:
    assert len(proof_step.current_presentation.relations) == 1
    u, v = proof_step.current_presentation.relations[0]
    assert len(u) >= 2 and len(v) >= 2
    if u[0] == u[-1]:
        u, v = v, u
    assert u[0] != u[-1] and u[-1] == v[0] and v[0] == v[-1]
    b = u[0]
    a = u[-1]
    k = len(u.split("a")[0])
    result: Layout = [to_rocq_char(a), " ", to_rocq_char(b), " "]
    result.extend(to_rocq_word(u[k + 1 :]))
    result.append(" ")
    result.extend(to_rocq_word(v[1:]))
    result.extend([" ", str(k)])
    return result


def to_rocq_small_overlap(
    proof_step: ProofStepIsC3Monoid | ProofStepIsC4Monoid,
) -> Layout:
    assert len(proof_step.args.factorizations) == 2 * len(
        proof_step.current_presentation.relations
    )
    for i, (u, v) in enumerate(proof_step.current_presentation.relations):
        assert "".join(proof_step.args.factorizations[2 * i]) == u
        assert "".join(proof_step.args.factorizations[2 * i + 1]) == v
    return to_rocq_list(
        (
            to_rocq_list((to_rocq_word(word) for word in factorization), sep="; ")
            for factorization in proof_step.args.factorizations
        ),
        sep=";\n",
    )


def to_rocq_strongly_compress_and_reduce(
    proof_step_compress: ProofStepStronglyCompress,
    proof_step_reduce: ProofStepReduceTo2Generators,
) -> Layout:
    strong_morph = proof_step_compress.args.morphism
    assert strong_morph.compression_length > 1
    presentation = proof_step_reduce.current_presentation
    reduce_morph = proof_step_reduce.args.morphism
    letter_words = {"a": [], "b": []}
    for word, letter in strong_morph:
        final_letter = reduce_morph.apply(letter, presentation)
        assert final_letter in {"a", "b"}, (
            proof_step_compress,
            proof_step_reduce,
            letter,
            final_letter,
        )
        letter_words[final_letter].append(word)
    assert len(letter_words["a"]) == 1 or len(letter_words["b"]) == 1, (
        proof_step_compress,
        proof_step_reduce,
    )
    singular_letter = "a"
    if len(letter_words["a"]) != 1:
        singular_letter = "b"
    result: Layout = []
    assert proof_step_compress.current_presentation.relations[0][0].startswith(
        letter_words[singular_letter][0]
    ), (proof_step_compress, proof_step_reduce)
    result.extend(to_rocq_word(letter_words[singular_letter][0]))
    result.append(" ")
    result.append(to_rocq_char(singular_letter))
    return result


def to_rocq_alphabet_isomorphism(
    proof_step: ProofStepAlphabetIsomorphism,
) -> Layout:
    return to_rocq_word(proof_step.args.morphism)


def to_rocq_reccert(
    recursive_step: ProofStepRecursive,
    proof_position: dict[tuple[str, ...], tuple[str, int]],
) -> tuple[Layout, str]:
    p = recursive_step.current_presentation.flatten()
    assert p in proof_position, recursive_step
    filename, number = proof_position[p]
    reccert: Layout = [
        "(",
        "RecCert",
        " ",
        f"{filename}.all_pres_dec",
        " ",
        str(number),
        ")",
    ]
    return reccert, filename


_to_rocq_proof_steps = {
    "tietze_add_generator": to_rocq_tietze_add_generator,
    "tietze_add_relation": to_rocq_tietze_add_relation,
    "tietze_rm_relation": to_rocq_tietze_rm_relation,
    "is_complete_rws": to_rocq_is_complete_rws_lenlex,
    "is_monogenic": lambda _: [],
    "equal_number_of_occurrences_of": to_rocq_equal_number_of_occurences_of,
    "is_watier1": to_rocq_is_watier1,
    "is_c3_monoid": to_rocq_small_overlap,
    "is_c4_monoid": to_rocq_small_overlap,
    "reverse": lambda _: [],
    "recursive": lambda _: [],
    "is_special": lambda _: [],
    "reorder_alphabet": lambda _: [],
    "alphabet_isomorphism": lambda _: [],
    "flip_all_relations": lambda _: [],
    "is_cycle_free": lambda _: [],
    "strongly_compress": lambda _: None,
    "reduce_to_2_generators": lambda _: None,
}


def to_rocq_presentation_certificate_type(proof: tuple[ProofStep, ...]) -> str | None:
    step_to_cert_type = {
        # "is_complete_rws": "CompleteRewritingSystem" # This is a special case and we handle in if below
        # "is_monogenic": "Monogenic", # Need to check how many gens, handled in if below
        "is_watier1": "Watier",
        "is_c3_monoid": "SmallOverlap",
        "is_c4_monoid": "SmallOverlap",
        "equal_number_of_occurrences_of": "EqualNumberOfOccurences",
        "reverse": "Reverse",
        "is_special": "Special",
        "reorder_alphabet": "AlphabetReorder",
        "is_cycle_free": "CycleFree",
        "flip_all_relations": "FlipAllRelations",
        "alphabet_isomorphism": "AlphabetIsom",
    }
    rocq_certificate_type = None
    for i, proof_step in enumerate(proof):
        if (
            proof_step.step == "is_complete_rws"
            and proof_step.args.termination_method == "lenlex"
        ):
            rocq_certificate_type = "CompleteRewritingSystem"
        elif proof_step.step == "is_monogenic":
            if len(proof_step.current_presentation.gens) == 1:
                rocq_certificate_type = "Monogenic"
            else:
                rocq_certificate_type = "FreeProductMonogenicAndFree"
        elif proof_step.step == "strongly_compress":
            assert i < len(proof) - 1
            if proof[i + 1].step == "is_special":
                return "StronglyCompressToSpecial"
            elif proof[i + 1].step == "reduce_to_2_generators":
                return "StronglyCompressAndReduce"
            else:
                raise RuntimeError(
                    f"strongly_compress found with unexpected following step {proof[i+1].step}!"
                )
        elif proof_step.step in step_to_cert_type:
            rocq_certificate_type = step_to_cert_type[proof_step.step]
        if rocq_certificate_type is not None:
            break
    return rocq_certificate_type


def to_rocq_presentation_certificate(
    proof: tuple[ProofStep, ...],
    proof_position: dict[tuple[str, ...], tuple[str, int]],
) -> tuple[Layout, str | None]:
    result: Layout = []
    rocq_certificate_type = to_rocq_presentation_certificate_type(proof)
    assert rocq_certificate_type is not None

    result.append(rocq_certificate_type)

    no_param = {
        "Monogenic",
        "FreeProductMonogenicAndFree",
        "Special",
        "StronglyCompressToSpecial",
        "CycleFree",
    }
    filename: str | None = None
    if rocq_certificate_type == "CompleteRewritingSystem":
        result.extend([Indent(), "\n"])
        tietze_step_layouts = []
        for proof_step in proof[:-1]:
            assert proof_step.step in {
                "tietze_add_generator",
                "tietze_rm_relation",
                "tietze_add_relation",
            }
            to_rocq_proof_step = _to_rocq_proof_steps[proof_step.step]
            tietze_step_layouts.append(to_rocq_proof_step(proof_step))
        result.extend(to_rocq_list(tietze_step_layouts, sep=";\n"))
        assert proof[-1].step == "is_complete_rws"
        assert isinstance(proof[-1], ProofStepIsCompleteRws)
        result.append("\n")
        result.extend(to_rocq_is_complete_rws_lenlex(proof[-1]))
        result.append(Dedent())
    elif rocq_certificate_type == "Watier":
        assert len(proof) == 1
        assert isinstance(proof[0], ProofStepIsWatier1)
        result.extend([Indent(), "\n"])
        result.extend(to_rocq_is_watier1(proof[0]))
        result.append(Dedent())
    elif rocq_certificate_type == "SmallOverlap":
        assert len(proof) == 1
        assert isinstance(proof[0], ProofStepIsC4Monoid) or isinstance(
            proof[0], ProofStepIsC3Monoid
        )
        result.extend([Indent(), "\n"])
        result.extend(to_rocq_small_overlap(proof[0]))
        result.append(Dedent())
    elif rocq_certificate_type == "EqualNumberOfOccurences":
        assert len(proof) == 1
        assert isinstance(proof[0], ProofStepEqualNumberOfOccurrencesOf)
        result.append(" ")
        result.extend(to_rocq_equal_number_of_occurences_of(proof[0]))
    elif rocq_certificate_type == "Reverse":
        assert len(proof) == 2
        assert isinstance(proof[0], ProofStepReverse)
        assert isinstance(proof[1], ProofStepRecursive)
        layout, filename = to_rocq_reccert(proof[1], proof_position)
        result.append(" ")
        result.extend(layout)
    elif rocq_certificate_type == "AlphabetIsom":
        assert len(proof) == 2
        assert isinstance(proof[0], ProofStepAlphabetIsomorphism)
        assert isinstance(proof[1], ProofStepRecursive)
        layout, filename = to_rocq_reccert(proof[1], proof_position)
        result.append(" ")
        result.extend(layout)
        result.append(" ")
        result.extend(to_rocq_alphabet_isomorphism(proof[0]))
    elif rocq_certificate_type == "FlipAllRelations":
        assert len(proof) == 2
        assert isinstance(proof[0], ProofStepFlipAllRelations)
        assert isinstance(proof[1], ProofStepRecursive)
        layout, filename = to_rocq_reccert(proof[1], proof_position)
        result.append(" ")
        result.extend(layout)
    elif rocq_certificate_type == "AlphabetReorder":
        assert len(proof) == 2, proof
        assert isinstance(proof[0], ProofStepReorderAlphabet)
        assert isinstance(proof[1], ProofStepRecursive)
        layout, filename = to_rocq_reccert(proof[1], proof_position)
        result.append(" ")
        result.extend(layout)
    elif rocq_certificate_type == "StronglyCompressAndReduce":
        assert len(proof) == 3
        assert isinstance(proof[0], ProofStepStronglyCompress)
        assert isinstance(proof[1], ProofStepReduceTo2Generators)
        assert isinstance(proof[2], ProofStepRecursive)
        layout, filename = to_rocq_reccert(proof[2], proof_position)
        result.append(" ")
        result.extend(layout)
        result.append(" ")
        result.extend(to_rocq_strongly_compress_and_reduce(proof[0], proof[1]))
    elif rocq_certificate_type in no_param:
        pass
    else:
        raise NotImplementedError(f"Can't handle {rocq_certificate_type} yet!")

    return result, filename


def to_rocq_presentation_file(
    batch: list[tuple[Presentation, tuple[ProofStep, ...]]]
) -> Layout:
    result: Layout = ['Require Import database_pres.\n\n']

    layouts = [
        to_rocq_presentation(initial_presentation) for initial_presentation, _ in batch
    ]
    prefix = "Definition all_pres := "
    result.extend([prefix, Indent(len(prefix))])
    result.extend(to_rocq_list(layouts, sep=";\n"))
    result.extend([".", Dedent(len(prefix)), "\n", "\n"])

    result.extend(
        [
            "Lemma size_int_all_pres : size_int all_pres = ",
            str(len(layouts)),
            ".",
            "\n",
            "Proof. by []. Qed.",
        ]
    )
    return result


def to_rocq_decideable_file(
    batch: list[tuple[Presentation, tuple[ProofStep, ...]]],
    presentation_filename: str,
    proof_position: dict[tuple[str, ...], tuple[str, int]],
) -> Layout:
    result: Layout = [
        'Require Import database_dec.\n',
        f"Require {presentation_filename}.\n\n",
    ]

    filenames: list[str] = []
    layouts: list[Layout] = []
    for _, proof in batch:
        layout, filename = to_rocq_presentation_certificate(proof, proof_position)
        if filename is not None:
            filenames.append(filename)
        layouts.append(layout)

    result.extend(f"Require {filename}.\n" for filename in sorted(set(filenames)))
    result.append("\n")

    result.extend(
        [
            "Lemma all_pres_dec (P : pres int) : P \\in ",
            f"{presentation_filename}.all_pres ",
            "-> WPdecidable P.\n",
            "Proof.\n",
            f"apply: (check_batchP (lc :=",
            Indent(),
            "\n",
        ]
    )

    result.extend(
        to_rocq_list(
            layouts,
            sep=";\n",
        )
    )
    result.extend(
        [
            ")).\n",
            "by (abstract native_cast_no_check (erefl BatchOk)) || (native_compute ; reflexivity).",
            Dedent(),
            "\n",
            "Qed.",
        ]
    )

    return result


## Batch file creation


def pop_batch_and_write_to_file(
    certificate_type: str,
    current_batches: dict[str, list[tuple[Presentation, tuple[ProofStep]]]],
    current_batches_number: Counter[str],
    batch_size: int | None,
    proof_position: dict[tuple[str, ...], tuple[str, int]],
    output_directory: Path,
):
    batch = current_batches[certificate_type]
    num = current_batches_number[certificate_type]
    filename = f"{certificate_type}_batch{num:03d}"

    if batch_size is not None:
        preamble = (
            f"(* Autogenerated certs for {certificate_type} "
            f"proofs {num*batch_size}-{(num+1)*batch_size-1} *)\n\n"
        )

    else:
        preamble = f"(* Autogenerated certs for all {certificate_type} proofs *)\n\n"

    print(f"Popping batch {num} of {certificate_type}!")
    with open(
        output_directory / certificate_type / "pres" / (filename + "_pres.v"),
        "w",
    ) as in_file:
        in_file.write(preamble)
        in_file.write(layout_to_str(to_rocq_presentation_file(batch)))
        in_file.write("\n")

    with open(
        output_directory / certificate_type / "dec" / (filename + "_dec.v"),
        "w",
    ) as in_file:
        in_file.write(preamble)
        in_file.write(
            layout_to_str(
                to_rocq_decideable_file(batch, filename + "_pres", proof_position)
            )
        )
        in_file.write("\n")

    # Update global proof store
    for i, (pres, _) in enumerate(batch):
        p = pres.flatten()
        if p not in proof_position:
            proof_position[p] = (filename + "_dec", i)

    batch.clear()
    current_batches_number[certificate_type] += 1


def do_correct_reverse_pres(presentation: tuple[str, ...]) -> tuple[str, ...]:
    return (presentation[0],) + tuple(word[::-1] for word in presentation[1:])


def do_flip_all_relations(presentation: tuple[str, ...]) -> tuple[str, ...]:
    result = [presentation[0]]
    for j in range(1, len(presentation), 2):
        result.append(presentation[j + 1])
        result.append(presentation[j])
    return tuple(result)


def do_alphabet_swap(presentation: tuple[str, ...]) -> tuple[str, ...]:
    assert presentation[0] in {"ba", "ab"}
    result = [presentation[0]]
    f = {"b": "a", "a": "b"}
    result.extend("".join(f[x] for x in word) for word in presentation[1:])
    return tuple(result)


def do_reorder_alphabet(presentation: tuple[str, ...]) -> tuple[str, ...]:
    return (presentation[0][::-1],) + presentation[1:]


def compute_all_simple_denormalizations(
    presentation: tuple[str, ...]
) -> dict[tuple[str, ...], tuple]:
    """Compute all possible proofs simply denormalizing a given presentation.

    A simple denormalization consists of any sequence of the following steps:

        reorder_alphabet
        reverse
        flip_all_relations
        alphabet_isomorphism

    Returns a dictionary
    """
    derivation = {}
    derivation[presentation] = ()
    opers = [
        do_reorder_alphabet,
        do_correct_reverse_pres,
        do_flip_all_relations,
        do_alphabet_swap,
    ]
    names = [
        "reorder_alphabet",
        "reverse",
        "flip_all_relations",
        "alphabet_isomorphism",
    ]
    changed = True
    while changed:
        changed = False
        old_presses = list(derivation.keys())
        for pres in old_presses:
            old_derivation = derivation[pres]
            for oper, name in zip(opers, names):
                if name == "alphabet_isomorphism" and pres[0] not in {"ab", "ba"}:
                    continue
                new_pres = oper(pres)
                if new_pres not in derivation:
                    new_step = (0, name, pres)
                    if name == "alphabet_isomorphism":
                        new_step += (pres[0][::-1],)
                    derivation[new_pres] = old_derivation + (
                        (new_step, (1, "recursive", new_pres)),
                    )
                    changed = True

    return derivation


def normalize_proof_single_step(proof: tuple[tuple, ...]) -> tuple[tuple, ...]:
    """Normalize proof to speed up ROCQ certs."""
    result: list[tuple] = []
    step_nr = 0
    idx = 0
    c = 0
    while idx < len(proof):
        c += 1
        if c == 1000:
            print()
        if c > 1000:
            print(proof)
        proof_step = proof[idx]
        assert len(proof_step) >= 3
        if proof_step[1] == "reverse" and idx < len(proof) - 1:
            # has to be handled differently if we do a reverse + flip
            next_proof_step = proof[idx + 1]
            correct_pres = (proof_step[2][0],) + tuple(
                word[::-1] for word in proof_step[2][1:]
            )
            if correct_pres != next_proof_step[2]:
                # need to add a flip all clause
                flipped_pres = [correct_pres[0]]
                for j in range(1, len(correct_pres), 2):
                    flipped_pres.append(correct_pres[j + 1])
                    flipped_pres.append(correct_pres[j])
                assert tuple(flipped_pres) == next_proof_step[2], (
                    proof,
                    flipped_pres,
                    next_proof_step[2],
                )
                result.append((step_nr, "reverse", proof_step[2]))
                step_nr += 1
                result.append((step_nr, "flip_all_relations", correct_pres))
                step_nr += 1
                idx += 1
                continue
            # must be a correct reverse, check if can cancel stuff
            if next_proof_step[1] == "reverse":
                # Either next one is last or next reverse is correct and we can cancel
                assert (
                    idx + 2 >= len(proof) or proof[idx + 2][2] == proof_step[2]
                ), proof
                # skip this and next step
                idx += 2
                continue
        elif proof_step[1] == "flip_all_relations" and idx < len(proof) - 1:
            next_proof_step = proof[idx + 1]
            if next_proof_step[1] == "flip_all_relations":
                assert (
                    idx + 2 >= len(proof) or proof[idx + 2][2] == proof_step[2]
                ), proof
                idx += 2
                continue
            elif next_proof_step[1] == "reverse":
                # reverses always precede flips
                # assume if we have a flip_all_relations that all reverses are
                # correct already
                result.append((step_nr, "reverse", proof_step[2]))
                step_nr += 1
                result.append(
                    (
                        step_nr,
                        "flip_all_relations",
                        do_correct_reverse_pres(proof_step[2]),
                    )
                )
                step_nr += 1
                idx += 2
                continue
        elif proof_step[1] == "reorder_alphabet" and idx < len(proof) - 1:
            # Reorder alphabet flips a's and b's in alphabet
            assert proof_step[2][0] in {"ab", "ba"}
            next_proof_step = proof[idx + 1]
            if next_proof_step[1] == "reorder_alphabet":
                assert (
                    idx + 2 >= len(proof) or proof[idx + 2][2] == proof_step[2]
                ), proof
                idx += 2
                continue
            elif next_proof_step[1] == "reverse":
                # reverses always precede reorder_alphabet
                # assume if we have a reorder_alphabet that all reverses are
                # correct already
                result.append((step_nr, "reverse", proof_step[2]))
                step_nr += 1
                result.append(
                    (
                        step_nr,
                        "reorder_alphabet",
                        do_correct_reverse_pres(proof_step[2]),
                    )
                )
                step_nr += 1
                idx += 2
                continue
            elif next_proof_step[1] == "flip_all_relations":
                # flip_all_relations always precede reorder_alphabet
                result.append((step_nr, "flip_all_relations", proof_step[2]))
                step_nr += 1
                result.append(
                    (
                        step_nr,
                        "reorder_alphabet",
                        do_flip_all_relations(proof_step[2]),
                    )
                )
                step_nr += 1
                idx += 2
                continue
        elif proof_step[1] == "strongly_compress" and idx < len(proof) - 1:
            next_proof_step = proof[idx + 1]
            if next_proof_step[1] == "reverse":
                assert idx + 2 <= len(proof) - 1
                assert proof[idx + 2][1] == "reduce_to_2_generators"
                reversed_next_pres = (next_proof_step[2][0],) + tuple(
                    word[::-1] for word in next_proof_step[2][1:]
                )
                # At this point no flip is needed
                assert reversed_next_pres == proof[idx + 2][2]

                reversed_pres = do_correct_reverse_pres(proof_step[2])
                assert len(proof_step) >= 4
                reversed_morphism = tuple(
                    (word[::-1], letter) for word, letter in proof_step[3]
                )
                result.append((step_nr, "reverse", proof_step[2]))
                step_nr += 1
                result.append(
                    (step_nr, "strongly_compress", reversed_pres, reversed_morphism)
                )
                step_nr += 1
                # Skip the reverse too
                idx += 2
                continue
            elif next_proof_step[1] in {
                "recursive",
                "is_monogenic",
                "is_cycle_free",
                "strongly_compress",
            }:
                # Has to be special case where we can use reduce_to_2_generators
                assert len(next_proof_step[2][0]) <= 2
                gens = "ab"
                if len(next_proof_step[2][0]) == 1:
                    gens = "a"
                result.append(
                    (step_nr,) + proof_step[1:],
                )
                step_nr += 1
                result.append(
                    (step_nr, "reduce_to_2_generators", next_proof_step[2], gens),
                )
                step_nr += 1
                idx += 1
                continue
            elif next_proof_step[1] == "reduce_to_2_generators":
                assert idx + 2 <= len(proof) - 1
                assert len(proof[idx + 2][2]) == 3
                if proof[idx + 2][2][1][0] == proof[idx + 2][2][2][0]:
                    # check we get a right cycle free presentation
                    if proof[idx + 2][2][1][-1] != proof[idx + 2][2][2][-1]:
                        # Same first letters, need to apply reverse before
                        # reducing it will get further swapped at a later
                        # point
                        result.append(
                            (step_nr,) + proof_step[1:],
                        )
                        step_nr += 1
                        result.append(
                            (step_nr, "reverse", next_proof_step[2]),
                        )
                        step_nr += 1
                        assert len(next_proof_step) >= 4
                        result.append(
                            (
                                step_nr,
                                "reduce_to_2_generators",
                                do_correct_reverse_pres(next_proof_step[2]),
                                next_proof_step[3],
                            ),
                        )
                        step_nr += 1
                        result.append(
                            (
                                step_nr,
                                "reverse",
                                do_correct_reverse_pres(proof[idx + 2][2]),
                            ),
                        )
                        step_nr += 1
                        idx += 2
                        continue
                assert set(proof_step[2][0]) == {"a", "b"}
                # Must be left cycle free. Check if we send lhs to x, if not then reorder alphabet
                if proof[idx + 2][2][1][0] != proof_step[2][0][0]:
                    # Check it begins with the other letter
                    assert proof[idx + 2][2][1][0] != proof_step[2][1]
                    # Need an alphabet reorder
                    result.append(
                        (step_nr, "reorder_alphabet", proof_step[2]),
                    )
                    step_nr += 1
                    assert len(proof_step) >= 4
                    result.append(
                        (
                            step_nr,
                            "strongly_compress",
                            do_reorder_alphabet(proof_step[2]),
                            proof_step[3],
                        )
                    )
                    step_nr += 1
                    assert len(next_proof_step) >= 4
                    result.append(
                        (
                            step_nr,
                            "reduce_to_2_generators",
                            next_proof_step[2],
                            next_proof_step[3],
                        ),
                    )
                    step_nr += 1
                    idx += 2
                    continue
                # Check where the singular letter is
                morph = next_proof_step[3]
                assert set(morph) == {"a", "b"}, morph
                assert morph.count("a") == 1 or morph.count("b") == 1
                singular_idx = morph.find("a")
                if morph.count("a") != 1:
                    singular_idx = morph.find("b")
                letter_to_compress_word = {
                    letter: word for word, letter in proof_step[3]
                }
                compression_word = letter_to_compress_word[
                    next_proof_step[2][0][singular_idx]
                ]
                if not proof_step[2][1].startswith(compression_word):
                    # LHS does not start with compression word, flip
                    result.append(
                        (step_nr, "flip_all_relations", proof_step[2]),
                    )
                    step_nr += 1
                    assert len(proof_step) >= 4
                    result.append(
                        (
                            step_nr,
                            "strongly_compress",
                            do_flip_all_relations(proof_step[2]),
                            proof_step[3],
                        )
                    )
                    step_nr += 1
                    assert len(next_proof_step) >= 4
                    result.append(
                        (
                            step_nr,
                            "reduce_to_2_generators",
                            do_flip_all_relations(next_proof_step[2]),
                            next_proof_step[3],
                        ),
                    )
                    step_nr += 1
                    result.append(
                        (
                            step_nr,
                            "flip_all_relations",
                            do_flip_all_relations(proof[idx + 2][2]),
                        ),
                    )
                    step_nr += 1
                    idx += 2
                    continue
                # Is a normal form, no further processing required
            elif next_proof_step[1] != "is_special":
                # unexpected step following strong compressions
                assert False, proof

        result.append((step_nr,) + proof_step[1:])
        step_nr += 1
        idx += 1
    return tuple(result)


def normalize_proof(proof: tuple[tuple, ...]) -> tuple[tuple, ...]:
    """Iterate normalization until proof is stable."""
    old_proof = None
    while proof != old_proof:
        proof, old_proof = normalize_proof_single_step(proof), proof
    return proof


def split_proof_into_recursives(proof: tuple[tuple, ...]) -> list[tuple[tuple, ...]]:
    """Splits a given proof into a sequence of recursive proofs.

    Returns a tuple of proofs. All proofs in the output apart from possibly the
    last are recursive.
    """
    result = []
    splitting_steps = {
        "reverse",
        "alphabet_isomorphism",
        "strongly_compress",
        "reduce_to_2_generators",
        "recursive",
        "flip_all_relations",
        "reorder_alphabet",
    }
    last = 0
    for i, proof_step in enumerate(proof):
        if last > i:
            continue
        assert len(proof_step) >= 3
        if proof_step[1] in splitting_steps:
            assert i != len(proof) - 1 or proof_step[1] == "recursive"
            if proof_step[1] == "recursive":
                assert i == len(proof) - 1
                # we won't split on the final recursive step so just skip it
                last = i + 1
                continue
            next_proof_step = proof[i + 1]
            assert len(next_proof_step) >= 3
            if proof_step[1] == "strongly_compress":
                assert next_proof_step[1] in {
                    "reduce_to_2_generators",
                    "is_special",
                }, proof
                continue
            elif proof_step[1] == "reduce_to_2_generators":
                assert i != 0
                assert proof[i - 1][1] == "strongly_compress"

            # TODO: should reset numbering, but it does not affect correctness
            result.append(
                proof[last : i + 1] + ((i + 1, "recursive", next_proof_step[2]),)
            )
            last = i + 1
    if last < len(proof):
        result.append(proof[last:])
    return result


def is_convertible_proof(proof_steps_tuple: tuple, good_steps: set[str]) -> bool:
    for step in proof_steps_tuple:
        assert len(step) >= 2
        if step[1] not in good_steps or (
            step[1] == "is_complete_rws" and step[3] != "lenlex"
        ):
            return False
    return True


def make_dependency_graph(
    all_proof_steps: list[tuple[tuple, ...]],
) -> tuple[dict, list[set[int]]]:
    adj = [set()]
    pres_to_idx = {None: 0}
    for proof_steps_tuple in all_proof_steps:
        assert len(proof_steps_tuple) >= 1
        assert len(proof_steps_tuple[0]) >= 3
        assert len(proof_steps_tuple[-1]) >= 3
        ip = proof_steps_tuple[0][2]
        if proof_steps_tuple[-1][1] != "recursive":
            tp = None
        else:
            tp = proof_steps_tuple[-1][2]
        if ip == tp:
            continue
        for p in {ip, tp}:
            if p not in pres_to_idx:
                pres_to_idx[p] = len(adj)
                adj.append(set())
        adj[pres_to_idx[ip]].add(pres_to_idx[tp])
    return pres_to_idx, adj


def reverse_adj(adj: list[set[int]]) -> list[set[int]]:
    result = [set() for _ in range(len(adj))]
    for i, nbs in enumerate(adj):
        for j in nbs:
            result[j].add(i)
    return result


def sort_into_layers(adj: list[set[int]]) -> tuple[dict[int, int], set[int]]:
    rev_adj = reverse_adj(adj)
    n = len(adj)
    layer_of_idx: list[int | None] = [None for _ in range(n)]
    seen = set()
    que = []
    for i in range(n):
        if len(adj[i]) == 0:
            layer_of_idx[i] = 0
            que.append(i)
            seen.add(i)

    idx = 0
    while idx < len(que):
        i = que[idx]
        for j in rev_adj[i]:
            if j in seen:
                continue
            # que always contains elements ascending order by layer, if we
            # haven't seen j already, this must be the shortest path
            layer_of_idx[j] = layer_of_idx[i] + 1
            que.append(j)
            seen.add(j)
        idx += 1

    result = {}
    failed = set()
    for idx, layer in enumerate(layer_of_idx):
        if layer is None:
            failed.add(idx)
        result[idx] = layer

    return result, failed


if __name__ == "__main__":
    arg_parser = argparse.ArgumentParser("to_rocq_proof.py")
    arg_parser.add_argument(
        "-b",
        "--batch-size",
        help="The maximum size of an output batch (default: 1000)",
        type=int,
        default=1000,
    )
    arg_parser.add_argument(
        "-o",
        "--output",
        help="Path to the output directory, must be empty (default: ./rocq)",
        type=Path,
        default="./rocq",
    )
    arg_parser.add_argument(
        "-v",
        "--verbose",
        help="Verbose output (default: False)",
        action="store_true",
    )
    args = arg_parser.parse_args()
    batch_size = args.batch_size
    verbose = args.verbose
    output_directory = args.output
    output_directory.mkdir(exist_ok=True)
    if any(output_directory.iterdir()):
        raise RuntimeError(
            f"The given output directory path {output_directory} is not empty!"
        )

    con = sqlite3.connect("database.db")
    cur = con.cursor()

    good_steps = set(_to_rocq_proof_steps.keys())

    current_batches_number = Counter()
    current_batches: dict[str, list[tuple[Presentation, tuple[ProofStep]]]] = {
        "CompleteRewritingSystem": [],
        "Monogenic": [],
        "FreeProductMonogenicAndFree": [],
        "EqualNumberOfOccurences": [],
        "Watier": [],
        "SmallOverlap": [],
        "Reverse": [],
        "Special": [],
        "StronglyCompressToSpecial": [],
        "CycleFree": [],
        "FlipAllRelations": [],
        "StronglyCompressAndReduce": [],
        "AlphabetIsom": [],
        "AlphabetReorder": [],
    }

    presentation_to_idx: dict[tuple[str, ...], list[int]] = {}

    # Make proof folder structure
    for certificate_type in current_batches:
        (output_directory / certificate_type).mkdir(parents=True, exist_ok=True)
        for subdirectory in {"pres", "dec"}:
            (output_directory / certificate_type / subdirectory).mkdir(
                parents=True, exist_ok=True
            )

    all_proof_tuples: list[tuple[tuple, ...]] = []

    recursive_join_query = """
SELECT rec.proof_steps AS rec_steps, base.proof_steps as base_steps
FROM proof_table rec, proof_table base
WHERE rec.conditional_presentation_id == base.presentation_id
    """

    print("Computing all simple denormalizations for recursives . . .")

    for recursive_proof_steps_string, proof_steps_string in cur.execute(
        recursive_join_query
    ):
        recursive_proof_steps_tuple = literal_eval(recursive_proof_steps_string)
        assert len(recursive_proof_steps_tuple) > 0
        assert len(recursive_proof_steps_tuple[-1]) > 2
        rec_pres = recursive_proof_steps_tuple[-1][2]

        proof_steps_tuple = literal_eval(proof_steps_string)
        assert len(proof_steps_tuple) > 0
        assert len(proof_steps_tuple[0]) > 2
        base_pres = proof_steps_tuple[0][2]

        if not is_convertible_proof(
            proof_steps_tuple, good_steps
        ) or not is_convertible_proof(recursive_proof_steps_tuple, good_steps):
            continue

        if rec_pres == base_pres:
            continue

        derivations = compute_all_simple_denormalizations(rec_pres)
        assert base_pres in derivations, (rec_pres, base_pres)

        all_proof_tuples.extend(derivations[base_pres])

    print("Collecting all proofs . . .")

    for proof_steps_string in cur.execute("SELECT proof_steps FROM proof_table"):
        proof_steps_tuple = literal_eval(proof_steps_string[0])

        if not is_convertible_proof(proof_steps_tuple, good_steps):

            continue

        all_proof_tuples.extend(
            split_proof_into_recursives(normalize_proof(proof_steps_tuple))
        )

    print("Constructing dependency graph . . .")

    pres_to_idx, dep_graph = make_dependency_graph(all_proof_tuples)
    rev_dep_graph = reverse_adj(dep_graph)
    idx_to_layer, failed = sort_into_layers(dep_graph)
    assert len(failed) == 0

    layers = [
        [] for _ in range(max(x for x in idx_to_layer.values() if x is not None) + 1)
    ]
    for proof_steps_tuple in all_proof_tuples:
        assert len(proof_steps_tuple) >= 1
        assert len(proof_steps_tuple[0]) >= 2
        p = proof_steps_tuple[0][2]
        assert p in pres_to_idx
        idx = pres_to_idx[p]
        layer = idx_to_layer[pres_to_idx[p]]
        assert layer >= 0
        layers[layer].append(proof_steps_tuple)

    proof_position = {}
    for layer in layers:
        for proof_steps_tuple in layer:

            proof = parse_proof_tuple(proof_steps_tuple)
            certificate_type = to_rocq_presentation_certificate_type(proof)
            assert certificate_type is not None
            initial_presentation = proof[0].current_presentation

            batch = current_batches[certificate_type]
            if not (
                proof_steps_tuple[-1][1] == "recursive"
                and proof_steps_tuple[-1][2] not in proof_position
            ):
                batch.append((initial_presentation, proof))

            if batch_size is not None and len(batch) >= batch_size:
                pop_batch_and_write_to_file(
                    certificate_type,
                    current_batches,
                    current_batches_number,
                    batch_size,
                    proof_position,
                    output_directory,
                )
        # Empty all half full batches at end
        for certificate_type in current_batches:
            if len(current_batches[certificate_type]) > 0:
                pop_batch_and_write_to_file(
                    certificate_type,
                    current_batches,
                    current_batches_number,
                    batch_size,
                    proof_position,
                    output_directory,
                )
