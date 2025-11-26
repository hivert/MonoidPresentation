"""
(c) Copyright 2025 Reinis Cirpons.
Distributed under the terms of CeCILL-B.

This module contains a reference implementation of a checker for the proof
database using the python package `libsemigroups_pybind11`.

The actual verification of the database is done using the check_proofs.py script.
"""

from inspect import getfullargspec as get_args
from textwrap import TextWrapper
from typing import Callable, Any, Union

from libsemigroups_pybind11 import (
    Kambites,
    presentation,
    ukkonen,
    Presentation,
    congruence_kind,
    KnuthBendix,
    ReportGuard,
)

# Helper functions


def wrap(thing, indent: int = 0) -> str:
    wrap = TextWrapper(break_on_hyphens=False, width=80, subsequent_indent=indent * " ")
    return "\n".join(wrap.wrap(str(thing)))


def _warn(f: Callable, args: list, msg: str) -> None:
    print(f'FAILED call to "{f.__name__}" with arguments:')
    for name, arg in zip(get_args(f).args, args):
        print(f"  * {name}: {wrap(arg, 7 + len(name))}")
    print(wrap("- " + msg, 2))


# Hack until libsemigroups_pybind11 implements a properly typeable Presentation type
PresentationType = Any


def to_presentation(p: tuple[str, ...]) -> PresentationType:
    pp = Presentation(p[0])
    pp.contains_empty_word(True)
    for i in range(1, len(p), 2):
        presentation.add_rule(pp, p[i], p[i + 1])
    return pp


def from_presentation(p: PresentationType) -> tuple[str, ...]:
    return (p.alphabet(), *p.rules)


def _make_kambites(p: PresentationType) -> Kambites:
    return Kambites(congruence_kind.twosided, p)


def _is_cn_monoid(
    p: tuple[str, ...],
    expected_pieces: tuple[tuple[str, ...], ...],
    n: int,
    called_by: Callable,
) -> Union[None, tuple[str, ...]]:
    if len(expected_pieces) != len(p) - 1:
        _warn(
            called_by,
            [p, expected_pieces],
            f"Expected {len(p) - 1} piece decompositions as the 2nd argument, found {len(expected_pieces)}!",
        )

    pp = to_presentation(p)
    k = _make_kambites(to_presentation(p))
    for i, rule in enumerate(pp.rules):
        join = "".join(expected_pieces[i])
        if join != rule:
            _warn(
                called_by,
                [p, expected_pieces],
                f'Expected the product of the words {expected_pieces[i]} to be "{rule}", found "{join}"!',
            )
            return None
        if len(expected_pieces[i]) < n:
            _warn(
                called_by,
                [p, expected_pieces],
                f"Expected >= {n} pieces, found {len(expected_pieces[i])}!",
            )
            return None
        found_pieces = tuple(ukkonen.pieces(k.ukkonen(), rule))

        if found_pieces != expected_pieces[i]:
            _warn(
                called_by,
                [p, expected_pieces],
                f"Expected pieces {expected_pieces[i]}, found {found_pieces}!",
            )
            return None

    return p


def _validate_relations(
    called_by: Callable, args: list, p: tuple[str, ...], w: str
) -> bool:
    if any(False if x in p[0] else True for x in w):
        _warn(
            called_by,
            args,
            f'Invalid relation word "{w}", contains a letter not in {p[0]}!',
        )
        return False
    return True


def _find_relation(
    p: tuple[str, ...], u: str, v: str
) -> Union[tuple[int, int], tuple[None, None]]:
    for i in range(1, len(p), 2):
        if p[i] == u and p[i + 1] == v:
            return i, i + 1
        elif p[i + 1] == u and p[i] == v:
            return i + 1, i
    return None, None


def _validate_elementary_sequence(
    called_by: Callable,
    p: tuple[str, ...],
    lhs: str,
    rhs: str,
    e: tuple[tuple[tuple[str, str, str], tuple[str, str, str]], ...],
) -> bool:
    if not _validate_relations(
        called_by, [p, lhs, rhs, e], p, lhs
    ) or not _validate_relations(called_by, [p, lhs, rhs, e], p, rhs):
        return False

    if len(e) == 0:
        if lhs != rhs:
            _warn(
                called_by,
                [p, lhs, rhs, e],
                f"Invalid elementary sequence, expected nonzero length!",
            )
            return False
        return True

    for i, step in enumerate(e):
        if len(step) != 2 or len(step[0]) != 3 or len(step[1]) != 3:
            _warn(
                called_by,
                [p, lhs, rhs, e],
                f"Invalid elementary sequence, each elementary rewrite must "
                f"be a pair of triples but got e[{i}]={step}!",
            )
            return False

    first = "".join(e[0][0])
    if lhs != first:
        _warn(
            called_by,
            [p, lhs, rhs, e],
            f'Invalid elementary sequence, "{lhs}" == "{first}" expected!',
        )
        return False
    last = "".join(e[-1][1])
    if rhs != last:
        _warn(
            called_by,
            [p, lhs, rhs, e],
            f'Invalid elementary sequence, "{rhs}" == "{last}" expected!',
        )
        return False

    last = lhs
    for step in e:
        if "".join(step[0]) != last:
            _warn(
                called_by,
                [p, lhs, rhs, e],
                f'Invalid elementary sequence, "{step[0]}" == "{last}" expected!',
            )
            return False
        elif step[0][0] != step[1][0]:
            _warn(
                called_by,
                [p, lhs, rhs, e],
                f'Invalid elementary sequence, "{step[0][0]}" == "{step[1][0]}" expected!',
            )
            return False
        elif step[0][2] != step[1][2]:
            _warn(
                called_by,
                [p, lhs, rhs, e],
                f'Invalid elementary sequence, "{step[0][2]}" == "{step[1][2]}" expected!',
            )
            return False
        last = "".join(step[1])
        if step[0][1] != step[1][1] and _find_relation(p, step[0][1], step[1][1]) == (
            None,
            None,
        ):
            _warn(
                called_by,
                [p, lhs, rhs, e],
                f'Invalid elementary sequence, no relation "{step[0][1]}" = "{step[1][1]}" found!',
            )
            return False
    return True


#


def is_valid_presentation(p: tuple[str, ...]) -> bool:
    return (
        len(p) % 2 == 1
        and all(isinstance(x, str) for x in p)
        and all(x in p[0] for rule in p[1:] for x in rule)
    )


# Transformation steps


def lenlex_order(letter_perm: str) -> Callable[[str, str], bool]:
    def compare(word1: str, word2: str) -> bool:
        if word1 == word2:
            return True
        if len(word1) != len(word2):
            return len(word1) < len(word2)
        i = 0
        while word1[i] == word2[i]:
            i += 1
        return letter_perm.index(word1[i]) < letter_perm.index(word2[i])

    return compare


def tietze_add_generator(
    p: tuple[str, ...], letter: str, subword: str
) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    if len(letter) != 1:
        _warn(
            tietze_add_generator,
            [p, letter, subword],
            f'Invalid generator, "{letter}" must have length 1, not {len(letter)}!',
        )
        return None
    if letter in p[0]:
        _warn(
            tietze_add_generator,
            [p, letter, subword],
            f'Invalid generator, "{letter}" already belongs to the alphabet {p[0]}!',
        )
        return None
    elif not _validate_relations(
        tietze_add_generator, [p, letter, subword], p, subword
    ):
        return None
    return (p[0] + letter, *p[1:]) + (letter, subword)


def tietze_rm_generator(
    p: tuple[str, ...], letter: str
) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    if len(letter) != 1:
        _warn(
            tietze_rm_generator,
            [p, letter],
            f'Invalid generator, "{letter}" must have length 1, not {len(letter)}!',
        )
        return None

    if letter not in p[0]:
        _warn(
            tietze_rm_generator,
            [p, letter],
            f'Invalid generator, "{letter}" already belongs to the alphabet "{p[0]}"!',
        )
        return None
    try:
        pos = p[1:].index(letter) + 1
    except ValueError:
        _warn(
            tietze_rm_generator,
            [p, letter],
            f'Invalid generator "{letter}", valid values are "{p[0]}"!',
        )
        return None
    q = list(p)
    if pos % 2 == 1:  # lhs
        subword = q[pos + 1]
        del q[pos + 1]
        del q[pos]
    else:
        subword = q[pos - 1]
        del q[pos]
        del q[pos - 1]
    # print(q, subword, letter)
    r = to_presentation(tuple(q))
    presentation.replace_subword(r, letter, subword)
    r.alphabet(r.alphabet().replace(letter, ""))
    return from_presentation(r)


def tietze_add_relation(
    p: tuple[str, ...], lhs: str, rhs: str, e
) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    if not _validate_elementary_sequence(tietze_add_relation, p, lhs, rhs, e):
        return None
    return (*p, lhs, rhs)


def tietze_rm_relation(
    p: tuple[str, ...], u: str, v: str, e
) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    pos_u, pos_v = _find_relation(p, u, v)

    if pos_u is None:
        _warn(
            tietze_rm_relation,
            [p, u, v, e],
            f'Invalid relation word, "{u}" is not a relation word!',
        )
        return None
    if pos_v is None:
        _warn(
            tietze_rm_relation,
            [p, u, v, e],
            f'Invalid relation word, "{v}" is not a relation word!',
        )
        return None
    if not _validate_elementary_sequence(tietze_rm_relation, p, u, v, e):
        return None
    rules_in_elementary_sequence = (p[0],) + tuple(
        sequence_triple[1]
        for sequence_triple_pair in e
        for sequence_triple in sequence_triple_pair
    )

    if pos_v < pos_u:
        pos_u, pos_v = pos_v, pos_u
    result = p[:pos_u] + p[pos_u + 1 : pos_v] + p[pos_v + 1 :]

    if (
        u != v
        and _find_relation(rules_in_elementary_sequence, u, v) != (None, None)
        and _find_relation(result, u, v) == (None, None)
    ):
        _warn(
            tietze_rm_relation,
            [p, u, v, e],
            f"Invalid elementary sequence, the relation {u} = {v} cannot "
            + "appear in the elementary sequence proving that "
            + "it is a consequence of the other relations!",
        )
        return None

    return result


# Decidable word problem checks
def is_c3_monoid(
    p: tuple[str, ...], expected_pieces: tuple[tuple[str, ...], ...]
) -> Union[None, tuple[str, ...]]:
    assert is_valid_presentation(p)
    return _is_cn_monoid(p, expected_pieces, 3, is_c3_monoid)


def is_c4_monoid(
    p: tuple[str, ...], expected_pieces: tuple[tuple[str, ...], ...]
) -> Union[None, tuple[str, ...]]:
    assert is_valid_presentation(p)
    return _is_cn_monoid(p, expected_pieces, 4, is_c4_monoid)


def equal_number_of_occurrences_of(
    p: tuple[str, ...], letter: str
) -> Union[None, tuple[str, ...]]:
    assert is_valid_presentation(p)
    if not p[0] in ("ab", "ba"):
        _warn(
            equal_number_of_occurrences_of,
            [p, letter],
            f'Invalid alphabet, expected "ab" or "ba" found "{p[0]}"!',
        )
        return None
    elif not letter in ("a", "b"):
        _warn(
            equal_number_of_occurrences_of,
            [p, letter],
            f'Invalid letter, expected "a" or "b" found "{letter}"!',
        )
        return None

    for i in range(1, len(p), 2):
        lhs = p[i]
        num = 0
        for x in lhs:
            if x == letter:
                num += 1
        rhs = p[i + 1]
        for x in rhs:
            if x == letter:
                num -= 1
        if num != 0:
            _warn(
                equal_number_of_occurrences_of,
                [p, letter],
                f"The number of occurrence of {letter} is not the same on both"
                + f"sides of the relation {lhs} = {rhs}",
            )
            return None
    return p


def is_watier1(p: tuple[str, ...]) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    if not p[0] in ("ab", "ba"):
        _warn(
            is_watier1,
            [p],
            f'Invalid alphabet, expected "ab" or "ba" found "{p[0]}"!',
        )
        return None
    elif len(p) != 3:
        _warn(
            is_watier1,
            [p],
            f"Invalid presentation, expected 1-relation found {(len(p) - 1) // 2}!",
        )
        return None
    elif len(p[1]) < 2 or len(p[2]) < 2:
        _warn(
            is_watier1,
            [p],
            "Invalid presentation, all relation words must have size at "
            + f"least 2, found |{p[1]}| = {len(p[1])} and |{p[2]}| = "
            + f"{len(p[2])}!",
        )
        return None
    elif p[1][0] + p[1][-1] != "ba" or p[2][0] + p[2][-1] != "aa":
        _warn(
            is_watier1,
            [p],
            "Invalid presentation, expected relation of the form bua = ava,"
            + f"found {p[1]} = {p[2]}!",
        )
        return None

    it0 = p[1].find("a")
    it1 = 0
    num_leading_b_s = it0

    while it0 != len(p[1]):
        # Start of the next sequence of b's
        it1 = p[1].find("b", it0 + 1)
        if it1 == -1:
            break
        # End of the next sequence of b's
        it0 = p[1].find("a", it1 + 1)
        if (it0 - it1) >= num_leading_b_s:
            _warn(
                is_watier1,
                [p],
                'Invalid presentation, initial sequence of "b"s is of length'
                + f'{num_leading_b_s} and there\'s a longer sequence of "b"s'
                + f" in position [{it1},{it0})!",
            )
            return None
    return p


def is_special(p: tuple[str, ...]) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    if len(p) != 3:
        _warn(
            is_special,
            [p],
            f"Invalid presentation, expected one relation found {(len(p) - 1) // 2}!",
        )
        return None
    if len(p[1]) != 0 and len(p[2]) != 0:
        _warn(
            is_special,
            [p],
            f"Invalid presentation, expected one relation word of length 0!",
        )
        return None
    return p


def is_monogenic(p: tuple[str, ...]) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    seen = set()
    for i in range(1, len(p)):
        if len(set(p[i])) > 1:
            _warn(
                is_monogenic,
                [p],
                f"Invalid presentation, expected each relation word to be a power of a generator, found {p[i]}.",
            )
            return None
        seen |= set(p[i])
    if len(seen) > 1:
        _warn(
            is_monogenic,
            [p],
            f"Invalid presentation, expected each relation word to be a power of the same generator, found {p}.",
        )
        return None
    return p


def is_cycle_free(p: tuple[str, ...]) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    for i in range(1, len(p), 2):
        if len(p[i]) == 0 or len(p[i + 1]) == 0:
            _warn(
                is_cycle_free,
                [p],
                f"Invalid presentation, expected all relation words to be non empty, but encountered {p[i]}={p[i+1]}",
            )
            return None
        if p[i][0] == p[i + 1][0]:
            _warn(
                is_cycle_free,
                [p],
                f"Invalid presentation, expected initial letters to differ, but found {p[i]}={p[i+1]}.",
            )
            return None
        if p[i][-1] == p[i + 1][-1]:
            _warn(
                is_cycle_free,
                [p],
                f"Invalid presentation, expected initial letters to differ, but found {p[i]}={p[i+1]}.",
            )
            return None
    return p


def recursive(p: tuple[str, ...]) -> Union[tuple[str, ...], None]:
    # TODO: This is a hack for now.
    # In the future should pull data from database to check
    # if p has a valid proof.
    return p


def strongly_compress(
    p: tuple[str, ...], morph: tuple[tuple[str, str], ...]
) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    if len(morph) == 0:
        return None
    k = len(morph[0][0])
    morph_dict = {key: value for key, value in morph}
    q = ["".join(set(morph_dict.values()))]
    for i in (1, 2):
        compressed_word = []
        for j in range(len(p[i])):
            piece = p[i][j : j + k]
            if len(piece) < k:
                break
            if piece not in morph_dict:
                return None
            compressed_word.append(morph_dict[piece])
        q.append("".join(compressed_word))
    return tuple(q)


def reduce_to_2_generators(
    p: tuple[str, ...], morph: str
) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    if morph.count(morph[p[0].index(p[1][0])]) == len(morph) - 1:
        idx = 0
    elif morph.count(morph[p[0].index(p[2][0])]) == len(morph) - 1:
        idx = 1
    else:
        return None
    q = to_presentation(p)
    if not presentation.reduce_to_2_generators(q, idx):
        return None
    return from_presentation(q)


def reverse(p: tuple[str, ...]) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    q = to_presentation(p)
    presentation.reverse(q)
    return from_presentation(q)


def alphabet_isomorphism(
    p: tuple[str, ...], morph: str
) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)
    if len(p[0]) != len(morph) or len(morph) != len(set(morph)):
        _warn(
            alphabet_isomorphism,
            [p, morph],
            f"Morphism not a bijection",
        )
        return None
    mapping: dict[str, str] = {}
    for i, j in zip(p[0], morph):
        mapping[i] = j
    q = [morph]
    for i in range(1, len(p)):
        q.append("".join(mapping[letter] for letter in p[i]))
    return tuple(q)


def is_complete_rws(
    p: tuple[str, ...], term_method: str, term_cert: str
) -> Union[tuple[str, ...], None]:
    assert is_valid_presentation(p)

    if term_method not in {"lenlex", "cpf"}:
        _warn(
            is_complete_rws,
            [p, term_method, term_cert],
            f"Invalid termination certification method, expected 'lenlex' or 'cpf', found {term_method}!",
        )
        return None

    if term_method == "cpf":
        # Not supported in current version
        return None
    elif term_method == "lenlex":
        if set(term_cert) != set(p[0]):
            _warn(
                is_complete_rws,
                [p, term_method, term_cert],
                f"Invalid termination certificate for method 'lenlex', "
                + 'expected permutation of "{p[0]}", but found {term_cert}!',
            )
            return None

        compare = lenlex_order(term_cert)
        for i in range(1, len(p), 2):
            if not compare(p[i + 1], p[i]):
                _warn(
                    is_complete_rws,
                    [p, term_method, term_cert],
                    f"System does not respect lenlex order {'<'.join(term_cert)} in rule {p[i]} -> {p[i+1]}!",
                )
                return None

    # Check locally confluent
    ReportGuard(False)
    kb = KnuthBendix(congruence_kind.twosided, to_presentation((term_cert,) + p[1:]))
    if not kb.confluent():
        _warn(
            is_complete_rws,
            [p, term_method, term_cert],
            f"System {p} is not locally confluent!",
        )
        return None

    return p


def no_proof(_: tuple[str, ...]) -> Union[tuple[str, ...], None]:
    return None


def sort_presentation(p: tuple[str, ...]) -> tuple[str, ...]:
    sorted_alphabet = "".join(sorted(p[0]))
    sorted_relations = [
        tuple(sorted((p[i], p[i + 1]), key=lambda x: (len(x), x)))
        for i in range(1, len(p), 2)
    ]
    sorted_relations.sort(key=lambda x: (len(x[0]), x, len(x[1]), x[1]))
    return (sorted_alphabet,) + tuple(
        relation_word for relation in sorted_relations for relation_word in relation
    )


_proof_step_to_function = {
    "tietze_add_generator": tietze_add_generator,
    "tietze_rm_generator": tietze_rm_generator,
    "tietze_add_relation": tietze_add_relation,
    "tietze_rm_relation": tietze_rm_relation,
    "strongly_compress": strongly_compress,
    "reduce_to_2_generators": reduce_to_2_generators,
    "reverse": reverse,
    "alphabet_isomorphism": alphabet_isomorphism,
    "is_watier1": is_watier1,
    "is_complete_rws": is_complete_rws,
    "is_c4_monoid": is_c4_monoid,
    "is_c3_monoid": is_c3_monoid,
    "equal_number_of_occurrences_of": equal_number_of_occurrences_of,
    "is_special": is_special,
    "is_cycle_free": is_cycle_free,
    "recursive": recursive,
    "is_monogenic": is_monogenic,
    "no_proof": no_proof,
}


def proof_evaluator(proof, verbose=True):
    transformations = (
        "tietze_add_generator",
        "tietze_rm_generator",
        "tietze_add_relation",
        "tietze_rm_relation",
        "strongly_compress",
        "reduce_to_2_generators",
        "reverse",
        "alphabet_isomorphism",
    )

    decidable = (
        "is_watier1",
        "is_complete_rws",
        "is_complete_adian_rws",
        "is_c4_monoid",
        "is_c3_monoid",
        "equal_number_of_occurrences_of",
        "is_special",
        "is_cycle_free",
        "recursive",
        "is_monogenic",
    )

    # 1. check that "proof" is a valid sequence of steps
    if len(proof) == 0:
        if verbose:
            print("- Invalid proof, proofs must not be of length 0!")
        return False

    last_step = None
    for i, step in enumerate(proof):
        if len(step) < 2:
            if verbose:
                print(
                    f"- Invalid proof step {i}, steps must have at least 2 entries, but found{len(step)}!"
                )
            return False
        func = _proof_step_to_function[step[1]]
        expected_num_args = len(get_args(func).args)
        if len(step) - 2 != expected_num_args:
            if verbose:
                print(
                    wrap(
                        f"- Invalid proof step {i}, the function {step[1]} expects "
                        + f"{expected_num_args} arguments, but found {len(step) - 2}!",
                        2,
                    )
                )
            return False
        if not step[1] in transformations:
            last_step = i
            break
    if last_step != len(proof) - 1:
        if verbose:
            print("Invalid proof structure 1!")
        return False
    if proof[last_step][1] not in decidable:
        if verbose:
            print(f"Invalid proof structure 2! Last step was {proof[last_step]}.")
        return False

    # 2. "run" the proof
    prev_output = sort_presentation(proof[0][2])
    for i, step in enumerate(proof):
        next_input = sort_presentation(step[2])
        if prev_output != next_input:
            print(
                f"- Invalid proof, expected input of step {i} to be:\n"
                + f"    {wrap(next_input, 4)}\n  but found:\n    {wrap(prev_output, 4)}"
            )
            return False
        func = eval(step[1])
        prev_output = func(step[2], *step[3:])
        if prev_output is None:
            return False
        prev_output = sort_presentation(prev_output)

    return True
