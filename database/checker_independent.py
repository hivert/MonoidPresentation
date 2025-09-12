"""
An independent proof verifier for the 1-relation database.

A largely faithful implementation of the proof spec. Functions have often been implemented in a slightly naive
manner, as speed isn't the goal here.

Does make use of check_termination_certificate from the reference implementation.
Proofs decided with is_adian_rws and any recursively depending on them are
ignored in the database.

The actual verification of the database is done using the check_proofs.py script.
"""

import inspect

ALLOWED_ALPHABET = set("abcdefghijklmnopqrstuvwxyz")
VERIFIED_DECIDABLE_PRESENTATIONS = set()


def presentation_relations(p):
    return [(p[i], p[i + 1]) for i in range(1, len(p), 2)]


def presentation_relations_flat(p):
    return p[1:]


def presentation_alphabet(p):
    return p[0]


def is_valid_presentation(p):
    if not (isinstance(p, tuple) and len(p) % 2 == 1):
        return False
    if not all(isinstance(x, str) for x in p):
        return False
    if len(p[0]) == 0:
        return False
    alpha = set(p[0])
    if len(alpha) != len(p[0]):
        return False
    for x in p[1:]:
        if not set(x).issubset(alpha):
            return False
    if len(set(presentation_relations(p))) != len(presentation_relations(p)):
        return False
    # next check is in spec, but is unnecessary/incorrect
    # for i in range(1, len(p), 2):
    #    if (p[i], p[i+1]) > (p[i+1], p[i]):
    #        return False
    return True


def is_valid_word(p, w):
    if not isinstance(w, str):
        return False
    if not set(w).issubset(presentation_alphabet(p)):
        return False
    return True


### Transformations


def is_valid_elementary_rewrite(p, rw):
    if not (isinstance(rw, tuple) and len(rw) == 2):
        return False
    if not all(isinstance(x, tuple) and len(x) == 3 for x in rw):
        return False
    if not all(is_valid_word(p, w) for triple in rw for w in triple):
        return False
    return (
        rw[0][0] == rw[1][0]
        and rw[0][2] == rw[1][2]
        and (
            (rw[0][1], rw[1][1]) in presentation_relations(p)
            or (rw[1][1], rw[0][1]) in presentation_relations(p)
        )
        or (rw[0][1] == rw[1][1])
    )


def is_valid_elementary_sequence(p, seq):
    if not (isinstance(seq, tuple) and len(seq) >= 1):
        return False
    if not all(is_valid_elementary_rewrite(p, rw) for rw in seq):
        return False
    for i in range(len(seq) - 1):
        if "".join(seq[i][1]) != "".join(seq[i + 1][0]):
            return False
    return True


def tietze_add_generator(p, g, w):
    if not (isinstance(g, str) and len(g) == 1 and g in ALLOWED_ALPHABET):
        return None
    if g in presentation_alphabet(p):
        return None
    if not is_valid_word(p, w):
        return None
    return (presentation_alphabet(p) + g,) + presentation_relations_flat(p) + (g, w)


def _tietze_replace_generator(p, g, w):
    new_alphabet = presentation_alphabet(p).replace(g, "")
    if not set(w).issubset(new_alphabet):
        return None

    rules = presentation_relations_flat(p)
    new_rules = []
    for u, v in presentation_relations(p):
        if (u, v) == (g, w) or (u, v) == (w, g):
            continue
        u = u.replace(g, w)
        v = v.replace(g, w)
        new_rules += [u, v]
    return (new_alphabet,) + tuple(new_rules)


def tietze_rm_generator(p, g):
    if g not in presentation_alphabet(p):
        return None

    # spec doesn't forbid empty presentations, so don't check

    # we have to choose one of the rules with LHS or RHS g
    # if there are multiple, we just pick the first one we find
    try:
        pos_g = presentation_relations_flat(p).index(g)
    except ValueError:
        return None
    if pos_g % 2 == 0:
        w = presentation_relations_flat(p)[pos_g + 1]
    else:
        w = presentation_relations_flat(p)[pos_g - 1]

    return _tietze_replace_generator(p, g, w)


def tietze_add_relation(p, lhs, rhs, seq):
    if not (is_valid_word(p, lhs) and is_valid_word(p, rhs)):
        return None
    if not is_valid_elementary_sequence(p, seq):
        return None
    if "".join(seq[0][0]) != lhs or "".join(seq[-1][1]) != rhs:
        return None
    return p + (lhs, rhs)


def tietze_rm_relation(p, lhs, rhs, seq):
    if not (is_valid_word(p, lhs) and is_valid_word(p, rhs)):
        return None
    if not ("".join(seq[0][0]) == lhs and "".join(seq[-1][1]) == rhs):
        return None

    new_rules = []
    removed_rule = False
    for rule in presentation_relations(p):
        # Remove the first matching relation (in either order) we find.
        if removed_rule or (rule != (lhs, rhs) and rule != (rhs, lhs)):
            new_rules.extend(rule)
        else:
            removed_rule = True
    new_p = (presentation_alphabet(p),) + tuple(new_rules)
    if not is_valid_elementary_sequence(new_p, seq):
        return None
    return new_p


def strongly_compress(p, morph):
    if not len(presentation_relations(p)) == 1:
        return None
    if not isinstance(morph, tuple):
        return None
    if not all(isinstance(x, tuple) and len(x) == 2 for x in morph):
        return None
    if not all(is_valid_word(p, x[0]) for x in morph):
        return None
    if not all(x[1] in ALLOWED_ALPHABET for x in morph):
        return None

    k = len(morph[0][0])

    u, v = p[1], p[2]
    if (
        not k > 0
        and u[: k - 1] == v[: k - 1]
        and (u[-(k - 1) :] == v[-(k - 1) :] or k == 1)
    ):
        return None
    if not (u[:k] != v[:k] or u[-k:] != v[-k:]):
        return None

    if not all(len(x[0]) == k and len(x[1]) == 1 for x in morph):
        return None
    if len(set(x[0] for x in morph)) != len(morph):
        return None
    if len(set(x[1] for x in morph)) != len(morph):
        return None

    length_k_subwords = set()
    for x in presentation_relations_flat(p):
        for i in range(len(x) - k + 1):
            length_k_subwords.add(x[i : i + k])

    if not length_k_subwords.issubset(set(x[0] for x in morph)):
        return None

    morph_dict = {x[0]: x[1] for x in morph}
    new_rules = []
    for x in presentation_relations_flat(p):
        rule = []
        for i in range(len(x)):
            w = x[i : i + k]
            if len(w) < k:
                break
            if w not in morph_dict:
                return None
            rule.append(morph_dict[w])
        new_rules.append("".join(rule))
    new_alphabet = "".join(sorted(set(x[1] for x in morph)))
    return (new_alphabet,) + tuple(new_rules)


def is_left_cycle_free(p):
    for u, v in presentation_relations(p):
        if len(u) == 0 or len(v) == 0 or u[0] == v[0]:
            return False
    return True


def is_right_cycle_free(p):
    for u, v in presentation_relations(p):
        if len(u) == 0 or len(v) == 0 or u[-1] == v[-1]:
            return False
    return True


def reduce_to_2_generators(p, morph):
    if len(p) != 3:
        return None
    if len(presentation_alphabet(p)) < 2:
        return None
    if not is_left_cycle_free(p):
        return None
    if len(morph) != len(presentation_alphabet(p)):
        return None
    if len(set(morph)) != 2:
        return None

    morph_dict = {presentation_alphabet(p)[i]: morph[i] for i in range(len(morph))}
    u, v = p[1], p[2]
    if morph_dict[u[0]] == morph_dict[v[0]]:
        return None
    if not (morph.count(morph_dict[u[0]]) == 1 or morph.count(morph_dict[v[0]]) == 1):
        return None

    rules = presentation_relations_flat(p)
    new_alphabet = "".join(set(morph))
    new_rules = tuple("".join(morph_dict[a] for a in w) for w in rules)
    return (new_alphabet,) + tuple(new_rules)


def reverse(p):
    return (presentation_alphabet(p),) + tuple(
        v[::-1] for v in presentation_relations_flat(p)
    )


def alphabet_isomorphism(p, morph):
    if not (isinstance(morph, str) and all(x in ALLOWED_ALPHABET for x in morph)):
        return None
    if not (
        len(morph) == len(presentation_alphabet(p)) and len(morph) == len(set(morph))
    ):
        return None
    morph_dict = {presentation_alphabet(p)[i]: morph[i] for i in range(len(morph))}
    return ("".join([morph_dict[x] for x in presentation_alphabet(p)]),) + tuple(
        "".join(morph_dict[a] for a in w) for w in presentation_relations_flat(p)
    )


###############################################################################
### Decidable word problem checks
###############################################################################

########################################################
### RWS checks
########################################################


def _rewrite_with_ordering(w, order_map):
    return tuple(order_map[x] for x in w)


def _is_lenlex_reducing(p, ordering):
    order_map = {}
    for i in range(len(ordering)):
        order_map[ordering[i]] = i
    return all(
        (len(u), _rewrite_with_ordering(u, order_map))
        > (len(v), _rewrite_with_ordering(v, order_map))
        for u, v in presentation_relations(p)
    )


########################
### cpf formats currently not supported
_is_cepa_validated = lambda p, cert: False
########################


def is_terminating_rws(p, termination_method, termination_certificate):
    if termination_method == "lenlex":
        return (
            p
            if (
                isinstance(termination_certificate, str)
                and len(termination_certificate) == len(presentation_alphabet(p))
                and set(termination_certificate) == set(presentation_alphabet(p))
                and _is_lenlex_reducing(p, termination_certificate)
            )
            else None
        )
    if termination_method == "cpf":
        return (
            p
            if (
                isinstance(termination_certificate, str)
                and _is_cepa_validated(
                    list(presentation_relations(p)), termination_certificate
                )
            )
            else None
        )
    return None


def _overlap_pairs(p):
    rewritables = set()
    for u, v in presentation_relations(p):
        rewritables.add(u)

    rewritable_to = {u: set() for u in rewritables}
    for u, v in presentation_relations(p):
        rewritable_to[u].add(v)

    pairs = set()
    for u in rewritables:
        for v in rewritables:
            # u to the left of v, slide v left
            for steps_left in range(1, len(u) + 1):
                len_overlap = min(steps_left, len(v))
                if (
                    u[-steps_left : len(u) - steps_left + len_overlap]
                    == v[:len_overlap]
                ):
                    start_v_in_u = len(u) - steps_left
                    right_dangling_u = u[start_v_in_u + len(v) :]
                    right_dangling_v = v[len_overlap:]
                    for u2 in rewritable_to[u]:
                        for v2 in rewritable_to[v]:
                            crit_pair = (
                                u[:start_v_in_u] + v2 + right_dangling_u,
                                u2 + right_dangling_v,
                            )
                            if crit_pair[0] != crit_pair[1]:
                                pairs.add(((u, v), crit_pair))
    return pairs


def _find_applicable_rewrite(rws, w):
    for u, v in rws.items():
        pos = w.find(u)
        if pos != -1:
            return ((u, v), pos)
    return None


def _apply_rewrite(w, rw, pos):
    return w[:pos] + rw[1] + w[pos + len(rw[0]) :]


# this *assumes* termination
def _arbitrarily_fully_reduce(p, w):
    rewrites = {}  # can ignore duplicate LHSs - we're arbitrary
    for u, v in presentation_relations(p):
        if u not in rewrites:
            rewrites[u] = v
    res = _find_applicable_rewrite(rewrites, w)
    while res is not None:
        rw, pos = res
        w = _apply_rewrite(w, rw, pos)
        res = _find_applicable_rewrite(rewrites, w)
    return w


def _is_confluent_assuming_terminating(p):
    for overlaps in _overlap_pairs(p):
        u, v = overlaps[1]
        if _arbitrarily_fully_reduce(p, u) != _arbitrarily_fully_reduce(p, v):
            return False
    return True


def is_complete_rws(p, termination_method, termination_certificate):
    if not is_terminating_rws(p, termination_method, termination_certificate):
        return None
    if not _is_confluent_assuming_terminating(p):
        return None
    return p


########################
### IMPROVE: implement is_complete_adian_rws independently
########################

########################################################
### easier decidable checks
########################################################


def is_watier1(p):
    if len(presentation_alphabet(p)) != 2:
        return None
    if len(p) != 3:
        return None
    if presentation_alphabet(p) != "ab" and presentation_alphabet(p) != "ba":
        return None
    x, y = sorted(presentation_relations(p)[0])  # should now be ava = bua
    if len(x) < 2 or len(y) < 2:
        return None
    if x[0] != "a" or x[-1] != "a" or y[0] != "b" or y[-1] != "a":
        return None

    initial_b_run = y.find("a")

    if "b" * initial_b_run in y[initial_b_run:]:
        return None

    return p


def _add_all_subwords(pieces, seen_subwords, w):
    for i in range(0, len(w)):
        for j in range(1, len(w) - i + 1):
            seen_subwords.add(w[i : i + j])
            pieces.add(w[i : i + j])


def _pieces(p):
    pieces = set()
    seen_subwords = set()

    for w in set(presentation_relations_flat(p)):
        for i in range(0, len(w)):
            for j in range(len(w) - i, 0, -1):
                potential_piece = w[i : i + j]
                if potential_piece in seen_subwords:
                    _add_all_subwords(pieces, seen_subwords, potential_piece)
                    break
                else:
                    seen_subwords.add(potential_piece)
    return pieces


def _is_geq_n_decomp(p, d, n):
    if not (
        isinstance(d, tuple)
        and len(d) == len(presentation_relations(p))
        and all(isinstance(x, tuple) and all(is_valid_word(p, y) for y in x))
        and len(x) >= n
        for x in d
    ):
        return False
    for i in range(len(p) - 1):
        w = p[i + 1]
        if "".join(d[i]) != w:
            return False
    return True


def is_c3_monoid(p, d):
    if not _is_geq_n_decomp(p, d, 3):
        return None
    pieces = _pieces(p)
    for i in range(len(p) - 1):
        w = presentation_relations_flat(p)[i]
        if any(x not in pieces for x in d[i]):
            return None
    relation_words = set(presentation_relations_flat(p))
    for u in pieces:
        for v in pieces:
            if u + v in relation_words:
                return None
    ## TODO: haven't actually checked that the certificate contains mimimal decompositions
    return p


def is_c4_monoid(p, d):
    if not _is_geq_n_decomp(p, d, 4):
        return None
    pieces = _pieces(p)
    relation_words = set(presentation_relations_flat(p))
    prefixes = set()
    for w in relation_words:
        for i in range(1, len(w)):
            prefixes.add(w[:i])
    for u in pieces:
        if u not in prefixes:
            continue
        for v in pieces:
            uv = u + v
            if uv not in prefixes:
                continue
            for x in pieces:
                if uv + x in relation_words:
                    return None
    # TODO: as above, haven't checked minimality of decompositions
    return p


def equal_number_of_occurrences_of(p, x):
    # check 2-generator, 1-relation, alphabet {a,b}, x in {a,b}
    if not (
        len(p) == 3
        and presentation_alphabet(p) in ["ab", "ba"]
        and isinstance(x, str)
        and x in ["a", "b"]
    ):
        return None
    return p if p[1].count(x) == p[2].count(x) else None


def is_special(p):
    if not (len(p) == 3 and "" in presentation_relations_flat(p)):
        return None
    return p


def is_cycle_free_1_rel(p):
    return (
        p
        if (is_left_cycle_free(p) and is_right_cycle_free(p) and len(p) == 3)
        else None
    )


def is_monogenic(p):
    used_letters = set()
    for w in presentation_relations_flat(p):
        used_letters.update(set(w))
    return p if len(used_letters) == 1 else None


###############################################################################
### Miscellaneous proof steps
###############################################################################


# minimise 2-generated presentation under alphabet isomorphism and rule ordering
def minimise_2_generated_1_rel_presentation(p):
    assert len(presentation_alphabet(p)) == 2
    assert len(p) == 3

    p1 = alphabet_isomorphism(p, "ab")
    p2 = alphabet_isomorphism(p, "ba")

    rev_p1 = ("ab", p1[1][::-1], p1[2][::-1])
    rev_p2 = ("ab", p2[1][::-1], p2[2][::-1])

    p1_sorted_relation = tuple(sorted(presentation_relations_flat(p1)))
    p2_sorted_relation = tuple(sorted(presentation_relations_flat(p2)))
    rev_p1_sorted_relation = tuple(sorted(presentation_relations_flat(rev_p1)))
    rev_p2_sorted_relation = tuple(sorted(presentation_relations_flat(rev_p2)))

    return ("ab",) + min(
        [
            p1_sorted_relation,
            p2_sorted_relation,
            rev_p1_sorted_relation,
            rev_p2_sorted_relation,
        ]
    )


def _sort_presentation(p):
    sorted_alphabet = "".join(sorted(presentation_alphabet(p)))
    sorted_rules = sorted(tuple(sorted(rule) for rule in presentation_relations(p)))
    sorted_rules = tuple(y for x in sorted_rules for y in x)
    return (sorted_alphabet,) + sorted_rules


def normalize(p):
    return minimise_2_generated_1_rel_presentation(p)


# We're going to assume that we are checking all non-recursive proofs first within this run;
# no database information is used. We also assume that p is 2-generated.
def recursive(p):
    return p if normalize(p) in VERIFIED_DECIDABLE_PRESENTATIONS else None


def no_proof(p):
    return None


################################################################################
### Now the proof evaluator
################################################################################
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
    "is_cycle_free": is_cycle_free_1_rel,
    "recursive": recursive,
    "is_monogenic": is_monogenic,
    "no_proof": no_proof,
}


def _step_number(step):
    return step[0]


def _step_name(step):
    return step[1]


def _step_presentation(step):
    return step[2]


def _step_parameters(step):
    # the presentation is one of the parameters.
    return step[2:]


def is_valid_proof_step(step):
    if not (isinstance(step, tuple) and len(step) >= 3):
        return False
    name = _step_name(step)
    if not (isinstance(name, str) and name in _proof_step_to_function):
        return False
    func = _proof_step_to_function[name]
    # all elements except the first two (step number, function) should be function arguments
    if len(_step_parameters(step)) != len(inspect.signature(func).parameters):
        return False
    if not is_valid_presentation(_step_presentation(step)):
        return False
    return True


def proof_evaluator(proof):
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
        return False
    for step in proof:
        if not is_valid_proof_step(step):
            print(f"Invalid proof step: {step}")
            return False
    if proof[-1][1] not in decidable:
        return False

    step = proof[0]
    res = _proof_step_to_function[_step_name(step)](*_step_parameters(step))
    if res is None:
        print(f"Got None from step {step}")
        return False

    # 2. "run" the proof
    for i in range(1, len(proof)):
        step = proof[i]
        # make sure we're not trying to carry on after we've completed a proof
        if _step_name(step) in decidable and i != len(proof) - 1:
            print("Decidable seen before end of proof")
            return False
        # check that our proof joins up correctly
        if _sort_presentation(_step_presentation(step)) != _sort_presentation(res):
            print(f"Presentations not matching: {res}, {_step_presentation(step)}")
            print(f"Previous step was {proof[i-1]}")
            return False
        res = _proof_step_to_function[_step_name(step)](*_step_parameters(step))
        if res is None:
            print(f"Got None from step {step}")
            return False
    return True
