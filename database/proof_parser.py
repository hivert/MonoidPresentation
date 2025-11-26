"""
(c) Copyright 2025 Reinis Cirpons.
Distributed under the terms of CeCILL-B.

A library file for parsing SA certificate proof tuples into structured form.
The SA certificate specification is available in the "SA_certificate_format.md"
file.
"""

from dataclasses import dataclass
from typing import NamedTuple, ClassVar, Generic, TypeVar, Union
from collections.abc import Iterable
from ast import literal_eval


def _validate_args_simple(
    arg_types: tuple[Union[type, None], ...],
    args: tuple,
    wrong_number_args_message: str = "Wrong number of arguments!",
    wrong_arg_type_message: str = "Wrong argument type!",
):
    if len(args) != len(arg_types):
        raise ValueError(
            f"{wrong_number_args_message} Expected {len(arg_types)}, but got {len(args)}."
        )
    for arg, t in zip(args, arg_types):
        if t is None:
            continue
        if not isinstance(arg, t):
            raise TypeError(
                f"{wrong_arg_type_message} Expected {arg} to have type {t}, but got {type(arg)}."
            )


class MatchedWord(NamedTuple):
    prefix: str
    match: str
    suffix: str

    @property
    def word(self) -> str:
        return self.prefix + self.match + self.suffix


@dataclass
class ElementaryRewrite:
    lhs: MatchedWord
    rhs: MatchedWord

    def __init__(self, lhs: tuple[str, str, str], rhs: tuple[str, str, str]):
        if lhs[0] != rhs[0]:
            raise ValueError(
                f"The prefix of a the lhs must equal the prefix of the rhs "
                f"in an ElementaryRewrite, initialized from {(lhs, rhs)}"
            )
        if lhs[2] != rhs[2]:
            raise ValueError(
                f"The suffix of a the lhs must equal the suffix of the rhs "
                f"in an ElementaryRewrite, initialized from {(lhs, rhs)}"
            )
        self.lhs = MatchedWord(*lhs)
        self.rhs = MatchedWord(*rhs)


@dataclass
class Presentation:
    gens: str
    relations: tuple[tuple[str, str], ...]

    def __init__(self, gens: str, *relation_words: str):
        if len(relation_words) % 2 != 0:
            raise ValueError(
                f"Invalid presentation gens={gens}, relation_words={relation_words}! "
                f"Length of relations not even."
            )
        for w in (gens,) + relation_words:
            if not isinstance(w, str):
                raise ValueError(
                    f"Invalid presentation gens={gens}, relation_words={relation_words}! "
                    f"Entries not all strings."
                )
        self.gens = gens
        self.relations = tuple(
            (relation_words[i], relation_words[i + 1])
            for i in range(0, len(relation_words), 2)
        )

    def flatten(self) -> tuple[str, ...]:
        return (self.gens,) + tuple(
            relation_word for relation in self.relations for relation_word in relation
        )


T = TypeVar("T")


@dataclass
class ProofStep(Generic[T]):
    args_type: ClassVar[type] = tuple
    step: ClassVar[Union[str, None]] = None
    current_presentation: Presentation
    number: int
    args: T

    def __init__(self, *proof_step_tuple):
        if len(proof_step_tuple) < 3:
            raise ValueError(
                f"Malformed proof step tuple {proof_step_tuple}! "
                f"Expected length >= 3, but got {len(proof_step_tuple)}!"
            )

        number = proof_step_tuple[0]
        step = proof_step_tuple[1]
        current_presentation = proof_step_tuple[2]
        args = proof_step_tuple[3:]

        if not (isinstance(number, int)):
            raise TypeError(
                f"Invalid proof step {proof_step_tuple}! "
                f"The first component {number} is not an int."
            )
        if not (isinstance(step, str)):
            raise TypeError(
                f"Invalid proof step {proof_step_tuple}! "
                f"The second component {step} is not a str."
            )
        if not (isinstance(current_presentation, tuple)):
            raise TypeError(
                f"Invalid proof step {proof_step_tuple}! "
                f"The second component {current_presentation} is not a tuple."
            )

        if self.step is not None and self.step != step:
            raise ValueError(f"Wrong step type, expected {self.step}, but got {step}!")

        self.number = number
        self.current_presentation = Presentation(*current_presentation)
        self.initialize_args(args)

    def initialize_args(self, args: tuple):
        self.args = self.args_type(args)  # Different here because of how tuple works


class _ArgsTietzeXGenerator(NamedTuple):
    letter: str
    word: str


class _ProofStepTietzeXGenerator(ProofStep[_ArgsTietzeXGenerator]):
    step = "tietze_add_generator"
    args_type = _ArgsTietzeXGenerator

    def initialize_args(self, args: tuple[str, str]):
        _validate_args_simple((str, str), args)
        if not len(args[0]) == 1:
            raise ValueError(
                f"Wrong first argument, expected word of length 1, but got {args[0]}"
            )
        self.args = self.args_type(*args)


class ProofStepTietzeAddGenerator(_ProofStepTietzeXGenerator):
    step = "tietze_add_generator"


class ProofStepTietzeRmGenerator(_ProofStepTietzeXGenerator):
    step = "tietze_rm_generator"


class _ArgsTietzeXRelation(NamedTuple):
    lhs: str
    rhs: str
    elementary_sequence: tuple[ElementaryRewrite, ...]


class _ProofStepTietzeXRelation(ProofStep[_ArgsTietzeXRelation]):
    args_type = _ArgsTietzeXRelation

    def initialize_args(self, args: tuple):
        _validate_args_simple((str, str, tuple), args)
        self.args = self.args_type(
            lhs=args[0],
            rhs=args[1],
            elementary_sequence=tuple(
                ElementaryRewrite(*elementary_rewrite) for elementary_rewrite in args[2]
            ),
        )


class ProofStepTietzeAddRelation(_ProofStepTietzeXRelation):
    step = "tietze_add_relation"


class ProofStepTietzeRmRelation(_ProofStepTietzeXRelation):
    step = "tietze_rm_relation"


class WordMorphism:
    def apply(self, word: str, presentation: Presentation) -> str:
        raise NotImplementedError()


class StrongCompressionMorphism(tuple[tuple[str, str], ...], WordMorphism):
    @property
    def compression_length(self) -> int:
        assert len(self) > 0 and len(self[0]) > 0
        return len(self[0][0])

    def apply(self, word: str, presentation: Presentation) -> str:
        k = self.compression_length
        if len(word) < k:
            return ""
        f = {lhs: rhs for lhs, rhs in self}
        result = []
        for i in range(len(word) - k + 1):
            part = word[i : i + k]
            if part not in f:
                raise ValueError(
                    f"Morphism {self} not defined for part {part} of word {word}!"
                )
            result.append(f[part])
        return "".join(result)


class _ArgsStronglyCompress(NamedTuple):
    morphism: StrongCompressionMorphism


class ProofStepStronglyCompress(ProofStep[_ArgsStronglyCompress]):
    args_type = _ArgsStronglyCompress
    step = "strongly_compress"

    def initialize_args(self, args: tuple):
        _validate_args_simple((tuple,), args)
        k = None
        for entry in args[0]:
            _validate_args_simple(
                (str, str),
                entry,
                wrong_number_args_message="Each morphism entry must be a pair!",
                wrong_arg_type_message="Each morphism pair entry must be a string!",
            )
            if len(entry[1]) != 1:
                raise ValueError(
                    f"The strong compression morphism must map words to letters! "
                    f"But entry {entry} of {args[0]} does not represent a mapping to a letter."
                )
            if k is not None and k != len(entry[0]):
                raise ValueError(
                    f"The strong compression morphism must be defined on words of the same length! "
                    f"But this is not the case for {args[0]}."
                )
            k = len(entry[0])
        self.args = self.args_type(morphism=StrongCompressionMorphism(args[0]))


class AlphabetInducedMorphism(str, WordMorphism):
    def apply(self, word: str, presentation: Presentation) -> str:
        if len(self) != len(presentation.gens):
            raise ValueError(
                f"Can't apply morphism, expected presentation "
                f"to have {len(self)} gens, but got {len(presentation.gens)}!"
            )
        f = {lhs: rhs for lhs, rhs in zip(presentation.gens, self)}
        return "".join(f[letter] for letter in word)


class _ArgsAlphabetInducedMorphism(NamedTuple):
    morphism: AlphabetInducedMorphism


class _ProofStepAlphabetInducedMorphism(ProofStep[_ArgsAlphabetInducedMorphism]):
    args_type = _ArgsAlphabetInducedMorphism

    def initialize_args(self, args: tuple):
        _validate_args_simple((str,), args)
        if not len(args[0]) == len(self.current_presentation.gens):
            raise ValueError(
                f"Argument does not represent a morphism of the given alphabet! "
                f"Presentation alphabet has length {len(self.current_presentation.gens)}, but morphism string has length {len(args[0])}"
            )
        self.args = self.args_type(morphism=AlphabetInducedMorphism(args[0]))


class ProofStepReduceTo2Generators(_ProofStepAlphabetInducedMorphism):
    step = "reduce_to_2_generators"


class _ProofStepNoArgs(ProofStep[tuple[()]]):
    args_type = tuple[()]

    def initialize_args(self, args: tuple):
        _validate_args_simple((), args)
        self.args = ()


class ProofStepReverse(_ProofStepNoArgs):
    step = "reverse"


class ProofStepAlphabetIsomorphism(_ProofStepAlphabetInducedMorphism):
    step = "alphabet_isomorphism"


class _ArgsIsCompleteRws(NamedTuple):
    termination_method: str
    termination_certificate: str


class ProofStepIsCompleteRws(ProofStep[_ArgsIsCompleteRws]):
    args_type = _ArgsIsCompleteRws
    step = "is_complete_rws"

    def initialize_args(self, args: tuple):
        _validate_args_simple((str, str), args)
        termination_method = args[0]
        termination_certificate = args[1]
        available_methods = {"lenlex", "cpf"}
        if termination_method not in available_methods:
            raise ValueError(
                f"Unsupported termination method {termination_method}. "
                f"Expected method in {available_methods}."
            )
        if termination_method == "lenlex" and sorted(
            self.current_presentation.gens
        ) != sorted(termination_certificate):
            mess = "<".join(termination_certificate)
            raise ValueError(
                f"Provided lenlex ordering {mess} "
                f"is not valid for given presentation {self.current_presentation}."
            )
        self.args = self.args_type(
            termination_method=termination_method,
            termination_certificate=termination_certificate,
        )


class Factorization(tuple[str, ...]):
    @property
    def word(self):
        return "".join(self)


class _ArgsSmallOverlap(NamedTuple):
    factorizations: tuple[Factorization, ...]


class _ProofStepSmallOverlap(ProofStep[_ArgsSmallOverlap]):
    args_type = _ArgsSmallOverlap

    def initialize_args(self, args: tuple):
        _validate_args_simple((tuple,), args)
        for factorization in args[0]:
            if not isinstance(factorization, tuple):
                raise ValueError(
                    f"The factorization {factorization} must be a tuple! "
                    f"But got {type(factorization)}."
                )
            for word in factorization:
                if not isinstance(factorization, tuple):
                    raise ValueError(
                        f"The factorization {factorization} must consist of words! "
                        f"But it contains {type(word)}."
                    )

        self.args = self.args_type(
            factorizations=tuple(
                Factorization(factorization) for factorization in args[0]
            )
        )


class ProofStepIsC4Monoid(_ProofStepSmallOverlap):
    step = "is_c4_monoid"


class ProofStepIsC3Monoid(_ProofStepSmallOverlap):
    step = "is_c3_monoid"


class _ArgsEqualNumberOfOccurrencesOf(NamedTuple):
    letter: str


class ProofStepEqualNumberOfOccurrencesOf(ProofStep[_ArgsEqualNumberOfOccurrencesOf]):
    args_type = _ArgsEqualNumberOfOccurrencesOf
    step = "equal_number_of_occurrences_of"

    def initialize_args(self, args: tuple):
        _validate_args_simple((str,), args)
        if len(args[0]) != 1:
            raise ValueError(f"Argument must be letter of length 1, but got {args[0]}.")
        self.args = self.args_type(letter=args[0])


class ProofStepIsWatier1(_ProofStepNoArgs):
    step = "is_watier1"


class ProofStepIsSpecial(_ProofStepNoArgs):
    step = "is_special"


class ProofStepIsCycleFree(_ProofStepNoArgs):
    step = "is_cycle_free"


class ProofStepIsMonogenic(_ProofStepNoArgs):
    step = "is_monogenic"


class ProofStepFlipAllRelations(_ProofStepNoArgs):
    step = "flip_all_relations"


class ProofStepReorderAlphabet(_ProofStepNoArgs):
    step = "reorder_alphabet"


class ProofStepRecursive(_ProofStepNoArgs):
    step = "recursive"


class ProofStepNoProof(_ProofStepNoArgs):
    step = "no_proof"


_step_to_class: dict[str, type[ProofStep]] = {
    "tietze_add_generator": ProofStepTietzeAddGenerator,
    "tietze_rm_generator": ProofStepTietzeRmGenerator,
    "tietze_add_relation": ProofStepTietzeAddRelation,
    "tietze_rm_relation": ProofStepTietzeRmRelation,
    "strongly_compress": ProofStepStronglyCompress,
    "reduce_to_2_generators": ProofStepReduceTo2Generators,
    "reverse": ProofStepReverse,
    "alphabet_isomorphism": ProofStepAlphabetIsomorphism,
    "is_complete_rws": ProofStepIsCompleteRws,
    "is_c4_monoid": ProofStepIsC4Monoid,
    "is_c3_monoid": ProofStepIsC3Monoid,
    "equal_number_of_occurrences_of": ProofStepEqualNumberOfOccurrencesOf,
    "is_watier1": ProofStepIsWatier1,
    "is_special": ProofStepIsSpecial,
    "is_cycle_free": ProofStepIsCycleFree,
    "is_monogenic": ProofStepIsMonogenic,
    "flip_all_relations": ProofStepFlipAllRelations,
    "reorder_alphabet": ProofStepReorderAlphabet,
    "recursive": ProofStepRecursive,
    "no_proof": ProofStepNoProof,
}


def parse_proof_tuple(proof_tuple: tuple) -> tuple[ProofStep]:
    result = []
    for proof_step_tuple in proof_tuple:
        if len(proof_step_tuple) < 2 or not isinstance(proof_step_tuple[1], str):
            raise ValueError(f"Malformed proof step tuple {proof_step_tuple}!")
        step = proof_step_tuple[1]
        if step not in _step_to_class:
            raise NotImplementedError(f"Parsing of {step} not implemented!")
        result.append(_step_to_class[step](*proof_step_tuple))
    return tuple(result)


def parse_proof_string(proof_string: str) -> tuple[ProofStep]:
    return parse_proof_tuple(literal_eval(proof_string))
