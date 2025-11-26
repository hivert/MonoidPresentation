# The SA certificate format

This document describes the SA certificate format stored in the 1-relation
monoid proof database. It was developed at the University of St Andrews by
R. Cirpons, J. D. Mitchell and F. Smith.

## Problem description

Many methods have been developed for solving specific instances of the word
problem for one relation monoids, see for example
["The Word Problem for One-relation Monoids: A Survey" by Carl-Fredrik Nyberg-Brodda][1]
for a recent survey. We have applied these methods as well as other general
purpose methods to solve the word problem in many small instances of one
relation monoids and would like to formally verify the correctness of our
results. To do so, we would either need to formally verify our implementations
or to record and verify the proofs produced by the methods.

Verifying programs is in general quite difficult and we would need to verify
many different pieces of code, many of which we did not write, coming from
several different languages. Hence we have opted to formally verify the proofs
themselves rather than the code producing them.

This document serves as the specification for proofs certifying the solvability
of word problems in certain one relation monoids.

[1]: https://arxiv.org/abs/2105.02853

## The specification

### Basic types

We assume the following basic types and type constructions.

- `None` - the empty or null type, it will usually indicate a failing proof.
- `str` - the string type. We only use double quote enclosed ASCII strings at
  the moment.
- `int` - an integer type. Should be able to handle arbitrarily large integers.
  At present integers are specified in proofs using their decimal notation.
- `tuple[T, ...]` - the homogeneous tuple type parametrized by `T`. Consists of
  all tuples whose entries are elements of the type `T`. We denote tuples by
  parentheses enclosed, comma delimited sequences of elements. The empty tuple is
  written as `()`, and the tuple consisting of a single element `x` is written as
  `(x,)`, note the comma after `x`.
- `tuple[T_1, T_2, ..., T_n]` - the heterogeneous tuple type. Consists of all
  tuples `(x_1, x_2, ..., x_n)` of length `n` such that each element `x_i` is a
  member of type `T_i`.
- `A | B` - the sum type of types `A` and `B`. Consists of all elements of
  either type `A` or type `B`.

We write `x: T` to specify that the variable `x` is a member of the type `T`.
When specifying a function `f` taking inputs `x_1, x_2, ..., x_n` of types
`T_1, T_2, ..., T_n` respectively and returning an output of type `U` we
will denote it by writing `f(x_1: T_1, x_2: T_2, ..., x_n: T_n) -> U`.
Elements of tuples are zero-indexed.
If `x: tuple[T, ...]` or `x: tuple[T_1, ..., T_n]`,
then we write `x[i]` to mean the `i`-th element of `x`,
where `i` is some non-negative integer. We write `len(x)` to mean the total
number of elements in the tuple `x`. The notation `range(a, b, k)` is shorthand
for the set of all integers of the form `a, a+k, a+2k, ..., a+nk` where `n` is
the largest non-negative integer such that `a+nk < b`. If no such integer
exists then `range(a, b, k)` is the empty set.

These definitions are all based on the corresponding Python types and Python
typing conventions, for more details see:

- [Python built-in type documentation](https://docs.python.org/3/library/stdtypes.html)
- [Python type system specification](https://typing.python.org/en/latest/spec/index.html)

### Presentation encoding

We assume monoid presentations $\langle A | R \rangle$ have an alphabet $A$
consisting of ASCII letters, so that every word over $A$ has a natural encoding
as an element of type `str`.

We think of the relations in $R$ as pairs of words, so that
$(u, v)\in R$ and $(v, u)\in R$ are distinct, and allow for trivial relations
of the form $(u, u)\in R$.

A monoid presentation $\langle A | R \rangle$ is encoded as a tuple `p` of
strings, i.e. an element `p: tuple[str, ...]`, as follows:

- The tuple `p` has precisely $|R|+1$ entries.
- The first entry `p[0]` of `p` encodes the alphabet.
  It is the string consisting of distinct letters in the alphabet $A$ of the
  presentation. The ordering of letters within this string is not important.
- The entries `p[i]` and `p[i + 1]` for `i` in `range(1, len(p), 2)` represent
  the `i`-th relation in the presentation. That is to say, if
  $R = \{(u_1, v_1), \ldots, (v_n, v_n)\}$, then `p[2*i-1]` encodes the word
  $u_i$ and `p[2*i]` encodes the word $v_i$.

Duplicate relations are not permitted in `p`. Otherwise the ordering or
relations may be arbitrary.

We write `Presentation` for the type consisting of all valid encodings of
presentations.

For example, `("ab", "bababa", "aba")` represents the monoid presentation:

$$ \langle a, b | bababa = aba \rangle.$$

And `("ba", "aaa", "", "bab", "a",)` represents the monoid
presentation

$$ \langle b, a | aaa = \varepsilon, bab = a \rangle,$$

### Rewriting system encoding

Let $R = \{u_1 \rightarrow v_1, \ldots, u_n\rightarrow v_n)\}$ be a string
rewriting system with alphabet $A$. We encode it in the same way as we would
the presentation $\langle A | u_1 = v_1, \ldots, u_n = v_n\rangle$.
We do not require every letter in $A$ to occur in some word of a rewrite rule
in $R$.

Our encoding scheme does make it ambiguous whether a tuple of strings encodes a
presentation or rewriting system, but this ambiguity is resolved by the needs
of the particular decidability criterion used.

We write `RewritingSystem` for the type consisting of all valid encodings of
rewriting systems.

So, for example, `("ab", "bababa", "aba")` represents the rewriting system:

$$ \{bababa \rightarrow aba\}. $$

And `("ba", "aaa", "", "bab", "a",)` represents the rewriting system

$$ \{aaa \rightarrow \varepsilon, bab \rightarrow a\}. $$

### Elementary sequence encoding

We will often be required to show that two words `s` and `t` are equal within
the monoid defined by a presentation `p`. The simplest way to do this is to
exhibit a sequence of elementary rewrites taking `s` into `t`.

Let `ElementaryRewrite` to be the type consisting of all elements of
`tuple[tuple[str, str, str], tuple[str, str, str]]` that satisfy the following
constraint. A 2-tuple `er` is an element of `ElementaryRewrite` if and only if
the entries of `er` can we written as:

- a 3-tuple `er[0] = (x, u, y)` where `x, u, y` are strings,
- a 3-tuple `er[1] = (x, v, y)` where `v` is a string and `x, y` are identical
  to the values in `er[0]`.

We think of the `er = ((x, u, y), (x, v, y))` as expressing that the word $xuy$
can be rewritten into $xvy$ in one step by using the relation $u = v$.
Clearly, if $u=v$ or $v=u$ is a relation of the presentation `p`, then it
follows that $xuy = xvy$ holds in the monoid presented by `p`.

Let `ElementarySequence` be the collection of all `tuple[ElementaryRewrite, ...]`
that satisfy the following constraint.
A tuple `es: tuple[ElementaryRewrite, ...]` is an element of
`ElementarySequence` if and only if
for each `i` in `range(0, len(s)-1)`,

- if `es[i][1] = (x, u, y)` and `es[i+1][0] = (z, v, t)` then $xuy=zvt$.

For example the rewriting sequence

```python
(
  (
    ("ba", "bab", "a"),
    ("ba", "a", "a")
  ),
  (
    ("b", "aaa", ""),
    ("b", "", "")
  )
)
```

shows that $bababa = b$ holds in the monoid defined by the presentation
`("ba", "bab", "a", "aaa", "")`. In equations its roughly equivalent to

$$ bababa = ba(bab)a = ba(a)a = b(aaa) = b(\varepsilon) = b.$$

---

### Proof format

A proof step is a heterogeneous tuple of arbitrary length
`proof_step`, such that

- `proof_step[0]: str` is the name of a function `step` to be called,
- `proof_step[1]: Presentation` is the input presentation tuple `p`,
- for `i` in `range(2, len(proof_step))`, `proof_step[i]` are any further arguments
  required for the function named `step`.

The signature of the function named `step` is
`step(p: tuple[str, ...], *args) -> tuple[str, ...] | None` where `p` is the
input presentation. We call the type of all valid proof steps `ProofStep`.

The proof of a solution to the word problem is encoded as a homogeneous tuple
`tuple[ProofStep, ...]` of tuples `ProofStep` encoding proof steps, such that the
following hold:

- if `(step1, p1, args1, ...)` and `(step2, p2, args2, ...)` are consecutive
  steps in a proof, then the output of `step1(p1, *args1)` must be the input
  presentation `p2` for the proof to be valid.
- an invalid step `step(p, *args)` should return `None`.

We write `Proof = tuple[ProofStep, ...]` for the type of all
proofs. We give examples of valid proofs later on.

### Proof step specification

There are two types of steps: transformations of the input presentation,
and decidability criteria. Roughly speaking, the first type modifies the
presentation in a way such that decidability of the word problem in the
original presentation can be inferred from decidability of the
transformed presentation. The decidability criteria just check the
decidability outright.

#### Transformations

- `tietze_add_generator(p: Presentation, letter: str, word: str) -> Presentation | None`  
   Add the generator `letter` to the presentation `p` and the relation
  `letter = word`. Return `None` if `letter` belongs to `p[0]` already.

  ```python
  >>> tietze_add_generator(("ab", "aab", "baa"), "c", "ab")
  ("abc", "aab", "baa", "c", "ab")
  >>> tietze_add_generator(("ab", "aab", "baa"), "b", "ab")
  None
  ```

- `tietze_rm_generator(p: Presentation, letter: str, word: str) -> Presentation | None`  
  Remove the generator `letter` from the presentation `p` and replace every
  occurrence by `word` provided that `letter = word` is a relation. Return
  `None` if `letter` is not in `p[0]` or `letter = word` is not a relation.

  ```python
  >>> tietze_rm_generator(("abc", "a", "bcb", "aab", "baa", "c", "ab"), "c", "ab")
  ("ab", "a", "babb", "aab", "baa")
  >>> tietze_rm_generator(("abc", "a", "bcb", "aab", "baa", "c", "ab"), "c", "bcb")
  ("bc", "bcbbcbb", "bbcbbcb", "c", "bcbb")
  >>> tietze_rm_generator(("abc", "a", "bcb", "aab", "baa", "c", "ab"), "b", "ccc")
  None
  >>> tietze_rm_generator(("abc", "a", "bcb", "aab", "baa", "c", "ab"), "a", "babb")
  None
  ```

- `tietze_add_relation(p: Presentation, lhs: str, rhs: str, e: ElementarySequence) -> Presentation | None`  
   Add the relation `lhs = rhs` to the presentation, where `e` is a proof that
  the relation holds in `p`.

  ```python
  >>> p = ("abc", "ab", "ba", "bc", "baa", "c", "cc")
  >>> e = (
    (("b", "cc", "a"), ("b", "c", "a")),
    (("", "bc", "a"), ("", "baa", "a")),
    (("", "ba", "aa"), ("", "ab", "aa")),
    (("a", "ba", "a"), ("a", "ab", "a")),
    (("aa", "ba", ""), ("aa", "ab", ""))
  )
  >>> tietze_add_relation(p, "bcca", "aaab", e)
  ("abc", "ab", "ba", "bc", "baa", "bcc", "aab")
  >>> e = ( # Invalid proof example
    (("b", "cc", "a"), ("b", "c", "a")),
    (("", "bc", "a"), ("", "baa", "a")),
    (("", "ba", "aa"), ("", "ab", "aa")),
    (("", "aba", "a"), ("", "aab", "a")), # No such rule in p
    (("aa", "ba", ""), ("aa", "ab", ""))
  )
  >>> tietze_add_relation(p, "bcca", "aaab", e)
  None
  >>> e = ( # Another invalid proof example
    (("b", "cc", "a"), ("b", "c", "a")),
    (("", "bc", "a"), ("", "baa", "a")),
    (("", "ba", "aa"), ("", "ab", "aa")),
    (("a", "ba", "a"), ("a", "ab", "a")) # Wrong final word
  )
  >>> tietze_add_relation(p, "bcca", "aaab", e)
  None
  ```

- `tietze_rm_relation(p: Presentation, lhs: str, rhs: str, e: ElementarySequence) -> Presentation | None`  
   Remove the relation `lhs = rhs` to the presentation, where `e` is a proof
  that `lhs = rhs` holds in the presentation `p` with relation `lhs = rhs`
  removed.

  ```python
  >>> p = ("abc", "ab", "ba", "bc", "baa", "c", "cc", "bcca", "aaab")
  >>> e = (
    (("b", "cc", "a"), ("b", "c", "a")),
    (("", "bc", "a"), ("", "baa", "a")),
    (("", "ba", "aa"), ("", "ab", "aa")),
    (("a", "ba", "a"), ("a", "ab", "a")),
    (("aa", "ba", ""), ("aa", "ab", ""))
  )
  >>> tietze_rm_relation(p, "bcca", "aaab", e)
  ("abc", "ab", "ba", "bc", "baa", "bcc", "aab")
  >>> e = ( # Invalid proof example
    (("b", "cc", "a"), ("b", "c", "a")),
    (("", "bc", "a"), ("", "baa", "a")),
    (("", "ba", "aa"), ("", "ab", "aa")),
    (("", "aba", "a"), ("", "aab", "a")), # No such rule in p
    (("aa", "ba", ""), ("aa", "ab", ""))
  )
  >>> tietze_rm_relation(p, "bcca", "aaab", e)
  None
  >>> e = ( # Another invalid proof example
    (("b", "cc", "a"), ("b", "c", "a")),
    (("", "bc", "a"), ("", "baa", "a")),
    (("", "ba", "aa"), ("", "ab", "aa")),
    (("a", "ba", "a"), ("a", "ab", "a")) # Wrong final word
  )
  >>> tietze_rm_relation(p, "bcca", "aaab", e)
  None
  >>> e = ( # A valid proof in p, but not with the relation removed
    (("", "bcca", ""), ("", "aaab", "")),
  )
  >>> tietze_rm_relation(p, "bcca", "aaab", e)
  None
  ```

- `strongly_compress(p: Presentation, morph: tuple[tuple[str, str]]) -> Presentation | None`  
  Perform strong compression on the one relation monoid `p`. Returns `None` if
  `p` does not define a one relation monoid. Otherwise let $C$ be the largest
  common prefix and $D$ be the longest common suffix of `p[1]` and `p[2]`. Let
  $k = \min(|C|, |D|) + 1$ and for each $k$-letter word $w$ over the alphabet
  `p[0]` define a new letter $e_w$. The compression function $\tau$ is then
  defined recursively by letting $\tau(w) = \varepsilon$ if $|w| < k$ and
  otherwise $\tau(w) = e_u \tau(w^\prime)$ where $u$ is the length $k$ prefix
  of $w$, and $w = aw^\prime$ for some letter $a$ and suffix $w^\prime$. The
  compressed presentation is then the presentation
  $\langle E \,|\, \tau(u) = \tau(v)\rangle$
  where `u = p[1]`, `v = p[2]` and $E$ consists of all letters $e_w$ where $w$
  is a length $k$ word over `p[0]`. The result is a left or right-cycle free
  presentation.

  The parameter `morph` is a tuple of pairs of strings. Each
  entry `morph[i]` must be a tuple with exactly two word entries. Each entry
  `morph[i][0]` must be a length `k` word over the alphabet `p[0]` and the
  corresponding entry `morph[i][1]` must be a single letter. The entries
  `morph[i][0]` and `morph[i][1]` must all be distinct.
  Furthermore for every length `k` subword
  `w` of `p[1]` or `p[2]` there must exist some `i` such that
  `morph[i][0] = w`. If any of these conditions on `morph` are not followed,
  then the function returns `None`.

  If `morph[i][0] = w` and
  `morph[i][1] = c` then we use the letter $c$ to represent $e_w$ in the
  compressed presentation. The
  final returned presentation will have alphabet consisting of entries
  `morph[i][1]` and the relation `x = y` where `x` is obtained by replacing
  each letter $e_w$ in $\tau(u)$ with the entry `morph[i][1]` where
  `morph[i][0] = w` and similarly for `y` and $\tau(v)$.

  ```python
  >>> p = ("ba", "aabba", "aabbaba")
  >>> morph = (
    ("aab", "a"),
    ("abb", "b"),
    ("bba", "c"),
    ("bab", "d"),
    ("aba", "e")
  )
  >>> strongly_compress(p, morph)
  ("abcde", "abc", "abcde")
  >>> morph = ( # Invalid morphism
    ("aab", "a"),
    ("abb", "b", "daa", "b"), # Wrong tuple size
    ("bba", "c"),
    ("bba", "d"), # Left hand sides must be unique
    ("bab", "e"),
    ("aba", "e") # Right hand sides must be unique
    ("abba", "f"), # Left hand sides don't have same length
  )
  >>> strongly_compress(p, morph)
  None
  >>> morph = ( # Invalid morphism
    ("aab", "a"),
    # Missing subword "abb"
    ("bba", "c"),
    ("bab", "d"),
    ("aba", "e")
  )
  >>> strongly_compress(p, morph)
  None
  ```

- `reduce_to_2_generators(p: Presentation, morph: str) -> Presentation | None`  
  Given a one relation monoid, reduce the number of generators to 2. Here `p`
  must be a length 3 presentation tuple defining a one relation monoid where
  `p[0]` has at least 2 elements and `p` must be left cycle free, otherwise
  the function returns `None`. Replaces the letter `p[0][i]` by `morph[i]` in
  every relation word of `p`. `morph` must have the same length as `p[0]` and
  must contain exactly two distinct letters, otherwise the function returns
  `None`. Furthermore, `morph` must map the letters `p[1][0]` and `p[2][0]` to
  distinct letters, and every other letter of `p[0]` must map to the same
  value as either `p[1][0]` or `p[2][0]`. Finally, we also require that one of
  the letters in `morph` appears exactly once in `morph`.

  ```python
  >>> p = ("abcd", "dcbcccaa", "acbdbc")
  >>> reduce_to_2_generators(p, "baaa")
  ("ba", "aaaaaabb", "baaaaa")
  >>> reduce_to_2_generators(p, "bccc")
  ("bc", "ccccccbb", "bccccc")
  >>> reduce_to_2_generators(p, "bbba")
  ("ab", "ababbbbb", "bbbabb")
  >> # First letter of each relation word must map to distinct letters
  >>> reduce_to_2_generators(p, "aaba")
  None
  >>> reduce_to_2_generators(p, "baba") # One letter must appear exactly once
  None
  >>> reduce_to_2_generators(p, "babc") # Exactly two letter must appear
  None
  >>> reduce_to_2_generators(p, "aaaa") # Exactly two letter must appear
  None
  ```

- `reverse(p: Presentation) -> Presentation`  
  Reverse every relation word in `p`.

  ```python
  >>> reverse(("ab", "abb", "babba", "aab", "bab"))
  ("ab", "bba", "abbab", "baa", "bab")
  ```

- `alphabet_isomorphism(p: Presentation, morph: str) -> Presentation | None`  
  Construct an isomorphic presentation by replacing letters in the alphabet.
  Replaces the letter `p[0][i]` by `morph[i]` in every relation word of `p`.
  `morph` must have the same length as `p[0]` and must not contain duplicate
  entries, otherwise the function returns `None`.

  ```python
  >>> p = ("abc", "ab", "bcb", "cb", "aa")
  >>> alphabet_isomorphism(p, "bad")
  ("bad", "ba", "ada", "da", "bb")
  >>> alphabet_isomorphism(p, "bdd") # Letters in morph must be distinct
  None
  >>> alphabet_isomorphism(p, "badc") # More letters than in alphabet
  None
  >>> alphabet_isomorphism(p, "ba") # Fewer letters than in alphabet
  None
  ```

#### Decidable word problem checks

- `is_complete_rws(p: Presentation, termination_method: str, termination_certificate: str) -> Presentation | None`  
  Check if the underlying rewriting system of `p` (as described in the section on rewriting system encodings)
  is locally confluent and terminating. Termination of `p`
  is exhibited using `termination_method` and `termination_certificate`. For
  more info see the `Termination checking` section.

  ```python
  >>> is_complete_rws(("ab", "ab", "ba", "baa", "a"), "lenlex", "ba")
  ("ab", "ab", "ba", "baa", "a")
  >>> # Cant use ordering a < b as the rule ab -> ba does not respect it
  >>> is_complete_rws(("ab", "ab", "ba", "baa", "a"), "lenlex", "ab")
  None
  ```

- `is_complete_adian_rws(p: Presentation, adian_rws: RewritingSystem, 
translation: tuple[tuple[Tuple[str, str] | str, str]],
termination_method: str,
termination_certificate: str) -> Presentation | None`  
   **Mathematical background**:
  Let $P = \langle A \,|\, R\rangle$ be a presentation and enumerate $R$ as $R
  = \{(p_1, p_2), (p_3, p_4), \ldots, (p_{2n-1}, p_{2n})\}$. We say that $P$ is
  left-cycle free if the initial letter of $p_{2i - 1}$ differs from the initial
  letter of $p_{2i}$ for all $(p_{2i - 1}, p_{2i})\in R$. Define the left-graph
  of $P$ to be the graph $\mathcal{L}(P)$ with vertex set $V(\mathcal{L}(P)) =
  A$ the alphabet of $P$ and an edge between vertices $a$ and $b$ if there is a
  relation $(p_{2i-1}, p_{2i}) \in R$ such that $a$ is the initial letter of
  $p_{2i-1}$ and $b$ of $p_{2i}$ or vice-versa. Note that in a left-cycle free
  presentation the associated left-graph $\mathcal{L}(P)$ is acyclic.

  Let $P$ be a left cycle free presentation and define a new alphabet $Q$ with
  letters $q_{(x, y)}$ for all words $x, y\in A^\ast$. Adian's rewriting system
  $\mathcal{A}$ is the rewriting system with underlying alphabet a subset of
  $Q\cup A$ and the following rules:
  - a rule $q_{(a, a)} \rightarrow a$ for all $a \in A$,
  - for every pair of distinct letters $a\neq e\in A$ that are connected in
    $\mathcal{L}(P)$, let $e$ be the letter adjacent to $a$ on the unique path
    from $a$ to $d$ (the path is unique since $\mathcal{L}(P)$ is acyclic).
    Then there exists a relation $(u, v)\in R$ such that $a$ is the first
    letter of $u$ and $e$ is the first letter of $v$ or vice-versa. Without
    loss of generality lets assume that a is the first letter of $u$ and $e$
    the first letter of $v$. Then we have:
    - a rule $q_{(a, \gamma)} b \rightarrow q_{(a, \gamma b)}$ for every proper
      prefix $\gamma$ of $v$ where $b\in A$ is the unique letter such that
      $\gamma b$ is also a prefix of $v$,
    - a rule $q_{(a, \gamma)} c \rightarrow q_{(a, \gamma)}q_{(b, c)}$ for
      every proper prefix $\gamma$ of $v$ and letter $c\neq b \in A$ where $b$
      is the same as in the previous point.
    - a rule $q_{(a, u)} \rightarrow q_{(a, e)} v^\prime$ where $v^\prime$ is
      such that $ev^\prime = v$.

  Note that $\mathcal{A}$ has only finitely many rules. It can be shown
  that the termination of Adian's rewriting system implies the solvability
  of the left divisibility problem in $P$ and hence the word problem.

  For slightly more details see

  > "Off with the head: termination provers and the word problem for 1-relation monoids",
  > R. Cirpons, J. D. Mitchell, F. Smith,
  > In: Proceedings of the 20th International Workshop on Termination

  **Function specification**: If the input presentation `p` is not
  left-cycle free then return `None`. Each tuple `translation[i]` must have
  length 2 and be such that `translation[i][0]` is either a pair of strings
  or a single letter and `translation[i][1]` is a single letter. All entries
  `translation[i][0]` must be distinct. All entries `translation[i][1]` must
  also be distinct. Furthermore, each letter of `adian_rws[0]` must occur as
  `translation[i][1]` for some `i`. If `translation` violates any of these
  properties, return `None`.

  Otherwise, interpret `adian_rws` as a rewriting system in the manner as
  described in the section `Presentation format`. Construct the Adian rewriting
  system $\mathcal{A}$ for `p` and transform it into a new rewriting system
  $\mathcal{A}^\prime$ by remapping its underlying alphabet in the following
  manner. Map each $a\in A$ to `translations[i][1]` where `i` is such that
  `translations[i][0] = a`, if no such `i` exists then return `None`. For every
  letter $q_(x, y)$ that appears in $\mathcal{A}$ map it to
  `translations[i][1]` where `i` is such that `translations[i][0] = (x, y)`, if
  no such `i` exists then return `None`.

  Once constructed check that $\mathcal{A}^\prime$ is equal (as a rewriting
  system) to the rewriting system `adian_rws`. If not then return `None`.
  Otherwise check that `adian_rws` is terminating using `termination_method`
  and `termination_certificate` as described in the specification of
  `is_complete_rws`. If `adian_rws` is terminating return `p`, otherwise return
  `None`.

- `is_watier1(p: Presentation) -> Presentation | None`  
  If `p` is of the form `bua = ava` and the initial sequence of
  `"b"`s in `p[1]` is longer than any subsequent sequence of `"b"`s in `p[1]`,
  then `p` is returned, otherwise `None` is returned.

  ```python
  >>> is_watier1(("ab", "bbbbbabbaaabbaba", "aababaaaababbbba"))
  ("ab", "bbbbbabbaaabbaba", "aababaaaababbbba")
  >>> is_watier1(("ab", "aababaaaababbbba", "bbbbbabbaaabbaba"))
  ("ab", "aababaaaababbbba", "bbbbbabbaaabbaba")
  >>> is_watier1(("ab", "ab", "ba", "baa", "a")) # Too many relations
  None
  >>> is_watier1(("ab", "abbbaba", "ababba")) # Not bua = ava
  None
  >>> is_watier1(("ab", "abbab", "bbbabb")) # Not bua = ava
  None
  ```

- `is_c4_monoid(p: Presentation, d: tuple[tuple[str, ...], ...]) -> Presentation | None`  
  **Mathematical background**:
  We call a word $w$ a piece if it occurs as a subword of two distinct relation
  words, or if it occurs as a subword in two distinct locations of a single
  relation word. A tuple $t = (w_1, w_2, \ldots, w_n)$ is a decomposition of the
  relation word $u$ if each $w_i$ is a piece and furthermore
  $u=w_1w_2\cdots w_n$. A decomposition is minimal if it contains the least
  possible amount of pieces. A presentation has the $C(n)$ property if each of
  its relation words has a minimal decomposition with at least $n$ pieces.

  **Function specification**:
  Returns `p` if the tuple `d` is such that `d[i]` is a minimal length
  decomposition of `p[i + 1]` into its pieces, and `len(d[i]) > 3` for every
  `i`.

- `is_c3_monoid(p: Presentation, d: Tuple[Tuple[str, ...], ...]) -> Presentation | None`  
  Returns `p` if `p` is 1-relation, the tuple `d` is such that `d[i]` is a
  minimal length
  decomposition of `p[i + 1]` into its pieces, and `len(d[i]) > 3` for every
  `i`.
  See the specification of `is_c4_monoid` for mathematical background.

- `equal_number_of_occurrences_of(p: Tuple[str], x: str):`  
  Returns `p` if `len(p) = 3`, `p[0] in ["ab", "ba"]` and
  `x in ["a", "b"]` and there are an
  equal number of occurrence of the letter `x` on both sides of every relation
  in `p`, and `None` otherwise.

  ```python
  >>> equal_number_of_occurrences_of(("ab", "baaabaa", "aabba"), "b")
  ("ab", "baaabaa", "aabba")
  >>> # The letter "a" is not preserved
  >>> equal_number_of_occurrences_of(("ab", "baaabaa", "aabba"), "a")
  None
  >>> # Wrong alphabet
  >>> equal_number_of_occurrences_of(("abc", "cbaaabaa", "aabba"), "b")
  None
  >>> # Wrong alphabet
  >>> equal_number_of_occurrences_of(("bc", "bcccbcc", "ccbbc"), "b")
  None
  >>> # Invalid letter
  >>> equal_number_of_occurrences_of(("ab", "baaabaa", "aabba"), "c")
  None
  >>> # Not 1-relation
  >>> equal_number_of_occurrences_of(("ab", "baaabaa", "aabba", "ba", "ab"), "b")
  None
  ```

- `is_special(p: Presentation) -> Presentation | None`  
  Returns `p` if the presentation `p` is a 1-relation
  monoid presentation, and one of the relation words is empty, and `None` if
  not.

  ```python
  >>> is_special(("ab", "baaabaa", ""))
  ("ab", "baaabaa", "")
  >>> is_special(("ab", "", "baaabaa"))
  ("ab", "", "baaabaa")
  >>> is_special(("abc", "baaaccbaac", ""))
  ("abc", "baaaccbaac", "")
  >>> is_special(("ab", "", "baaabaa", "abaa", "")) # Not 1-relation
  None
  >>> is_special(("ab", "aab", "baaabaa")) # Neither relation word empty
  None
  ```

- `is_cycle_free(p: Presentation) -> Presentation | None`  
  Returns `p` if the presentation `p` is 1-relation and both
  left and right cycle free, i.e.
  for every relation `u=v` in `p`, the initial and terminal letters of `u`
  each differ from respectively the initial and terminal letters of `v`.
  If any relation word is empty, or if `p` is not cycle free then
  returns `None`.

  ```python
  >>> is_cycle_free(("ab", "baaabaa", "abbbbab"))
  ("ab", "baaabaa", "abbbbab")
  >>> is_cycle_free(("ab", "baaabaab", "abbbbaba"))
  ("ab", "baaabaab", "abbbbaba")
  >>> is_cycle_free(("abc", "baaabaac", "abbbbaba"))
  ("ab", "baaabaac", "abbbbaba")
  >>> is_cycle_free(("ab", "aba", "b"))
  ("ab", "aba", "b")
  >>> # Not 1-relation
  >>> is_cycle_free(("ab", "baaabaab", "abbbbaba", "aba", "b"))
  None
  >>> # Not right cycle free
  >>> is_cycle_free(("ab", "baaaba", "abbbba"))
  None
  >>> # Empty word is a relation word
  >>> is_cycle_free(("ab", "", "abbbba"))
  None
  ```

- `is_monogenic(p: Presentation) -> Presentation | None`  
  Returns `p` if the presentation `p` is monogenic, i.e. every relation word
  is a power of the same generator, otherwise returns `None`.

  ```python
  >>> is_monogenic(("ab", "aaaa", "a", "aaaaa", "", "aa", "aaa"))
  ("ab", "aaaa", "a", "aaaaa", "", "aa", "aaa")
  >>> is_monogenic(("ab", "bbaa", "a", "aaaaa", ""))
  None
  ```

#### Misc proof steps

- `recursive(p: Presentation) -> Presentation | None`  
  Returns `p` if presentation `p` has a proof in some proof entry in the
  database. See the section on the database schema for more details.
- `no_proof(p: Presentation) -> None`  
  Always returns `None` independent of presentation. Indicates that the
  presentation `p` does not yet have a proof.

### Termination checking

In order to check termination of rewriting systems, the following methods are available:

- `lenlex`  
  Verifies that the rewriting system is lenlex-reducing. The certificate is a
  string describing the ordering of the alphabet. For example `"abc"` denotes the
  ordering `a < b < c`.
- `cpf`  
  Verifies that the rewriting system terminates by providing a
  [CPF](http://cl-informatik.uibk.ac.at/software/cpf/) format proof.
  The certificate is the associated CPF xml represented as a string.

### Valid step ordering

Any sequence of the `Transformation` steps:

```
(tietze_add_generator, *)
(tietze_rm_generator, *)
(tietze_add_relation, *)
(tietze_rm_relation, *)
(strongly_compress, *)
(reduce_to_2_generators, *)
(reverse, *)
```

followed by a single `Decidable word problem check` step:

```
(is_watier1, *)
(is_complete_rws, *)
(is_c4_monoid, *)
(is_c3_monoid, *)
(equal_number_of_occurrences_of, *)
(is_special, *)
```

### Proof validation

Given a proposed `proof` that a 1-relation monoid presentation such as:
`("ba", "aabbaabbab", "aaabbbaab")`
the proof might look like:

```python
( ("alphabet_isomorphism",
    ("ba", "aabbaabbab", "aaabbbaab"),
    "ab"),
  ("reverse",
    ("ab", "bbaabbaaba", "bbbaaabba")),
  ("strongly_compress",
    ("ab", "abbaaabbb", "abaabbaabb"),
    ( ("abb", "a"),
      ("bba", "b"),
      ("baa", "c"),
      ("aaa", "d"),
      ("aab", "e"),
      ("bbb", "f"),
      ("aba", "g"))),
  ("reduce_to_2_generators",
    ("abcdefg", "abcdeaf", "gceabcea"),
    "abbbbbb"),
  ("is_cycle_free",
    ("ab", "abbbbab", "bbbabbba")))
```

The `proof_evaluator` function checks:

1. That the steps in the proof (if correct) are a valid proof that the word
   problem is solvable in the input presentation.
2. for each step, the corresponding function is called, and the output compared
   with the first argument for the next step, and so on.

If any of this fails, then `False` is returned, otherwise `True` is returned
and `proof` is considered valid. A Python mock-up of such a function, modulo
the correct implementation of the proof step functions is given below:

```python
def proof_evaluator(proof):

    transformations = (
        tietze_add_generator,
        tietze_rm_generator,
        tietze_add_relation,
        tietze_rm_relation,
        strongly_compress,
        reduce_to_2_generators,
        reverse,
    )

    decidable = (
        is_watier1,
        is_complete_rws,
        is_c4_monoid,
        is_c3_monoid,
        equal_number_of_occurrences_of,
        is_special,
    )

    # 1. check that "proof" is a valid sequence of steps
    if len(proof) == 0:
        return False

    last_step = None
    for i, step in enumerate(proof):
        if not step[0] in transformations:
            last_step = i
            break
    if last_step != len(proof) - 1 or not step[0] in decidable:
        return False

    # 2. "run" the proof
    prev_output = proof[0][1]
    for step in proof:
        if prev_output != step[1]:
            return False
        prev_output = step[0](step[1], *step[2:])
    return True
```

**Note**: In the proof database proofs steps also store the index of the step
in the proof as the first entry. Additionally, the outer braces are square
braces instead of round braces. So, the SA certificate stored in the database would
look something like:

```python
[
  (0, "alphabet_isomorphism",
    ("ba", "aabbaabbab", "aaabbbaab"),
    "ab"),
  (1, "reverse",
    ("ab", "bbaabbaaba", "bbbaaabba")),
  (2, "strongly_compress",
    ("ab", "abbaaabbb", "abaabbaabb"),
    ( ("abb", "a"),
      ("bba", "b"),
      ("baa", "c"),
      ("aaa", "d"),
      ("aab", "e"),
      ("bbb", "f"),
      ("aba", "g"))),
  (3, "reduce_to_2_generators",
    ("abcdefg", "abcdeaf", "gceabcea"),
    "abbbbbb"),
  (4, "is_cycle_free",
    ("ab", "abbbbab", "bbbabbba"))
]
```
