#import "../src/macros.typ": *
= Proved results

This section separates fully proved Lean results from assumptions or future work. In the final paper, each result should include a pointer to the Lean declaration and, when appropriate, a compressed proof sketch.

== Intermediate cardinal witness

#theorem[
  `exists_intermediate_cardinal`: assuming `ICAH.not_CH`, there exists a cardinal $kappa$ such that $aleph_0 < kappa < c$.
]

#remark[
  The witness is $aleph_1$. The proof uses `aleph0_lt_aleph_one`, `aleph_one_le_continuum`, and turns non-equality into strict inequality through `lt_of_le_of_ne`.
]

== Concrete synthetic stratum

#construction[
  `syntheticStratum` materializes an intermediate-cardinality subset of $RR$ by extracting a concrete set $S subset.eq RR$ with cardinality $aleph_1$ from a cardinal existence theorem.
]

This is the first bridge from a cardinal statement to an inhabited Lean structure. It turns the abstract existence of an intermediate cardinal into a concrete `Stratum` object.

== Subfield strata and size-aware fields

#theorem[
  `fieldOnSubfieldStratum`: every `SubfieldStratum` yields a `SizeAwareField` whose carrier and cardinal match the underlying stratum.
]

The technical point is that the carrier equality is treated as a propositional equality of subtypes, not merely a bijection. This is precisely what the `SizeAwareField.carrier` field requires.

== Real algebraic numbers as a base field

#theorem[
  `algReal_card_le_aleph0`: the real algebraic numbers, represented as `algebraicClosure QQ RR` inside $RR$, have cardinality at most $aleph_0$.
]

Together with the lower bound for infinite types, this supports the concrete base object `algRealSAF`, a countable size-aware field outside the intermediate-cardinality hierarchy.

== Definability of addition and multiplication

#theorem[
  `graphDefinable_add` and `graphDefinable_mul`: the graphs of addition and multiplication on $RR$ are first-order definable in the selected ring language with parameters.
]

These lemmas are technically demanding because the proof must build explicit bounded formulas and then verify realization through several layers of Mathlib's model-theory API.

== Elementarity-preserving composition

#theorem[
  `embLE`: for any $m <= n$, the chain induces an elementary embedding from level $m$ to level $n$.
]

#theorem[
  `embLE_eq_sysEmb`: the elementarity-preserving embedding built by recursive composition agrees as a function with the directed-system embedding used by `Language.DirectLimit`.
]

== Cardinality of the direct limit

#theorem[
  `directLimit_card`: if every level has cardinality below continuum and the supremum of the level cardinalities is continuum, then the direct limit has cardinality continuum.
]

The proof has two halves. The upper bound exhibits the direct limit as a quotient of the sigma type $sum_(n : NN) C_n$, bounding its cardinality by $aleph_0 dot c = c$. The lower bound uses injectivity of the canonical maps from each level into the direct limit and then takes the supremum over levels.

#contribution[
  For the paper, this is the strongest fully proved mathematical theorem to foreground. It is independent of the grand interpretation of ICAH and can be read as a reusable cardinal-arithmetic theorem for direct limits of countable chains.
]
