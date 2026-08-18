#import "../src/macros.typ": *
= Proved results

This section separates fully proved Lean results from hypotheses. Section 8 contains the complete declaration-to-paper mapping table; Section 5 records, for each result, which of the two named hypotheses (if any) it consumes.

== Intermediate cardinal witness

#theorem[
  `exists_intermediate_cardinal`: assuming the hypothesis `NotCH`, there exists a cardinal $kappa$ such that $aleph_0 < kappa < c$.
]

#remark[
  The witness is $aleph_1$. The proof uses `aleph0_lt_aleph_one`, `aleph_one_le_continuum`, and turns non-equality into strict inequality (`aleph_one_lt_continuum_of_notCH`).
]

== Elementary substrata via downward Löwenheim–Skolem (Pillar A)

#theorem[
  `exists_elementary_substratum_extending` (ZFC-pure): for every cardinal $aleph_0 <= kappa <= c$ and every set $s subset.eq RR$ with $\#s <= kappa$, there is an elementary substructure $S prec RR$ in the ring language with $s subset.eq S$ and $\#S = kappa$.
]

#remark[
  This is Mathlib's downward Löwenheim–Skolem theorem `exists_elementarySubstructure_card_eq` instantiated at $M = RR$; the language has five symbols (`card_ring`), so the language-size condition is absorbed by $aleph_0 <= kappa$. Elementarity of the strata is free — no Tarski–Seidenberg. This single theorem powers every clause of `icahElementary` (Theorem 1).
]

#theorem[
  `elemSubstratumSubfield`: the carrier of any elementary substructure of $RR$ in the ring language is a subfield of $RR$.
]

#remark[
  Closure under $+, dot, -, 0, 1$ is the substructure property; closure under inverses is a transfer of the formula $exists y, x dot y = 1$ along elementarity. This is the satisfaction-to-structure bridge that gives Pillar A strata an algebraic identity.
]

#theorem[
  `elemSubstratum_models_thReal` (ZFC-pure): an elementary substratum of $RR$ satisfies every sentence true in $RR$. In particular it models $op("Th")(RR)$, which contains the first-order axiomatization of real-closed fields in #LRing.
]

#remark[
  RCF is a first-order theory in the ring language (order defined via squares; the axiom schema is the ring axioms, every nonnegative element is a square, and odd-degree polynomials have roots). An elementary substructure of $RR$ therefore satisfies RCF and is real closed in the first-order sense. Native Lean `IsRealClosed` instance transfer along this observation is not formalized; that is a packaging gap, not a first-order gap. Pillar B remains the place where *named* real-closed subfields carry `IsRealClosed` instances.
]

== Nesting, directed unions, and a strictly increasing chain

#lemma[
  `elementaryInclusion` (ZFC-pure): if $S subset.eq T$ are both elementary substructures of a common model $M$, then $S prec T$. Satisfaction in $S$ and in $T$ both reduce to satisfaction in $M$.
]

#theorem[
  `directed_iSup_isElementary` (ZFC-pure): the directed supremum of a nonempty family of elementary substructures of $RR$ is again elementary in $RR$. Specialization: the union of a nonempty monotone chain is elementary (`iUnionChainElem`).
]

#remark[
  This is the Tarski–Vaught test verbatim: an existential witnessed in $RR$ with parameters from the union has its (finitely many) parameters in some common member, which is already $prec RR$.
]

#construction[
  `strictElemChain` (under `NotCH`): a strictly increasing $NN$-indexed elementary chain of $aleph_1$-sized substrata of $RR$. Start from DLS at $aleph_1$; since $aleph_1 < c$, pick $x in.not S_n$; apply `exists_elementary_substratum_extending` to $S_n union {x}$. Successor maps are nesting inclusions. The direct limit is elementarily equivalent to $RR$ (`strictElemChain_directLim_equiv`).
]

This construction is the witness of the chain clauses in both top-level theorems.

== Concrete synthetic stratum

#construction[
  `syntheticStratum`: under `NotCH`, materializes an intermediate-cardinality subset of $RR$ by extracting a concrete set $S subset.eq RR$ with cardinality $aleph_1$ from a cardinal existence theorem.
]

This is the first bridge from a cardinal statement to an inhabited Lean structure. It turns the abstract existence of an intermediate cardinal into a concrete `Stratum` object.

== Subfield strata and size-aware fields

#theorem[
  `fieldOnSubfieldStratum`: every `SubfieldStratum` yields a `SizeAwareField` whose carrier and cardinal match the underlying stratum.
]

The technical point is that the carrier equality is treated as a propositional equality of subtypes, not merely a bijection. This is precisely what the `SizeAwareField.carrier` field requires.

#lemma[
  `fieldOnStratum`: every `Stratum` (not only subfield strata) admits a `SizeAwareField` with matching carrier and cardinal. Formerly an axiom.
]

#remark[
  This is deliberately stated as a lemma, not a theorem: it is a *packaging* result. The proof transports the field structure of a real-closed subfield of the right cardinality (from `exists_rc_subfield`, below) across a cardinality `Equiv`, using `Equiv.field` and `LinearOrder.lift'` — so the resulting operations on the carrier are an arbitrary transport and bear no relation to the ambient operations of $RR$. The mathematically meaningful field structures live on `SubfieldStratum` and `RCSubfieldStratum`, whose operations *are* those of $RR$.
]

== Real-closedness of $RR$ and of relative algebraic closures

#theorem[
  `Real.isRealClosed`: $RR$ is a real-closed field. Formerly an axiom.
]

#remark[
  The proof uses `IsRealClosed.of_linearOrderedField`: squares are handled by `Real.sqrt`, and odd-degree polynomials acquire roots by the intermediate value theorem combined with the leading-coefficient asymptotics `Polynomial.tendsto_atTop`/`atBot`.
]

#theorem[
  `isRealClosed_of_forall_root` and `relAlgebraic_isRealClosed`: a subfield of $RR$ closed under taking real roots of its polynomials is real closed; in particular the relative algebraic closure `relAlgebraic K₀` of any subfield $K_0 subset.eq RR$ is real closed.
]

#theorem[
  `exists_rc_subfield` (ZFC-pure): for every cardinal $kappa$ with $aleph_0 <= kappa <= c$, there exists a real-closed subfield of $RR$ of cardinality exactly $kappa$.
]

#remark[
  This proves (and strengthens) the former `subfieldStratumExists` axiom. The subfield is the relative algebraic closure of the subfield generated by a set of size $kappa$; the cardinality is pinned by `Algebra.IsAlgebraic.cardinalMk_le_max` for the upper bound and injectivity of the generators for the lower bound. It is the concrete (Pillar B) counterpart of `exists_elementary_substratum`: an explicit algebraic description, at the price that elementarity over $RR$ is no longer free.
]

== Real algebraic numbers as a base field

#theorem[
  `algReal_card_le_aleph0`: the real algebraic numbers, represented as `algebraicClosure QQ RR` inside $RR$, have cardinality at most $aleph_0$.
]

Together with the lower bound for infinite types, this supports the concrete base object `algRealSAF`, a countable size-aware field outside the intermediate-cardinality hierarchy.

== Elementarity-preserving composition

#theorem[
  `embLE`: for any $m <= n$, the chain induces an elementary embedding from level $m$ to level $n$.
]

#theorem[
  `embLE_eq_sysEmb`: the elementarity-preserving embedding built by recursive composition agrees as a function with the directed-system embedding used by `Language.DirectLimit`.
]

== Tarski–Vaught theorem for direct limits

#theorem[
  `ElemChain.tarskiVaughtDirectLimit`: if every level of an elementary chain embeds elementarily and compatibly into $RR$, then the direct limit is elementarily equivalent to $RR$. Formerly an axiom.
]

#remark[
  The underlying map is built by `Language.DirectLimit.lift`; elementarity is established by the Tarski--Vaught test: a witness of an existential in $RR$ over parameters from the limit is pulled back to a finite level via the compatibility of the embeddings. *Naming note:* an earlier draft called this result "Łoś-style"; that was a misattribution (Łoś's theorem concerns ultraproducts; the relevant classical result is the Tarski–Vaught elementary chain theorem, here relativized to the ambient model $RR$).
]

#theorem[
  `ElemChain.ofLevelElem` and `realize_ofLevel_iff` (ZFC-pure; *ambient-free* Tarski–Vaught chain theorem): for any elementary chain, the canonical embedding of each level into the direct limit is itself *elementary* — no ambient model required. Consequently the direct limit is elementarily equivalent to every level (`directLim_elementarilyEquivalent`).
]

#remark[
  Unlike the relativized version, this cannot be obtained from Mathlib's Tarski–Vaught test (pulling realization back through `DirectLimit.of` for arbitrary formulas is precisely what is being proved). The proof is a direct induction on `BoundedFormula`; in the `all` case, a direct-limit witness is pulled down to a common level via directedness and `DirectLimit.of_f`, while the universally quantified hypothesis is pushed up through the elementary transition embeddings. Mathlib's `DirectLimit` file currently has no elementarity results at all; this theorem is the form Mathlib should receive.
]

== Cardinality of the direct limit: identity, closure, and sharpness

An earlier draft stated `directLimit_card`: *if* every level has cardinality below the continuum *and* the supremum of the level cardinalities is the continuum, *then* the direct limit has cardinality continuum. Those hypotheses are jointly unsatisfiable in ZFC — König's theorem gives $"cof"(c) > aleph_0$, so a countable supremum of cardinals $< c$ stays $< c$ — making the theorem true and empty. It has been deleted and replaced by three non-vacuous results.

#theorem[
  `directLimit_card_eq_iSup` (ZFC-pure): for an $NN$-indexed chain with infinite supremum of level cardinalities, $\#(op("DirectLim") C) = sup_n \#C_n$.
]

The proof has two halves. The upper bound exhibits the direct limit as a quotient of the sigma type $sum_(n : NN) C_n$, bounding its cardinality by $aleph_0 dot sup_n \#C_n = sup_n \#C_n$. The lower bound uses injectivity of the canonical maps from each level into the direct limit and then takes the supremum over levels.

#theorem[
  `directLimit_card_lt_continuum` and `directLimit_intermediate` (ZFC-pure; closure): if every level of an $NN$-indexed chain has cardinality $< c$, so does the direct limit; if moreover the first level is uncountable, the limit is again of intermediate size. Countable elementary chains never escape the stratum hierarchy.
]

#theorem[
  `cofinal_family_length_lower_bound` (ZFC-pure; sharpness, lower bound): any family ${S_i}_(i in iota)$ of subsets of $RR$ with $\#S_i < c$ for all $i$ and $union.big_i S_i = RR$ satisfies $\#iota >= "cof"(c)$.
]

== Cofinal elementary and real-closed families

#theorem[
  `exists_cofinal_elem_family` (under `NotCH`): there is a monotone, `𝔠.ord`-indexed family of elementary substructures of $RR$, each of intermediate cardinality, covering $RR$. Every inclusion is elementary by `elementaryInclusion`. Compressing along a fundamental sequence yields a covering family of length exactly $"cof"(c)$ (`exists_cofinal_elem_family_cof_length`).
]

#theorem[
  `exists_cofinal_rc_family` and `exists_cofinal_rc_family_cof_length` (under `NotCH`): the same cardinal picture for *named* real-closed subfields (relative algebraic closures). Under `RCFModelComplete`, the inclusions of that family are elementary (`exists_cofinal_rc_family_elementary`, via `nestedRCEmbedding`).
]

#remark[
  Together with the lower bound, these results say: among covering families whose members are subsets of $RR$ of size $< c$, the minimum possible index cardinal is $"cof"(c)$; under `NotCH`, that minimum is attained both by elementary substrata and by named real-closed subfields. The $NN$-indexed chain cannot exhaust $RR$ (König); the cofinal families can.
]

#contribution[
  For the paper, `exists_elementary_substratum`, `elementaryInclusion`, `directed_iSup_isElementary`, `strictElemChain`, `exists_cofinal_elem_family`, `ofLevelElem`, `directLimit_card_eq_iSup`, the $"cof"(c)$ sharpness pair, and `exists_rc_subfield` are the strongest fully proved results to foreground. Each is independent of any grand interpretation of a named hypothesis, and all but the `NotCH`-consuming ones are ZFC-pure — which is precisely their selling point as Mathlib upstreaming candidates.
]
