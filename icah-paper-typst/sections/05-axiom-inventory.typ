#import "../src/macros.typ": *

#pagebreak(weak: true)
= Axiom inventory and Mathlib roadmap

A central strength of the Lean development is that it does not hide its assumptions. The theorem `icahTheorem` is assembled from proved components plus a small set of named dependencies.

== External mathematical assumption

#gap[
  `ICAH.not_CH`: the negation of the Continuum Hypothesis, represented as `continuum ≠ aleph 1`.
]

This is not a Mathlib gap. It is the intended set-theoretic regime of the project. The paper should say explicitly that the theory is developed relative to $not "CH"$.

== Abstract field-on-stratum assumption

#gap[
  `ICAH.fieldOnStratum`: every stratum admits a size-aware field whose carrier and cardinal match the stratum.
]

This is too strong for arbitrary raw strata. The paper should present `SubfieldStratum` as the corrected refinement and `fieldOnSubfieldStratum` as the proved replacement in the subfield case.

== Intermediate-size subfields

#gap[
  `ICAH.subfieldStratumExists`: under $not "CH"$, there exists a subfield of $RR$ with cardinality strictly between $aleph_0$ and $c$.
]

The expected classical construction is to take a transcendence basis of $RR$ over $QQ$, choose a subset of size $aleph_1$, and take the real closure of the generated subfield inside $RR$. The Lean work needed is not the idea itself but the assembly of the relevant field-theoretic and cardinality APIs.

== Real-closedness infrastructure

#gap[
  `ICAH.Real.isRealClosed`: package `IsRealClosed RR` as an available Mathlib fact.
]

#gap[
  `ICAH.subfieldIsRealClosed`: formulate and prove the preservation of real-closedness for the intended elementary subfield setting.
]

The first gap is likely a direct Mathlib contribution. The second is more structural: it requires connecting `IsRealClosed` to first-order real-closed-field theory or using an appropriate elementary-substructure theorem.

== Direct limits of elementary chains

#gap[
  `ICAH.ElemChain.losDirectLimit`: if every level of an elementary chain embeds compatibly into $RR$, then the direct limit is elementarily equivalent to $RR$.
]

This is the most important model-theoretic API gap. The expected proof route is to build the underlying embedding by `Language.DirectLimit.lift` and prove it elementary via a Tarski--Vaught argument.

== Recommended order of attack

+ Polish and submit `IsRealClosed RR` to Mathlib.
+ Extract `directLimit_card` as a reusable theorem or at least document it as a local theorem independent of ICAH.
+ Prove an elementary-direct-limit theorem for `Language.DirectLimit`.
+ Formalize intermediate-cardinality subfields via transcendence bases and real closure.
+ Replace the global `fieldOnStratum` axiom with refined hypotheses, probably using `SubfieldStratum` or a closure predicate.
