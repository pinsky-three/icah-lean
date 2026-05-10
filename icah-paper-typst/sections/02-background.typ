#import "../src/macros.typ": *

= Background

== The continuum and the role of $not "CH"$

Let $c = 2^aleph_0$ denote the cardinality of the continuum. The Continuum Hypothesis states that there is no cardinal $kappa$ satisfying $aleph_0 < kappa < c$. Since Gödel and Cohen, the standard mathematical background is that CH is independent of ZFC, assuming ZFC is consistent @koellner_ch @cohen1966.

The Lean project therefore does not attempt to prove $not "CH"$ in ZFC. Instead, it introduces $not "CH"$ as a named axiom and develops all downstream objects relative to that assumption.

#proposition[
  Under the project axiom `ICAH.not_CH`, the cardinal $aleph_1$ witnesses the existence of an intermediate cardinal:
  $ exists kappa, aleph_0 < kappa and kappa < 2^aleph_0. $
]

The Lean proof uses the standard inequality $aleph_0 < aleph_1$, the theorem $aleph_1 <= c$, and converts the inequality plus non-equality $c != aleph_1$ into the strict inequality $aleph_1 < c$.

== Real closed fields and definability

Real closed fields are the algebraic and model-theoretic setting closest to the ordered real field. They admit quantifier-elimination results and provide the natural language in which order, addition, multiplication, and definability can be studied together @vddries1988 @marker2002.

ICAH uses this background in a restrained way. The code does not merely assume every bare subset of $RR$ is a field. Instead, it introduces `SubfieldStratum`, which requires the carrier set to be the underlying set of a `Subfield RR`. This is the right formal move: closure under field operations is obtained from the subfield structure rather than reconstructed ad hoc.

== Elementary chains and direct limits

An elementary chain is a sequence of structures connected by elementary embeddings. The classical model-theoretic expectation is that unions or directed limits of elementary chains preserve the relevant first-order theory under suitable hypotheses @weiss_model_theory.

The Lean project packages this through `ElemChain`, where each level carries an `LOR`-structure and each successor map is an elementary embedding. The direct limit is then implemented using Mathlib's `Language.DirectLimit` API.
