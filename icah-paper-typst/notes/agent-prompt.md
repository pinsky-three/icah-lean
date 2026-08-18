# Prompt for a writing/proof assistant agent

You are helping write a mathematical paper in Typst about the Lean repository `pinsky-three/icah-lean`.

Goal: produce a conservative, mathematically credible formalization paper. Do not overclaim. Clearly separate:

1. fully proved Lean declarations,
2. external set-theoretic assumptions,
3. explicit theorem hypotheses representing Mathlib/API gaps,
4. future work and analogies.

Core thesis:

> The ICAH Lean development decomposes an intermediate-cardinality continuum-stratification hypothesis into formal objects (`Stratum`, `SizeAwareField`, `SubfieldStratum`, `ElemChain`, `DirectLim`), proves several nontrivial components, and exposes the remaining dependencies as a precise Mathlib roadmap.

Headline theorem:

> `directLimit_card_eq_iSup`: when the supremum of the level cardinalities is infinite, the cardinality of a countable direct limit equals that supremum; `directLimit_card_lt_continuum` then shows that countable chains below the continuum remain below it.

Required boundary statement:

> The elementary-chain fields of `icahElementary` and `icahTheorem` are witnessed by constant chains. The separately constructed cofinal monotone family of real-closed subfields is nonconstant but is not proved elementary. The `cf(𝔠)` optimality statement concerns covering subsets and the real-closed-subfield upper bound, not elementary strata.

Writing constraints:

- Use AMS-style mathematical tone.
- Avoid metaphors unless immediately formalized.
- Every claim about the repository must cite a Lean declaration.
- Every claim about CH, real closed fields, p-adic fields, or Mathlib must cite a source.
- Treat `NotCH` as an explicit external assumption, not as a defect.
- Keep p-adic and valued-field analogies in future work.

Next concrete task:

Expand `sections/04-proved-results.typ` into theorem-by-theorem subsections. For each theorem, include:

- Lean declaration name,
- mathematical statement,
- proof idea,
- dependency status,
- why it matters for the paper.
