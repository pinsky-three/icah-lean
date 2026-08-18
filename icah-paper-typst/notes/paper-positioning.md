# Paper positioning

## Strongest framing

**Elementary strata of the continuum under ¬CH: a Lean formalization study.**

This is stronger and more credible than presenting ICAH as a completed new mathematical theory or axiom candidate.

## What to foreground

1. `strictElemChain` and `exists_cofinal_elem_family_cof_length` as the informal picture, now formalized.
2. `elementaryInclusion` and `directed_iSup_isElementary` as the cheap lemmas that unlock it.
3. `ofLevelElem` and `tarskiVaughtDirectLimit` as the general elementary-chain results.
4. `exists_elementary_substratum` and `exists_rc_subfield` as the two cardinal-controlled existence theorems.
5. The exact `cf(𝔠)` threshold, attained by both elementary substrata and named real-closed subfields.
6. The explicit hypothesis inventory as a research roadmap; Pillar B is the conditional algebraic pillar.

## Boundary that must remain explicit

- Pillar A needs only `NotCH`.
- Pillar B's named algebraic inclusions are elementary only given `RCFModelComplete`.
- Elementary substrata model `Th(ℝ)` (first-order RCF); native `IsRealClosed` transfer is not formalized.
- Do not claim the RCF gap is uniquely remaining in Mathlib until the Zulip check returns.

## What to avoid

- Do not overclaim novelty in set theory.
- Do not restore "Hypothesis" branding as an axiom-candidate comparison.
- Do not describe constant-chain objects as the top-level witnesses.
- Do not present p-adic analogies as part of the proof; keep them as future work.
