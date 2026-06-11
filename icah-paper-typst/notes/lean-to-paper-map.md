# Lean-to-paper map

| Lean declaration | Paper role | Status | Notes |
|---|---|---:|---|
| `ICAH.NotCH` | Set-theoretic regime | Hypothesis | Intended external assumption, not a Mathlib gap |
| `exists_intermediate_cardinal` | First theorem under ¬CH | Proved | Witnesses `ℵ₁` |
| `syntheticStratum` | Concrete stratum object | Proved construction | Materializes a subset of `ℝ` of cardinality `ℵ₁` |
| `SizeAwareField` | Bundled algebra/cardinal object | Definition | Useful as a reusable pattern |
| `SubfieldStratum` | Corrected field-bearing stratum | Definition | Avoids closure problems of raw subsets |
| `subfieldToSAF` | Algebra-to-size bridge | Construction | Converts subfields into size-aware fields |
| `fieldOnSubfieldStratum` | Replacement for abstract field axiom in subfield case | Proved | Key for reducing assumptions |
| `algReal_card_le_aleph0` | Concrete base-field cardinality | Proved | Real algebraic numbers are countable |
| `graphDefinable_add` | Definability of addition graph | Proved | Technical model-theory API use |
| `graphDefinable_mul` | Definability of multiplication graph | Proved | Same as above |
| `ElemChain` | Elementary chain architecture | Definition | Core model-theoretic object |
| `embLE` | Composite elementary embeddings | Construction | Preserves elementarity |
| `embLE_eq_sysEmb` | Coherence with directed-system API | Proved | Important Lean/API bridge |
| `DirectLim` | Direct-limit carrier | Definition | Uses `Language.DirectLimit` |
| `tarskiVaughtDirectLimit` | Elementary equivalence of direct limit | Proved | `DirectLimit.lift` + Tarski--Vaught test; Mathlib PR candidate |
| `directLimit_card_eq_iSup` / `directLimit_card_lt_continuum` | Direct-limit cardinality identity and closure | Proved | Reusable cardinal-arithmetic theorem; replaces the vacuous former `directLimit_card` |
| `Real.isRealClosed` | ℝ is real closed | Proved | `of_linearOrderedField` + sqrt + IVT; Mathlib PR candidate |
| `isRealClosed_of_forall_root` | Root-closure criterion for subfields | Proved | Drives `relAlgebraic_isRealClosed` |
| `exists_rc_subfield` | RC subfields of every infinite cardinality ≤ 𝔠 | Proved | Strengthens former `subfieldStratumExists` axiom |
| `fieldOnStratum` | Field on arbitrary stratum | Proved | Equiv-transport; formerly an axiom |
| `RCSubfieldStratum` | Real-closed field-bearing stratum | Definition | Sound replacement for deleted false axioms |
| `RCFSubfieldRealElementary` / `RCFModelComplete` | Real-closed subfields of ℝ embed elementarily | Hypothesis / Mathlib gap | Specialized consequence of RCF model completeness; the single remaining gap |
| `exists_cofinal_rc_family` | Honest M6: cofinal RC family | Proved | 𝔠.ord-indexed; avoids König obstruction |
| `cofinal_family_limit_size` | Union has cardinality 𝔠 | Proved | Limit-size clause of `ICAHStatement` |
| `ICAHStatement` | Top-level Prop-valued statement | Definition | Core claims M1/M3/M5/M6 (M6 via cofinal family) |
| `icahTheorem` | Assembly theorem | Proved | Hypotheses: `NotCH`, `RCFModelComplete`; project declares zero axioms, enforced via `#guard_msgs` |
