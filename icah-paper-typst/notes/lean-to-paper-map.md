# Lean-to-paper map

| Lean declaration | Paper role | Status | Notes |
|---|---|---:|---|
| `ICAH.not_CH` | Set-theoretic regime | Axiom | Intended external assumption, not a Mathlib gap |
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
| `losDirectLimit` | Elementary equivalence of direct limit | Axiom / Mathlib gap | Tarski--Vaught route |
| `directLimit_card` | Headline cardinal theorem | Proved | Best main theorem for paper |
| `ICAHStatement` | Top-level Prop-valued statement | Definition | Four core claims M1/M3/M5/M6 |
| `icahTheorem` | Assembly theorem | Proved from named assumptions | Include exact axiom inventory |
