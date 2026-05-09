# AGENTS.md — ICAH Lean Formalization Guide

This document describes the repository layout, build workflow, proof conventions,
and the hybrid human-agent formalization process for the ICAH Lean project.

---

## Repository layout

```
icah-lean/
├── ICAH.lean                  # Umbrella import (all modules)
├── ICAH/
│   ├── Prelude.lean           # Smoke tests; Mathlib availability check
│   ├── Axioms.lean            # Global set-theoretic axioms (not_CH)
│   ├── SizeAwareField.lean    # SizeAwareField structure
│   ├── Strata.lean            # Stratum structure + M1 cardinal lemmas
│   ├── Definability.lean      # LOR definability kernel (M2)
│   ├── FieldOnStratum.lean    # SubfieldStratum, field construction (M3+M4)
│   ├── ElementaryChain.lean   # ElemChain, StratumChain, directLimit_card (M5+M6)
│   └── Main.lean              # ICAHStatement + icahTheorem assembly
├── Makefile                   # Build targets (see below)
├── lakefile.lean              # Lake project config (Mathlib dependency)
├── lean-toolchain             # Lean version pin
└── spec.md                    # Implementation specification
```

### Module dependency order

```
Axioms ──► SizeAwareField ──► Strata ──► Definability ──► FieldOnStratum ──► ElementaryChain ──► Main
```

---

## Build commands

```bash
# First-time setup: download Mathlib cache (~8 GB, takes a few minutes)
make cache

# Build everything
make build

# Count sorrys (should be 0 in a clean state)
make sorry-count

# Count and list project axioms
make axiom-count

# Remove build artifacts
make clean
```

The `Makefile` requires `~/.elan/bin/lake` and `~/.elan/bin/lean` on PATH.
If `lake` is not found, run:
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
```

---

## Current proof status

| File | Declarations | Status |
|---|---|---|
| `Prelude.lean` | 1 example | ✅ Compiles |
| `Axioms.lean` | 1 axiom, 1 theorem | ✅ `not_CH` + `exists_intermediate_cardinal` |
| `SizeAwareField.lean` | 1 structure, 1 lemma | ✅ Compiles |
| `Strata.lean` | 1 structure, 5 lemmas, 1 def | ✅ M1 complete; `fieldOnStratum` axiom remains |
| `Definability.lean` | 3 defs, 7 lemmas, 1 instance | ✅ M2 complete |
| `FieldOnStratum.lean` | 2 structures, 6 defs/lemmas, 3 axioms, 1 instance | ✅ M3 complete; M4 axioms documented |
| `ElementaryChain.lean` | 2 structures, 7 defs/lemmas, 1 axiom | ✅ M6 proved; M5 axiom documented |
| `Main.lean` | 1 structure, 2 defs, 1 theorem, 1 axiom | ✅ `icahTheorem` proved |

### Named axioms (run `make axiom-count` to verify)

| Axiom | File | Status |
|---|---|---|
| `ICAH.not_CH` | `Axioms.lean` | Global assumption (¬CH) |
| `ICAH.fieldOnStratum` | `Strata.lean` | Abstract placeholder; proved for `SubfieldStratum` |
| `ICAH.Real.isRealClosed` | `FieldOnStratum.lean` | Mathlib gap: `IsRealClosed ℝ` not yet an instance |
| `ICAH.subfieldIsRealClosed` | `FieldOnStratum.lean` | Mathlib gap: subfield RCF not yet in Mathlib |
| `ICAH.subfieldStratumExists` | `FieldOnStratum.lean` | Existence of intermediate-size subfield |
| `ICAH.ElemChain.losDirectLimit` | `ElementaryChain.lean` | Mathlib gap: Łoś for `Language.DirectLimit` |
| `ICAH.subfieldStratumElemEmb` | `Main.lean` | Mathlib gap: elementary embedding of subfield into ℝ |

---

## Incremental formalization workflow

This project uses a **hybrid human-agent** workflow. The agent handles mechanical
formalization; the human supervises strategy and resolves blockers.

### Core rule

> Do not optimize for impressive output. Optimize for the next verified step.

### Phase 1 — Preparation (before writing any proof)

Before touching a file, produce a formalization plan:

1. State the target theorem precisely.
2. List required definitions, imports, and typeclass assumptions.
3. Identify helper lemmas and their dependency order.
4. Classify each subgoal: Easy / Medium / Hard.
5. Identify parallelizable tasks.

Do not write the full proof in this phase.

### Phase 2 — Incremental formalization

Work on exactly one unit at a time:
- one lemma or theorem step
- one induction case
- one typeclass/coercion bridge
- one algebraic identity

For each unit, output:
1. **Current target** — exact statement
2. **Why this is next** — dependency reason
3. **Code** — only the code for this unit
4. **Verification** — checked or unverified
5. **Blockers** — unresolved issues
6. **Next step** — exactly one recommendation

### Phase 3 — Compilation and error-driven revision

After each meaningful change, run `lake build` or `lake env lean <file>`.

If a proof fails:
1. Read the exact error message.
2. Identify the smallest failing location.
3. Inspect the local goal state.
4. Revise only the relevant block.
5. Do not replace the whole proof with a larger tactic blob.

### Phase 4 — Escalation

If stuck after reasonable attempts, stop and report:

```
Blocker report:
- Target: [exact lemma/step]
- Failing code: [snippet]
- Error: [compiler message]
- Local goal: [goal state]
- Hypotheses: [relevant hyps]
- Likely cause: [explanation]
- Smallest fix: [minimal patch]
- Solving mode: [rewrite / calc / congr / ext / ring / case split / induction / coercion / library search / human patch]
- Request: [smallest useful human intervention]
```

### Phase 5 — Refinement

After the proof compiles:
- Extract repeated fragments into helper lemmas.
- Simplify long tactic blocks.
- Improve names.
- Run `make sorry-count` and `make axiom-count` to verify the state.

---

## Lean 4 + Mathlib style rules

### Instances and structure

- Use `noncomputable` for anything depending on `Real`, `Cardinal`, or `Subfield ℝ`.
- Register `LOR.Structure` instances globally when they are needed by multiple files
  (see `subfieldStratumLORStr` in `FieldOnStratum.lean`).
- Prefer `inferInstance` over explicit instance terms when synthesis works.
- When transporting instances along type equalities, use `heq ▸ inst` (not `rw [heq]`
  inside `instance` bodies, which causes instance mismatch errors).

### Tactics

- `simp only [...]` with an explicit lemma list for stability.
- `exact?` / `apply?` to find library lemmas before inventing proofs.
- `calc` for readable chains of inequalities or equalities.
- `ring`, `linarith`, `omega`, `norm_num` for arithmetic.
- `Cardinal.mk_congr` + `Equiv.subtypeEquivRight` for cardinality of subtypes.
- Avoid `simp` without arguments in final proofs (fragile).

### Cardinal arithmetic

Key lemmas used in this project:

```lean
Cardinal.aleph0_pos           : 0 < ℵ₀
Cardinal.aleph0_lt_aleph_one  : ℵ₀ < ℵ₁
Cardinal.aleph_one_le_continuum : ℵ₁ ≤ 𝔠
Cardinal.mk_real              : #ℝ = 𝔠
Cardinal.mkRat                : #ℚ = ℵ₀
Cardinal.continuum_mul_aleph0 : 𝔠 * ℵ₀ = 𝔠
Cardinal.sum_const            : sum (fun _ : ι => c) = #ι * c
Cardinal.sum_le_sum           : (∀ i, f i ≤ g i) → sum f ≤ sum g
Cardinal.mk_le_of_surjective  : Surjective f → #β ≤ #α
Cardinal.mk_le_of_injective   : Injective f → #α ≤ #β
Cardinal.le_mk_iff_exists_set : c ≤ #α ↔ ∃ S : Set α, #S = c
Algebra.IsAlgebraic.cardinalMk_le_max : #L ≤ max #R ℵ₀  (for algebraic extensions)
```

### First-order model theory

Key API used in this project:

```lean
Language.DirectLimit          : (ι → Type) → ... → Type
DirectLimit.inductionOn       : every element comes from some level
DirectLimit.of                : embedding of level n into DirectLimit
Language.ElementaryEmbedding  : M ↪ₑ[L] N
ElementaryEmbedding.refl      : identity is elementary
Language.Equiv                : M ≅[L] N
Set.Definable                 : A.Definable L s ↔ ∃ φ, s = setOf φ.Realize
withConstants_expansion       : lhomWithConstants is an expansion
LHom.realize_onFormula        : realize commutes with LHom when IsExpansionOn
Formula.realize_relabel       : realize of relabeled formula
BoundedFormula.realize_toFormula : realize of toFormula
```

---

## `#print axioms` discipline

Every theorem that is part of the ICAH claim should be checked with:

```lean
#print axioms icahTheorem
```

The expected output (non-kernel axioms only):
```
ICAH.not_CH
ICAH.fieldOnStratum
ICAH.subfieldStratumExists
ICAH.Real.isRealClosed
ICAH.subfieldIsRealClosed
ICAH.ElemChain.losDirectLimit
ICAH.subfieldStratumElemEmb
```

If `sorryAx` appears, there is a hidden `sorry` somewhere — find and fix it before
declaring the proof complete.

---

## Closing the remaining axiom gaps

The following axioms are the primary targets for the next formalization stage:

### 1. `ICAH.ElemChain.losDirectLimit` (highest priority)

**What**: Łoś/Tarski–Vaught theorem for `Language.DirectLimit` of elementary embeddings.

**Proof strategy**:
1. Use `Language.DirectLimit.lift` to build an embedding `DirectLim C ↪[L] ℝ`.
2. Apply `Language.Embedding.isElementary_of_exists` (Tarski–Vaught test):
   for every formula φ and tuple x in DirectLim, if ℝ ⊨ ∃y, φ(lift(x), y) then
   DirectLim ⊨ ∃y, φ(x, y).
3. The witness in ℝ can be pulled back to some level G n via the compatible embeddings.

**Mathlib status**: `Language.DirectLimit` exists; the elementary version is absent.
Consider contributing this to Mathlib.

### 2. `ICAH.Real.isRealClosed` + `ICAH.subfieldIsRealClosed`

**What**: `IsRealClosed ℝ` instance and its inheritance by subfields.

**Proof strategy for `IsRealClosed ℝ`**:
- `isSquare_or_isSquare_neg`: use `Real.sqrt` for non-negatives.
- `exists_isRoot_of_odd_natDegree`: use IVT (`intermediate_value_univ`) +
  `Polynomial.tendsto_atTop`/`atBot` for the sign-change argument.

**Proof strategy for subfields**:
- Show `K ≺ ℝ` (elementary substructure) using `subfieldStratumElemEmb`.
- Cite that elementary substructures of RCFs are RCFs.

### 3. `ICAH.subfieldStratumExists`

**What**: existence of a subfield of ℝ with `ℵ₀ < κ < 𝔠`.

**Proof strategy**: Under `not_CH`, `ℵ₁ < 𝔠`. Take a transcendence basis B of ℝ
over ℚ with `#B = 𝔠`. Choose a subset B' ⊆ B with `#B' = ℵ₁`. The real closure
of ℚ(B') in ℝ is a subfield of ℝ with cardinality `ℵ₁`. This requires:
- `Cardinal.exists_subset_card_le` or similar for choosing B'.
- Real closure construction (not yet in Mathlib for subfields of ℝ).

### 4. `ICAH.fieldOnStratum` (abstract placeholder)

**What**: every `Stratum` (not just `SubfieldStratum`) admits a `SizeAwareField`.

**Current state**: proved for `SubfieldStratum` via `fieldOnSubfieldStratum`.
The abstract axiom remains for strata whose carrier is not a priori a subfield.

**Resolution**: either restrict `Stratum` to always be a `SubfieldStratum`, or
prove that every intermediate-size definable set in ℝ is contained in a subfield.

---

## Escalation protocol

| Situation | Action |
|---|---|
| Proof compiles with warnings only | Proceed |
| `exact?` / `apply?` finds nothing | Try `simp?`, `decide`, or manual calc |
| Instance synthesis fails | Check if a global `instance` is needed; use `haveI` locally |
| Type mismatch after `▸` | Use `Equiv.subtypeEquivRight` + `Cardinal.mk_congr` instead |
| `sorry` needed temporarily | Replace with a named `axiom`; document the blocker |
| Stuck after 3 attempts | Write a blocker report; escalate to human |
| Mathlib lemma not found | Search with `exact?`, grep `.lake/packages/mathlib`, or check Mathlib docs |
