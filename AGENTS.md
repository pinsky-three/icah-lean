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
│   ├── Axioms.lean            # NotCH : Prop (hypothesis, NOT an axiom) + intermediate cardinal
│   ├── SizeAwareField.lean    # SizeAwareField structure
│   ├── Strata.lean            # Stratum structure + M1 cardinal lemmas + König helper
│   ├── Definability.lean      # LRing/LOR definability kernel (M2)
│   ├── RealClosed.lean        # IsRealClosed ℝ + root-closed subfield criterion (M4)
│   ├── FieldOnStratum.lean    # SubfieldStratum, relAlgebraic, exists_rc_subfield,
│   │                          #   fieldOnStratum theorem, RCFModelComplete : Prop (M3+M4)
│   ├── ElementaryChain.lean   # ElemChain, tarskiVaughtDirectLimit, ambient-free
│   │                          #   ofLevelElem, directLimit_card_eq_iSup/_lt_continuum (M5)
│   ├── ElementaryStrata.lean  # Pillar A: DLS, nesting, strict ℕ-chain, icahElementary
│   ├── CofinalFamily.lean     # cofinal elementary/RC families + cf(𝔠) optimality (M6)
│   └── Main.lean              # ICAHStatement + icahTheorem + per-theorem #guard_msgs audits
├── .github/workflows/ci.yml   # CI: build + axiom audit + sorry count + axiom count
├── docs/UPSTREAMING.md        # Zulip draft + Mathlib PR sequence
├── Makefile                   # Build targets (see below)
├── lakefile.lean              # Lake project config (Mathlib dependency)
├── lean-toolchain             # Lean version pin
└── spec.md                    # Implementation specification
```

### Module dependency order

```
Axioms ──► SizeAwareField ──► Strata ──► Definability ──► RealClosed ──► FieldOnStratum
                                                              ├──► ElementaryChain ───► Main
                                                              ├──► ElementaryStrata ──► Main
                                                              └──► CofinalFamily ─────► Main
```

### Two-pillar architecture

* **Pillar A** (`ElementaryStrata.lean`): the *semantic* development. Strata
  are elementary substructures of ℝ produced by Mathlib's downward
  Löwenheim–Skolem theorem at every intermediate cardinality; elementarity is
  free by construction. Nesting + directed unions yield a strictly increasing
  ℕ-chain and a cofinal elementary family of length `cf(𝔠)`. Main theorem:
  `icahElementary (hCH : NotCH)`.
* **Pillar B** (`FieldOnStratum.lean` + `Main.lean`): the *conditional
  algebraic realization*. Strata are relative algebraic closures of generated
  subfields, with native real-closed instances. Elementarity of those named
  inclusions uses `RCFModelComplete`. Main theorem:
  `icahTheorem (hCH : NotCH) (hMC : RCFModelComplete)`.

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
| `Axioms.lean` | 1 def (`NotCH : Prop`), 2 theorems | ✅ Hypothesis + `exists_intermediate_cardinal` |
| `SizeAwareField.lean` | 1 structure, 1 lemma | ✅ Compiles |
| `Strata.lean` | 1 structure, 6 lemmas, 1 def | ✅ M1 complete + König helper `aleph0_lt_cof_ord_continuum` |
| `Definability.lean` | 3 defs, 7 lemmas, 1 instance | ✅ M2 complete |
| `RealClosed.lean` | 2 theorems + helpers | ✅ `Real.isRealClosed` **proved** (IVT + sqrt) |
| `FieldOnStratum.lean` | 3 structures, 1 def (`RCFModelComplete : Prop`), ~12 defs/lemmas/theorems | ✅ M3+M4: `fieldOnStratum`, `exists_rc_subfield`, `relAlgebraic_isRealClosed` proved |
| `ElementaryChain.lean` | 2 structures, ~14 defs/lemmas/theorems | ✅ M5: `tarskiVaughtDirectLimit` + ambient-free `ofLevelElem` **proved**; `directLimit_card_eq_iSup`, `directLimit_card_lt_continuum` |
| `ElementaryStrata.lean` | nesting, directed unions, `strictElemChain`, `elemSubstratum_models_thReal`, `icahElementary` | ✅ Pillar A complete: DLS + strict ℕ-chain |
| `CofinalFamily.lean` | RC + elementary cofinal families, cf(𝔠) pair | ✅ Honest M6 + elementary covering family |
| `Main.lean` | `ICAHStatement`, `icahTheorem`, guarded audits | ✅ Strict-chain M5; RC-elementary clause consumes `RCFModelComplete` |

### Hypotheses (the project declares **zero** axioms; `make axiom-count` = 0)

| Hypothesis (`Prop`) | File | Role |
|---|---|---|
| `ICAH.NotCH` | `Axioms.lean` | The ¬CH regime (`continuum ≠ aleph 1`) — definitional for ICAH; consumed by both pillars |
| `ICAH.RCFModelComplete` | `FieldOnStratum.lean` | Mathlib gap: model completeness of RCF (Tarski–Seidenberg); elementary embedding of a real-closed subfield into ℝ. Pillar B only |

Former axioms, now resolved:

| Former axiom | Resolution |
|---|---|
| `ICAH.not_CH` | **Converted to hypothesis** `NotCH : Prop`, threaded explicitly |
| `ICAH.rcfModelComplete` | **Converted to hypothesis** `RCFModelComplete : Prop`, threaded explicitly (Pillar B only) |
| `ICAH.fieldOnStratum` | **Proved** (`FieldOnStratum.lean`): Equiv-transport from a real-closed subfield of cardinality `R.κ` |
| `ICAH.Real.isRealClosed` | **Proved** (`RealClosed.lean`): `of_linearOrderedField` + `Real.sqrt` + IVT |
| `ICAH.subfieldIsRealClosed` | **Deleted — was false** (ℚ is a subfield of ℝ, not real closed) |
| `ICAH.subfieldStratumExists` | **Proved** (`FieldOnStratum.lean`): `exists_rc_subfield` via `relAlgebraic ∘ Subfield.closure` |
| `ICAH.ElemChain.losDirectLimit` | **Proved & renamed** `tarskiVaughtDirectLimit` (`ElementaryChain.lean`): `DirectLimit.lift` + Tarski–Vaught test (Łoś was a misattribution); ambient-free version `ofLevelElem` also proved |
| `ICAH.subfieldStratumElemEmb` | **Deleted — was false** for arbitrary subfields; replaced by `RCFModelComplete` (real-closed hypothesis added) |

Removed as **vacuous**: the ℕ-indexed `directLimit_card` (hypotheses
unsatisfiable under ¬CH since `cof 𝔠 > ℵ₀` by König). Replaced by the
unconditional `directLimit_card_eq_iSup`, `directLimit_card_lt_continuum`,
`directLimit_intermediate`, and the sharp optimality pair
`cofinal_family_length_lower_bound` / `exists_cofinal_rc_family_cof_length`
(least covering-family length = `cf(𝔠)`).

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

The expected output is locked into the build via per-theorem `#guard_msgs`
blocks in `Main.lean` (15 audits covering both pillars and all flagship
building blocks):
```
'ICAH.icahTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ICAH.icahElementary' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The project declares **zero** axioms: `NotCH` and `RCFModelComplete` are
explicit hypotheses visible in type signatures, so every audit reports only
the Lean kernel axioms. If any axiom set drifts — including a hidden
`sorryAx` — `lake build` fails.

---

## Closing the remaining hypothesis gap

### `ICAH.RCFModelComplete` (the only Mathlib gap)

**What**: a real-closed subfield `K ⊆ ℝ` is an *elementary* substructure of ℝ
in the first-order ring language (`K ↪ₑ[LOR] ℝ`; note `LOR := Language.ring` —
order is ring-definable in real-closed fields).

**Mathematical content**: model completeness of the theory of real-closed
fields, a consequence of Tarski–Seidenberg quantifier elimination. True theorem;
formalizing QE for RCF in Mathlib is a substantial project
(`Mathlib.ModelTheory.Algebra.*` has begun work on field languages).

**Proof strategy** (long-term):
1. Formalize quantifier elimination for RCF in `LOR` (Tarski–Seidenberg), or
2. Use a model-theoretic criterion (e.g., every RCF embedding is existentially
   closed, via sign-change/root-counting arguments + the intermediate value
   property of real-closed fields, already partially in
   `Mathlib.FieldTheory.IsRealClosed`).

**Note on soundness**: the real-closedness hypothesis is essential. The former
axiom `subfieldStratumElemEmb` asserted this for *arbitrary* subfields and was
false (ℚ ⊆ ℝ is not elementary: `∃x, x² = 2` distinguishes them). All strata
used in `icahTheorem` now carry `IsRealClosed` witnesses (`RCSubfieldStratum`),
which exist at every intermediate cardinality by `exists_rc_subfield`.

### A note on M6 and König's theorem

The former ℕ-indexed `directLimit_card` hypothesis set (`∀ n, #(obj n) < 𝔠` and
`⨆ n, #(obj n) = 𝔠`) was unsatisfiable since `cof 𝔠 > ℵ₀`
(`aleph0_lt_cof_ord_continuum` in `Strata.lean`); the theorem has been deleted.
The honest M6 is `ICAH.exists_cofinal_rc_family`: a `𝔠.ord`-indexed monotone
family of intermediate-size real-closed subfields whose union is all of ℝ.
Sharpness: the least possible length of such a family is exactly `cf(𝔠)`
(`cofinal_family_length_lower_bound` + `exists_cofinal_rc_family_cof_length`).

### Upstreaming

See `docs/UPSTREAMING.md` for the Zulip post draft and the Mathlib PR
sequence (DLS substrata + cardinality identity → ambient-free chain theorem →
real-closedness lemmas → long-term RCF model completeness).

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
