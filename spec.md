# Spec: ICAH Lean — Incremental Proof Formalization

## Problem Statement

The `icah-lean` repository contains a Lean 4 + Mathlib formalization of the
Intermediate-Cardinality Arithmetic Hypothesis (ICAH). The current codebase
compiles but is largely scaffolding: two `axiom` declarations stand in for
unproved results, two `sorry`-stubs block the key theorems, and several
milestones (M3, M4, M6) have no Lean code at all.

The goal is to:
1. Advance the formalization through all milestones (M1–M6) incrementally,
   replacing stubs with real proofs wherever Mathlib support exists.
2. Produce a `Makefile` for the build/check workflow.
3. Produce a detailed `AGENTS.md` encoding the hybrid human-agent workflow for
   future contributors.

---

## Current Status Audit

| File | Declarations | Stubs / Gaps |
|---|---|---|
| `Prelude.lean` | 1 example | None — smoke test only |
| `SizeAwareField.lean` | 1 structure, 1 lemma | None — compiles cleanly |
| `Strata.lean` | 1 structure, 1 def | **`axiom fieldOnStratum`** — no construction |
| `Definability.lean` | 3 defs, 5 lemmas, 1 instance | Compiles; `GraphDefinable` unused |
| `ElementaryChain.lean` | 2 structures, 6 defs/lemmas | **2 `sorry`-stubs** (`directLimit_elementarilyEquiv_real`, `directLimit_card`) |
| `Main.lean` | 1 def, 1 axiom | **`axiom icahAxiom`** — no proof |

**Open blockers:**
- `fieldOnStratum`: requires a concrete stratum family with closure proofs (M3).
- `directLimit_elementarilyEquiv_real`: requires a Łoś/Tarski–Vaught theorem
  for `Language.DirectLimit` of elementary embeddings — not yet in Mathlib.
- `directLimit_card`: requires cardinal arithmetic for `Language.DirectLimit`.
- `icahAxiom`: depends on all prior milestones.

---

## Requirements

### R1 — Global axiom: ¬CH

Add a single named axiom `ICAH.not_CH : ¬(continuum = aleph 1)` in
`ICAH/Prelude.lean` (or a new `ICAH/Axioms.lean`). All cardinal-bound
witnesses on `Stratum` may cite this axiom. Track it with `#print axioms`.

### R2 — M1: Cardinal scaffolding (strengthen existing)

- Prove `Stratum.card_pos`: `0 < R.κ` from `h_bounds`.
- Prove `Stratum.card_lt_continuum`: `R.κ < continuum` directly from `h_bounds`.
- Prove `Stratum.card_gt_aleph0`: `aleph0 < R.κ` directly from `h_bounds`.
- Add a synthetic example `Stratum` instance (using `not_CH`) to demonstrate
  the bounds are satisfiable.

### R3 — M2: Definability kernel (extend existing)

- Add `DefinableOn_product`: definability is closed under finite products
  (`Set.Definable` already has this; expose it via `DefinableOn`).
- Add `DefinableOn_preimage`: preimage of a definable set under a definable map
  is definable.
- Prove `graphDefinable_add`: the graph of real addition restricted to a
  stratum `S` is `GraphDefinable S (+)` — using the fact that `+` is
  `LOR`-term-definable.
- Prove `graphDefinable_mul`: same for multiplication.

### R4 — M3: Internal field operations

Create `ICAH/FieldOnStratum.lean`:

- Define a concrete stratum family: for each `n : ℕ`, let `S n` be the set of
  reals that are algebraic over ℚ of degree ≤ `2^n` (or another explicit
  definable family — see implementation notes).
- Prove closure of `S n` under `+` and `·`.
- Construct `[Field (Stratum.carrier R)]` and `[LinearOrder (Stratum.carrier R)]`
  instances by restriction from ℝ.
- Prove `[IsStrictOrderedRing (Stratum.carrier R)]`.
- Replace `axiom fieldOnStratum` with a `theorem fieldOnStratum` using this
  construction.

### R5 — M4: Real-closedness

In `ICAH/FieldOnStratum.lean` (or a new `ICAH/RealClosed.lean`):

- Path A (preferred): show `Stratum.carrier R ≺ ℝ` as an elementary
  substructure in `LOR`, then cite the Mathlib theorem that elementary
  substructures of real-closed fields are real-closed.
- If Path A is blocked (Mathlib gap), use Path B: prove directly that every
  positive element has a square root and every odd-degree polynomial has a root
  in the carrier.
- Deliver `theorem F_n_realClosed (R : Stratum) : RealClosedField (Stratum.carrier R)`.

### R6 — M5: Elementary chain theorems

In `ICAH/ElementaryChain.lean`:

- Attempt to prove `directLimit_elementarilyEquiv_real` using Mathlib's
  `Language.DirectLimit` API and the Tarski–Vaught criterion.
- If the Łoś theorem for direct limits is absent from Mathlib, replace the
  `sorry` with a named `axiom` (`ICAH.losDirectLimit`) and document the gap
  precisely.
- Attempt to prove `directLimit_card` using `Cardinal.mk_iUnion_le` or
  `Cardinal.iSup_le` and the chain's cardinal hypotheses.
- If blocked, replace `sorry` with a named `axiom` (`ICAH.directLimitCard`).

### R7 — M6: Size of the limit

In `ICAH/ElementaryChain.lean` or a new `ICAH/LimitSize.lean`:

- Prove `theorem limitField_card (SC : StratumChain) : Cardinal.mk (SC.toElemChain.DirectLim) = continuum`
  under the hypothesis that `⨆ n, SC.strata n |>.κ = continuum`.
- This may depend on `ICAH.directLimitCard` (axiom) if M5 is blocked.

### R8 — Main theorem

In `ICAH/Main.lean`:

- Refine `ICAHStatement` to the precise conjunction of M1–M6 results.
- Replace `axiom icahAxiom` with a `theorem icahAxiom` that assembles the
  milestone results, citing any remaining axioms explicitly.
- Run `#print axioms icahAxiom` and record the axiom set in a comment.

### R9 — Makefile

Create a `Makefile` at the repo root with targets:

```makefile
build        # lake build
check        # lake env lean ICAH.lean
sorry-count  # grep -rn sorry ICAH/ --include=*.lean | wc -l
axiom-count  # grep -rn "^axiom " ICAH/ --include=*.lean | wc -l
clean        # lake clean
```

### R10 — AGENTS.md

Create `AGENTS.md` at the repo root encoding the hybrid human-agent workflow:

- Repo layout and module dependency graph.
- Build commands and how to interpret Lean errors.
- The incremental formalization workflow (phases 1–5 from the master prompt).
- Per-milestone status table (updated to reflect post-implementation state).
- Escalation protocol: when to leave a `sorry`, when to introduce a named
  `axiom`, when to ask the human.
- Lean 4 + Mathlib style rules specific to this project.
- `#print axioms` discipline.

---

## Acceptance Criteria

1. `lake build` completes with zero errors.
2. `grep -rn "^sorry$\|  sorry$" ICAH/ --include="*.lean"` returns only
   intentional stubs, each accompanied by a named `axiom` and a blocker comment.
3. `#print axioms icahAxiom` lists only: `Classical.choice`, `propext`,
   `Quot.sound`, `funext`, `ICAH.not_CH`, and any explicitly named gap axioms
   (`ICAH.losDirectLimit`, `ICAH.directLimitCard` if needed).
4. All milestone deliverables from the README (M1–M6) have corresponding Lean
   declarations (theorems, instances, or named axioms with documented blockers).
5. `Makefile` targets `build`, `sorry-count`, `axiom-count`, and `clean` all
   execute without error.
6. `AGENTS.md` exists, covers all sections in R10, and is accurate relative to
   the post-implementation state.

---

## Implementation Approach (ordered)

1. **Audit & baseline** — run `lake build`, record current sorry/axiom counts,
   confirm the build is green before any changes.

2. **Add `not_CH` axiom** — create `ICAH/Axioms.lean`, add
   `axiom ICAH.not_CH`, import it in `ICAH.lean` and `Strata.lean`.

3. **M1 — Cardinal lemmas** — add `card_pos`, `card_lt_continuum`,
   `card_gt_aleph0` to `Strata.lean`; add a synthetic `Stratum` example.

4. **M2 — Definability extensions** — add product, preimage, `graphDefinable_add`,
   `graphDefinable_mul` to `Definability.lean`.

5. **M3 — Concrete stratum family** — create `ICAH/FieldOnStratum.lean`;
   define the carrier family; prove closure; build field instances; replace
   `axiom fieldOnStratum`.

6. **M4 — Real-closedness** — prove `F_n_realClosed` via Path A or B in
   `FieldOnStratum.lean` or `RealClosed.lean`.

7. **M5 — Elementary chain theorems** — attempt proofs of
   `directLimit_elementarilyEquiv_real` and `directLimit_card`; replace
   `sorry`s with named axioms if blocked.

8. **M6 — Limit size** — prove `limitField_card` in `ElementaryChain.lean`
   or `LimitSize.lean`.

9. **Main theorem** — refine `ICAHStatement`, replace `axiom icahAxiom` with
   a theorem, run `#print axioms`.

10. **Makefile** — create with all required targets.

11. **AGENTS.md** — write the contributor/agent guide reflecting final state.

12. **Final verification** — run `lake build`, `make sorry-count`,
    `make axiom-count`; confirm acceptance criteria.

---

## Implementation Notes

### Concrete stratum family for M3

The simplest family that is mathematically correct and Lean-tractable:

- Use `Polynomial.aeval`-based algebraic numbers: `S n := {x : ℝ | IsAlgebraic ℚ x}`.
  This is a single stratum (the algebraic reals), not a hierarchy — but it is
  a real-closed field and is definable. Use it as the base case `F_0`.
- For the hierarchy, index by definability rank: `S n` = reals definable by
  `LOR`-formulas of quantifier depth ≤ `n` with algebraic parameters. This
  requires a quantifier-depth predicate not yet in Mathlib; use an `axiom` for
  the existence of such a family and prove the algebraic properties from it.
- Alternative (simpler, fully provable): use `{x : ℝ | IsAlgebraic ℚ x}` as
  the single concrete field, prove it is real-closed, and treat the hierarchy
  as an abstract `StratumChain` with existence axioms.

### Mathlib gaps to anticipate

| Gap | Likely workaround |
|---|---|
| Łoś theorem for `Language.DirectLimit` | Named axiom `ICAH.losDirectLimit` |
| Cardinal of `Language.DirectLimit` | Named axiom `ICAH.directLimitCard` |
| Quantifier-depth definability hierarchy | Named axiom for existence of the family |
| `RealClosedField` instance for algebraic reals | May exist as `Mathlib.RingTheory.AlgebraicClosure`; search first |

### File dependency order

```
Axioms.lean
  └─ Prelude.lean
  └─ SizeAwareField.lean
       └─ Strata.lean
            └─ Definability.lean
            └─ FieldOnStratum.lean (new)
                 └─ RealClosed.lean (new, optional)
                      └─ ElementaryChain.lean
                           └─ LimitSize.lean (new, optional)
                                └─ Main.lean
```
