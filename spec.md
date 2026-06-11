# Spec: ICAH Lean — Next PR: Inclusion-Form RCF Gap and Pillar A Strengthening

> **Status: required implementation slice complete on this branch.**
> This spec responds to the review of PR #6 (`referee-pass-alignment`,
> commit `bf33506`). PR #6 correctly implemented the statement-packaging and
> documentation slice of the second-round review, but the review identified one
> statement-level mismatch and two still-open mathematical strengthening paths.
>
> The required R1–R5 slice has been implemented: the RCF gap is now stated over
> bare subfields in inclusion form, the bundled project helper is derived from
> that statement, PR #6's M6 proof has been verified, and docs have been
> aligned. Optional R6–R7 theorem work remains deferred.

## Problem Statement

PR #6 introduced `RCFSubfieldRealElementary` as the truth-in-naming primary
name for the remaining RCF model-theory gap, with `RCFModelComplete` retained
as compatibility spelling. However, the current proposition is still weaker
and less reusable than the paper prose claims:

```lean
def RCFSubfieldRealElementary : Prop :=
  ∀ R : RCSubfieldStratum,
    Nonempty (R.toSubfieldStratum.toStratum.carrier ↪ₑ[LOR] ℝ)
```

This asserts existence of some elementary embedding from the bundled carrier to
`ℝ`. The paper and upstreaming notes instead describe the inclusion of a
real-closed subfield `K ⊆ ℝ` as elementary. Those are not the same statement.
The existence form is enough for the current constant-chain witness, but it is
not the right Mathlib-facing theorem and will not support a genuinely
increasing chain of real-closed subfields whose transition maps are inclusions.

The next PR should fix this mismatch and, if feasible, start closing the
remaining "Pillar A undersells itself" findings:

1. Restate the RCF gap over a bare `K : Subfield ℝ`, not the project-specific
   `RCSubfieldStratum` bundle.
2. Make the claimed elementary map the actual inclusion/subtype map, not an
   arbitrary existing elementary embedding.
3. Keep project-facing compatibility for `RCFModelComplete`.
4. Optionally prove or scaffold the next Pillar A strengthening:
   elementary substrata are real closed, by transferring a ring-language
   axiomatization of real-closed fields.
5. Optionally prove the directed-union elementary-substructure lemma needed to
   build monotone cofinal families of elementary substrata.

## Requirements

### R1 — Replace the Project-Bundled Gap With a Bare-Subfield Gap

Define a Mathlib-facing proposition over bare subfields:

```lean
def RCFSubfieldRealElementary : Prop :=
  ∀ (K : Subfield ℝ), IsRealClosed K →
    -- inclusion/subtype map K → ℝ is elementary in Language.ring
    ...
```

The target must quantify over `K : Subfield ℝ` and its `IsRealClosed K`
witness only. It must not require:

- `RCSubfieldStratum`
- intermediate-cardinality bounds
- an ordinal index
- `Stratum` packaging

### R2 — Assert Inclusion Elementarity, Not Mere Embeddability

The proposition must state that the canonical subtype/inclusion map
`K → ℝ` is elementary. It must not merely assert `Nonempty (K ↪ₑ[LOR] ℝ)`.

Implementation should search the existing Mathlib API for the most direct
statement shape. Preferred possibilities, in order:

1. A theorem/field on the canonical first-order embedding induced by the
   subfield inclusion, if Mathlib exposes one.
2. A bundled `K ↪ₑ[LOR] ℝ` whose `toFun` is definitionally or propositionally
   equal to `Subtype.val`.
3. A proposition pairing the elementary embedding with a proof that its
   function is the inclusion:

   ```lean
   ∃ e : K ↪ₑ[LOR] ℝ, ∀ x : K, e x = (x : ℝ)
   ```

Use the least awkward version that compiles cleanly and makes the inclusion
content explicit.

### R3 — Derive the Bundled Project Consequence

Add a small helper deriving the current project-facing form for
`RCSubfieldStratum` from the bare-subfield gap. Existing uses in `Main.lean`
should continue to extract an elementary embedding for a bundled
`RCSubfieldStratum`.

If the proposition uses an existential inclusion-form embedding, the helper may
return the embedding component. If it uses a canonical embedding type directly,
wrap it in the existing extraction API.

### R4 — Maintain Compatibility Without Reintroducing Ambiguity

Keep `RCFModelComplete` as a compatibility spelling for now, but make the new
name primary in source comments, README, paper draft, and upstreaming notes.

If Lean accepts the attribute cleanly, mark the compatibility spelling as
deprecated:

```lean
@[deprecated RCFSubfieldRealElementary]
def RCFModelComplete : Prop := RCFSubfieldRealElementary
```

If the deprecation attribute is noisy or incompatible with current uses, do not
force it in this PR; instead leave a clear docstring stating that
`RCFModelComplete` is compatibility-only.

### R5 — Harden the PR #6 M6 Proof After Toolchain Verification

Once Lean is available, verify the new `ICAHStatement.limit_size` proof from
PR #6. If elaboration fails, try only the smallest local changes:

- destructure `exists_cofinal_rc_family` according to its actual constructor
  order;
- replace `(hcover x).imp fun _ hi => hi` with a more explicit witness proof if
  coercion elaboration fails;
- replace `rw [huniv, Cardinal.mk_univ, Cardinal.mk_real]` with
  `simp only [huniv, Cardinal.mk_univ, Cardinal.mk_real]` or
  `Cardinal.mk_congr` if rewriting under subtype cardinality fails.

Do not refactor the cofinal-family construction while fixing this proof.

### R6 — Optional: Prove `elemSubstratum_isRealClosed`

If the inclusion-form gap change is straightforward, attempt the arXiv-blocking
Pillar A strengthening:

```lean
theorem elemSubstratum_isRealClosed
    (S : LOR.ElementarySubstructure ℝ) :
    IsRealClosed (elemSubstratumSubfield S) := ...
```

Expected architecture:

1. Define or reuse a ring-language theory/schema for real-closed fields.
2. Prove `ℝ` satisfies the schema.
3. Transfer each sentence through `S.isElementary`.
4. Convert satisfaction of the schema on `S` into `IsRealClosed` for the
   subfield produced by `elemSubstratumSubfield`.

This is proof-heavy. If it requires substantial first-order schema plumbing,
stop after a precise blocker report and do not mask the gap with a new axiom.

### R7 — Optional: Directed Union of Elementary Substructures

If time remains after R1–R5, specify or prove the model-theoretic helper needed
for a monotone cofinal elementary-strata family:

```lean
-- schematic target
theorem directed_iUnion_elementarySubstructure
    (S : ι → L.ElementarySubstructure M)
    (hdirected : Directed (· ≤ ·) S) :
    ... := ...
```

Expected proof route: Tarski–Vaught. Parameters are finite, so they land in one
directed member; that member supplies the witness by elementarity.

This theorem should be treated as a separate Mathlib-facing contribution if it
grows beyond a small local lemma.

## Constraints

- Do not add project axioms.
- Do not add `sorry`.
- Do not weaken the current zero-axiom audit.
- Do not merge or rely on unrelated `.devcontainer/` changes currently present
  in the worktree.
- Keep PR scope focused. R1–R5 are required; R6–R7 are optional and may become
  follow-up PRs if they require large schema or directed-colimit infrastructure.
- Preserve the existing two-pillar architecture:
  - Pillar A remains `NotCH`-only.
  - Pillar B remains conditional on the RCF subfield-elementarity hypothesis
    until the Mathlib gap is actually proved.
- Keep `LOR` as a compatibility abbreviation for now, but continue documenting
  that it is `Language.ring`, not an ordered-ring language.
- Run Lean through the project wrapper when the toolchain is available:
  `make build`, `make sorry-count`, and `make axiom-count`.

## Architecture

### Lean Source Changes

Primary files:

- `ICAH/FieldOnStratum.lean`
  - redefine `RCFSubfieldRealElementary` over bare subfields;
  - keep or deprecate `RCFModelComplete`;
  - update `RCFModelComplete.emb` or add a new extraction helper.
- `ICAH/Main.lean`
  - adjust only if the extraction helper type changes;
  - verify the strengthened M6 proof from PR #6.
- `ICAH/ElementaryStrata.lean`
  - optional home for `elemSubstratum_isRealClosed`;
  - optional imports may be needed for first-order theory/schema work.

Documentation files:

- `README.md`
- `docs/UPSTREAMING.md`
- `icah-paper-typst/main.typ`
- `icah-paper-typst/sections/01-introduction.typ`
- `icah-paper-typst/sections/03-formal-architecture.typ`
- `icah-paper-typst/sections/05-axiom-inventory.typ`
- `icah-paper-typst/sections/08-conclusion.typ`
- `icah-paper-typst/notes/lean-to-paper-map.md`

### Dependency Direction

The bare-subfield proposition belongs below `RCSubfieldStratum` only because it
uses `IsRealClosed` and `LOR`, both already available in `FieldOnStratum.lean`.
No downstream file should need to know about the internal `RCSubfieldStratum`
packaging to state the Mathlib-facing gap.

If `elemSubstratum_isRealClosed` is attempted, avoid creating a dependency from
`FieldOnStratum.lean` back to `ElementaryStrata.lean`. The theorem should live
in `ElementaryStrata.lean` or a new later module if imports become cyclic.

## Implementation Steps

1. Restore a verified baseline on the PR branch:
   - install or expose the Lean toolchain if needed;
   - run `make build`;
   - record any existing failures before edits.
2. Inspect Mathlib APIs for first-order embeddings induced by subfield
   inclusions:
   - search local `.lake/packages/mathlib` if available;
   - use `#check` probes in a temporary scratch block if needed, removing them
     before commit.
3. Rewrite `RCFSubfieldRealElementary` to quantify over bare `K : Subfield ℝ`
   and assert inclusion elementarity.
4. Update `RCFModelComplete.emb` or add a new helper deriving the bundled
   `RCSubfieldStratum` embedding used by `Main.lean`.
5. Run `lake env lean ICAH/FieldOnStratum.lean` and fix only local type errors.
6. Run `lake env lean ICAH/Main.lean` and harden the PR #6 M6 proof if needed.
7. Update documentation so the paper and README say "inclusion is elementary"
   only if the Lean proposition now really says that.
8. If R1–R5 are complete and green, decide whether to attempt R6:
   - if Mathlib already has suitable RCF theory/schema transfer APIs, implement
     `elemSubstratum_isRealClosed`;
   - otherwise write a blocker report in the PR body and leave the theorem for
     a dedicated PR.
9. If R6 is complete or explicitly deferred, decide whether to attempt R7 under
   the same small-lemma standard.
10. Run final verification:
    - `make build`
    - `make sorry-count`
    - `make axiom-count`
11. Commit on a focused branch and open a PR. The PR body must clearly separate:
    - required statement-level fixes;
    - optional mathematical strengthenings completed;
    - optional strengthenings deferred with blockers;
    - verification results.

## Success Criteria

Required:

1. `RCFSubfieldRealElementary` is stated over bare `K : Subfield ℝ`.
2. The proposition asserts elementarity of the inclusion/subtype map, not mere
   existence of some elementary embedding.
3. Existing `icahTheorem` assembly still compiles using the compatibility
   hypothesis or its helper.
4. The project still declares zero axioms.
5. `make axiom-count` prints 0.
6. `make sorry-count` prints 0.
7. `make build` succeeds.
8. README, upstreaming notes, and paper draft prose match the new Lean
   statement exactly.
9. The PR body documents whether `elemSubstratum_isRealClosed` and the
   directed-union lemma were implemented or deferred.

Optional success:

10. `elemSubstratum_isRealClosed` is proved with no new axioms or sorries.
11. A directed-union elementary-substructure lemma is proved or precisely
    specified as a Mathlib-facing follow-up.
12. The constant-chain M5 witness is documented as temporary, with a clear path
    to a strictly increasing chain once inclusion elementarity and directed
    union infrastructure are available.

## Risks and Mitigations

- **Risk:** Mathlib's elementary embedding API does not expose a convenient
  canonical inclusion embedding for subfields.
  **Mitigation:** Use an existential pair `(e, ∀ x, e x = (x : ℝ))` as the
  proposition shape.

- **Risk:** Deprecating `RCFModelComplete` causes warnings in files guarded by
  exact `#guard_msgs`.
  **Mitigation:** Do not add the deprecation attribute in this PR; use a
  docstring-only compatibility note.

- **Risk:** `elemSubstratum_isRealClosed` requires substantial RCF
  axiomatization work.
  **Mitigation:** Defer it with a blocker report rather than adding axioms or
  large unverified schema code.

- **Risk:** The local environment lacks Lean again.
  **Mitigation:** Do not edit proofs blind. Install/expose the toolchain first
  or leave the PR unmerged until CI is green.

---

# Historical Spec: ICAH Lean — Incremental Proof Formalization

> **Status (June 2026): implemented and superseded — twice.**
> All requirements R1–R10 below are complete, and the project has since gone
> beyond this spec's acceptance criteria. After the June 2026 review round the
> development was restructured around a **two-pillar architecture** with
> **zero project axioms**:
>
> ```
> 'ICAH.icahTheorem'    depends on axioms: [propext, Classical.choice, Quot.sound]
> 'ICAH.icahElementary' depends on axioms: [propext, Classical.choice, Quot.sound]
> ```
>
> Deltas relative to this spec:
>
> - **Axioms → hypotheses.** `axiom not_CH` and `axiom rcfModelComplete` are
>   now named `Prop`s (`NotCH` in `ICAH/Axioms.lean`, `RCFModelComplete` in
>   `ICAH/FieldOnStratum.lean`) threaded as explicit hypotheses. The project
>   declares zero axioms; `make axiom-count` regression-checks 0.
> - **Pillar A (new).** `ICAH/ElementaryStrata.lean` proves the semantic ICAH
>   (`icahElementary`) under `NotCH` alone, via Mathlib's downward
>   Löwenheim–Skolem theorem: elementary substrata of ℝ at every intermediate
>   cardinality, whose carriers are subfields.
> - **Pillar B.** `fieldOnStratum` (R4), `Real.isRealClosed` / real-closedness
>   (R5) were **proved**, not axiomatized. New modules: `ICAH/RealClosed.lean`,
>   `ICAH/CofinalFamily.lean`. The chain theorem (R6) was proved and renamed
>   `tarskiVaughtDirectLimit` (the "Łoś" name was a misattribution); the
>   **ambient-free** version `ofLevelElem` (the canonical maps into the direct
>   limit are elementary) is also proved, by induction on bounded formulas.
> - The ℕ-indexed `directLimit_card` (R6/R7) was **vacuous** under ¬CH by
>   König's theorem (`cof 𝔠 > ℵ₀`); it was replaced by the unconditional
>   identity `directLimit_card_eq_iSup`, the closure theorem
>   `directLimit_card_lt_continuum`, and the sharp `cf(𝔠)` optimality pair in
>   `ICAH/CofinalFamily.lean` (`cofinal_family_length_lower_bound`,
>   `exists_cofinal_rc_family_cof_length`). The honest M6 is the
>   `𝔠.ord`-indexed cofinal family (`exists_cofinal_rc_family`,
>   `cofinal_family_limit_size`), used by `ICAHStatement`.
> - Two axioms introduced after this spec (`subfieldIsRealClosed`,
>   `subfieldStratumElemEmb`) were found to be **mathematically false** as
>   stated and were deleted, replaced by the sound `RCSubfieldStratum`
>   refinement plus the `RCFModelComplete` hypothesis (model completeness of
>   RCF — the one remaining Mathlib gap, used by Pillar B only).
> - The kernel-only axiom sets are enforced in-source by per-theorem
>   `#guard_msgs in #print axioms` blocks (`ICAH/Main.lean`) and by CI
>   (`.github/workflows/ci.yml`).
>
> Current state of record: `AGENTS.md`. Upstreaming plan: `docs/UPSTREAMING.md`.
> Next target: prove `RCFModelComplete`.
> The text below is preserved as the original working spec.

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
