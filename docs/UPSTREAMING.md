# UPSTREAMING.md — Mathlib engagement plan

This document tracks what the ICAH development can contribute back to Mathlib,
in what order, and how to open the conversation. Actual posting and PRs are
done by the human maintainer; this file keeps the drafts and sequencing.

Pinned state: toolchain `leanprover/lean4:v4.31.0-rc2`, Mathlib
`a810615ff479602ad66b5403d179bfa805314a50` (June 2026).

---

## Step 0 — Zulip post (before any PR)

Target stream: `#mathlib4 > model theory` (cross-link `#mathlib4 > algebra`
if the RCF discussion takes off).

### Draft

> **Subject: Elementary chain theorems for `Language.DirectLimit` + model
> completeness of RCF — upstreaming check**
>
> Hi all. As part of a small formalization study
> ([icah-lean](https://github.com/pinsky-three/icah-lean), Lean
> `v4.31.0-rc2`, Mathlib `a810615`), we proved a few results around
> `FirstOrder.Language.DirectLimit` and real-closed subfields of `ℝ` that
> Mathlib doesn't seem to have. Before opening PRs I'd like to check for
> duplication with in-progress work:
>
> 1. **Elementary chain theorems.** Mathlib's `ModelTheory/DirectLimit.lean`
>    has no elementarity results. We proved, for ℕ-indexed chains of
>    elementary embeddings:
>    - *ambient-free*: each canonical map `DirectLimit.of` into the limit is
>      an `ElementaryEmbedding` (induction on `BoundedFormula`; the `all`
>      case pulls limit witnesses to a common level via directedness);
>    - *relativized*: if all levels embed elementarily and compatibly into a
>      fixed model `M`, the induced map from the limit to `M` is elementary
>      (via `DirectLimit.lift` + the Tarski–Vaught test).
>    The upstream version should generalize ℕ to a directed order — the
>    induction carries over verbatim.
> 2. **Direct limit cardinality.** `#(DirectLimit G f) = ⨆ i, #(G i)` when
>    the supremum is infinite.
> 3. **Real-closedness of ℝ and of relative algebraic closures.**
>    `IsRealClosed ℝ` (IVT + `Real.sqrt`), a root-closure criterion for
>    subfields, and: the relative algebraic closure of a subfield of `ℝ` is
>    real closed. Is any of this subsumed by in-progress work on
>    `Mathlib.FieldTheory.IsRealClosed` or the ordered-field model theory
>    files?
> 4. **The gap we did *not* close** (long-term target): the real-subfield
>    elementarity consequence of model completeness of RCF. Minimized
>    statement in Mathlib vocabulary, where
>    `LOR := Language.ring`:
>
>    ```lean
>    /-- Every real-closed subfield of ℝ is an elementary substructure
>        (order is ring-definable, so the ring language suffices). -/
>    theorem rcf_subfield_elementary (K : Subfield ℝ)
>        (hK : IsRealClosed K) : Nonempty (K ↪ₑ[Language.ring] ℝ)
>    ```
>
>    The natural route is Robinson's test modeled on the ACF development
>    (`Mathlib.ModelTheory.Algebra.ACF`), but the Łoś–Vaught/categoricity
>    shortcut used for ACF is closed for RCF (unstable, maximal models), so
>    it needs genuine quantifier elimination or existential closedness via
>    sign-change/root-counting. Is anyone working on this?
>
> Happy to split/reshape PRs however maintainers prefer.

---

## PR sequence

| # | Content | Source in this repo | Size | Risk |
|---|---|---|---|---|
| 1 | DLS-based elementary substructures of ℝ at every infinite cardinality `≤ 𝔠` + direct-limit cardinality identity | `ElementaryStrata.exists_elementary_substratum`, `ElemChain.directLimit_card_eq_iSup` | Small | Low — ZFC-pure, self-contained |
| 2 | Ambient-free Tarski–Vaught chain theorem for `Language.DirectLimit` | `ElemChain.ofLevelElem`, `realize_ofLevel_iff`, `directLim_elementarilyEquivalent` | Medium | Low–medium — generalize ℕ-index to directed orders; relation case no longer vacuous outside the ring language |
| 3 | Real-closedness lemmas (after Zulip dedup check) | `Real.isRealClosed`, `isRealClosed_of_forall_root`, `relAlgebraic_isRealClosed` | Medium | Medium — naming/placement decisions with `Mathlib.FieldTheory.IsRealClosed` |
| 4 | RCF subfield elementarity (long-term) | discharges `RCFSubfieldRealElementary` / `RCFModelComplete` | Large | High — follows from QE (Tarski–Seidenberg) or Robinson's test infrastructure |

### Notes per PR

- **PR 1**: `exists_elementary_substratum` is a thin specialization of
  Mathlib's `exists_elementarySubstructure_card_eq`; the upstream-worthy part
  is the packaging for `ℝ` in `Language.ring` together with the subfield
  bridge (`elemSubstratumSubfield`: the carrier of an elementary substructure
  of ℝ is a subfield — inverse-closure by one formula transfer). The
  cardinality identity is independent and belongs in
  `ModelTheory/DirectLimit.lean`.
- **PR 2**: state for `[Nonempty ι] [IsDirected ι] [Nonempty ι]`-style
  directed systems rather than ℕ. The local proof's `all` case uses only
  `DirectLimit.inductionOn`, directedness, and `DirectLimit.of_f`, so it
  generalizes mechanically.
- **PR 3**: check overlap first; `IsRealClosed` is young in Mathlib and the
  maintainers may prefer different normal forms (e.g. stating root closure
  via `Polynomial.roots`).
- **PR 4**: do not attempt as a single PR. Sequence: language/theory of
  ordered fields → RCF axiomatization → existential closedness of RCF
  embeddings (sign changes + IVP) → Robinson's test or QE-grade theorem.
  Discharging `RCFSubfieldRealElementary` turns ICAH Pillar B into a
  `NotCH`-only theorem, matching Pillar A.

---

## What stays local

- The ICAH-specific packaging (`Stratum`, `SizeAwareField`, `ICAHStatement`,
  `ICAHElementary`, the cofinal-family statements specialized to
  intermediate cardinalities under `NotCH`). These are the paper's subject
  matter, not general-purpose library material.
- The `cf(𝔠)` sharpness pair is borderline: the lower bound
  (`cofinal_family_length_lower_bound`) is a generic cofinality fact that
  could upstream if stated for arbitrary sets; flag it in the Zulip thread.
