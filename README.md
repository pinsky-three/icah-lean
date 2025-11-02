# ICAH Lean Starter

A minimal Lean 4 + Mathlib project scaffold for formalising the **Intermediate‑Cardinality Arithmetic Hypothesis (ICAH)**.

## Quick start

1) Install Lean toolchain manager **elan** (https://leanprover-community.github.io/get_started.html).
2) In this folder run:
   ```bash
   elan toolchain install leanprover/lean4:stable
   lake update
   lake exe cache get   # fetch mathlib precompiled cache (optional but recommended)
   lake build
   ```
3) Open the folder in VS Code with the Lean 4 extension. The file `ICAH/Prelude.lean` should compile.

## Project layout

- `ICAH/Prelude.lean` — smoke tests; confirms Mathlib is live.
- `ICAH/SizeAwareField.lean` — a small wrapper `SizeAwareField` (carrier + designated cardinal).
- `ICAH/Strata.lean` — placeholder definition of definability strata `R[≤ n]` with cardinal bounds.
- `ICAH/Main.lean` — a formal statement stub `ICAHStatement` to refine as you progress.
- `ICAH.lean` — aggregates the submodules.

## Notes

- The Mathlib git ref in `lakefile.lean` points at the default branch. If your toolchain needs a specific tag, edit the `require mathlib ... @ "<tag>"` line accordingly.
- Replace the axioms / placeholders with real definitions and proofs as your development matures.

Happy proving!
