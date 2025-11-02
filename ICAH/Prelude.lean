import Mathlib

/-!
# Prelude

Simple smoke tests to ensure the environment and Mathlib are available.
-/

-- A tiny evaluation so you see something nontrivial in the editor
#eval (Nat.succ (Nat.succ 1))  -- expect: 3

-- A basic real-number lemma coming from Mathlib
example (x y : ℝ) : x + y = y + x := by
  simpa [add_comm]
