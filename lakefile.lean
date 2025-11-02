import Lake
open Lake DSL

package icah where
  -- Add project-wide Lean options here if desired
  -- leanOptions := #[⟨`autoImplicit, false⟩]

-- Mathlib dependency (branch/tag can be adjusted to match your toolchain)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib ICAH
