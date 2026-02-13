import Lake
open Lake DSL

package formalDistribution where
  -- Package configuration

@[default_target]
lean_lib FormalDistribution where
  roots := #[`FormalDistribution]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
