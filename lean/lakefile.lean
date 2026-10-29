import Lake
open Lake DSL

package albertsonCollins where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"

@[default_target]
lean_lib AlbertsonCollins where
