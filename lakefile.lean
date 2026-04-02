import Lake
open Lake DSL

package conditionalAdmissibility where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib ConditionalChoice where
  srcDir := "src"
  roots := #[`SetAlgebra, `ConditionalJudgment, `Transformation, `Category]

lean_lib Examples where
  srcDir := "test"
  roots := #[`Examples]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
