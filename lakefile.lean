import Lake
open Lake DSL

package conditionalAdmissibility where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib ConditionalChoice where
  srcDir := "src"
  roots := #[`SetAlgebra, `ConditionalJudgment, `Transformation, `Category, `RevealedPreference, `ConstantActs, `ConstActInvariance, `EUImpliesWARP, `MultiRepresentable, `StrictIndiffIncomp, `EAdmissible, `CredalEU, `Transformations.Examples, `Conditionalization]

lean_lib Examples where
  srcDir := "test"
  roots := #[`Examples, `RevealedPreferenceExamples, `Fin3RepNotWARP, `Levi2PriorExample]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
