import CAJ

/-!
# Smoke test: a concrete decision context and judgment

Instantiates a tiny concrete context (states and acts are `Bool`, powerset
algebra, the single menu `univ`) and checks that the top judgment on it
satisfies WARP, α, β, γ — confirming the Phase 1 definitions are nonvacuous.
-/

namespace CAJTest

open CAJ

/-- The powerset algebra on any type. -/
def powersetAlgebra (X : Type*) : SetAlgebra X where
  carrier := Set.univ
  univ_mem := trivial
  union_mem _ _ := trivial
  compl_mem _ := trivial

/-- A tiny concrete decision context. -/
def tinyCtx : DecisionContext where
  State := Bool
  Act := Bool
  alg := powersetAlgebra Bool
  Menus := {Set.univ}
  menus_nonempty := by rintro m rfl; exact ⟨true, trivial⟩
  menus_inhabited := ⟨Set.univ, rfl⟩

example : (⊤ : AdmissibilityJudgment tinyCtx).WARP :=
  AdmissibilityJudgment.top_warp

example : (⊤ : AdmissibilityJudgment tinyCtx).SenAlpha :=
  AdmissibilityJudgment.WARP.senAlpha _ AdmissibilityJudgment.top_warp

example : (⊤ : AdmissibilityJudgment tinyCtx).SenBeta :=
  AdmissibilityJudgment.WARP.senBeta _ AdmissibilityJudgment.top_warp

example : (⊤ : AdmissibilityJudgment tinyCtx).SenGamma :=
  AdmissibilityJudgment.top_senGamma

/-- The top judgment is live everywhere. -/
example (e : tinyCtx.Event) : (⊤ : AdmissibilityJudgment tinyCtx).Live e :=
  fun m => tinyCtx.menu_nonempty m

end CAJTest
