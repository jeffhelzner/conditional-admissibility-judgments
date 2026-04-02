import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import SetAlgebra
import ConditionalJudgment

namespace ConditionalChoice

universe u v u' v'

/-- A transformation (morphism) between two conditional judgments.
    Viewed categorically, each ConditionalJudgment is an object and
    CJTransformation is a morphism. The map `f : X → X'` pulls back epistemic
    states (coarse-to-fine); the map `g : K' → K` pushes forward consequences. -/
structure CJTransformation
    {X : Type u} {K : Type v} {X' : Type u'} {K' : Type v'}
    (χ : ConditionalJudgment X K) (χ' : ConditionalJudgment X' K') where
  /-- Map on state spaces. -/
  f : X → X'
  /-- Map on consequence spaces (contravariant direction). -/
  g : K' → K
  /-- Every epistemic state of χ arises as the preimage of some
      epistemic state of χ'. Weaker than global surjectivity of f. -/
  f_preimage_surjective_on_E :
    ∀ e, e ∈ χ.E → ∃ e', e' ∈ χ'.E ∧ f ⁻¹' e' = e
  /-- Preimages of χ'-epistemic states lie in χ's set algebra. -/
  preimage_preserves_E :
    ∀ e', e' ∈ χ'.E → f ⁻¹' e' ∈ χ.E
  /-- Composing with g and f maps χ'-alternatives into χ-alternatives. -/
  alternatives_closed :
    ∀ a' ∈ χ'.A, (g ∘ a' ∘ f) ∈ χ.A
  /-- Transforming a χ'-menu produces a χ-menu. -/
  menus_closed :
    ∀ m' ∈ χ'.M, Set.image (fun b' => g ∘ b' ∘ f) m' ∈ χ.M
  /-- Chosen alternatives transform to chosen alternatives. -/
  choice_preserved :
    ∀ e', e' ∈ χ'.E →
    ∀ m', m' ∈ χ'.M →
    ∀ a', a' ∈ χ'.C e' m' →
      (g ∘ a' ∘ f) ∈ χ.C (f ⁻¹' e') (Set.image (fun b' => g ∘ b' ∘ f) m')

/-- An alternative transformed by a CJTransformation belongs to χ.A. -/
theorem CJTransformation.transform_alternative_mem
    {X : Type u} {K : Type v} {X' : Type u'} {K' : Type v'}
    {χ : ConditionalJudgment X K} {χ' : ConditionalJudgment X' K'}
    (T : CJTransformation χ χ') (a' : X' → K') (ha' : a' ∈ χ'.A) :
    (T.g ∘ a' ∘ T.f) ∈ χ.A :=
  T.alternatives_closed a' ha'

/-- A menu transformed by a CJTransformation belongs to χ.M. -/
theorem CJTransformation.transform_menu_mem
    {X : Type u} {K : Type v} {X' : Type u'} {K' : Type v'}
    {χ : ConditionalJudgment X K} {χ' : ConditionalJudgment X' K'}
    (T : CJTransformation χ χ') (m' : Set (X' → K')) (hm' : m' ∈ χ'.M) :
    Set.image (fun b' => T.g ∘ b' ∘ T.f) m' ∈ χ.M :=
  T.menus_closed m' hm'

/-- A chosen alternative transformed by a CJTransformation belongs to
    the transformed choice set. -/
theorem CJTransformation.transform_choice_mem
    {X : Type u} {K : Type v} {X' : Type u'} {K' : Type v'}
    {χ : ConditionalJudgment X K} {χ' : ConditionalJudgment X' K'}
    (T : CJTransformation χ χ')
    (e' : Set X') (he' : e' ∈ χ'.E)
    (m' : Set (X' → K')) (hm' : m' ∈ χ'.M)
    (a' : X' → K') (ha' : a' ∈ χ'.C e' m') :
    (T.g ∘ a' ∘ T.f) ∈ χ.C (T.f ⁻¹' e') (Set.image (fun b' => T.g ∘ b' ∘ T.f) m') :=
  T.choice_preserved e' he' m' hm' a' ha'

end ConditionalChoice
