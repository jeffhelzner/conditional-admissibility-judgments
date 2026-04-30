import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import SetAlgebra
import ConditionalJudgment
import Transformation

namespace ConditionalChoice

universe u v u' v' u'' v''

/-- The identity transformation on a conditional judgment. Uses `f := id` and
    `g := id`; all fields follow from basic properties of `id` and preimage. -/
def CJTransformation.id {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) : CJTransformation χ χ where
  f := _root_.id
  g := _root_.id
  f_preimage_surjective_on_E := by
    intro e he
    exact ⟨e, he, Set.preimage_id⟩
  preimage_preserves_E := by
    intro e' he'
    rw [Set.preimage_id]
    exact he'
  alternatives_closed := by
    intro a' ha'
    simp
    exact ha'
  menus_closed := by
    intro m' hm'
    have : Set.image (fun b' => _root_.id ∘ b' ∘ _root_.id) m' = m' := by
      ext x; simp
    rw [this]
    exact hm'
  choice_preserved := by
    intro e' he' m' hm' a' ha'
    have hf : _root_.id ⁻¹' e' = e' := Set.preimage_id
    have hm : Set.image (fun b' => _root_.id ∘ b' ∘ _root_.id) m' = m' := by
      ext x; simp
    rw [hf, hm]
    simpa using ha'

/-- Composition of two CJTransformations. Given `T : χ → χ'` and `T' : χ' → χ''`,
    produces `T.comp T' : χ → χ''` with `f := T'.f ∘ T.f` and `g := T.g ∘ T'.g`
    (note the contravariant direction of g). -/
def CJTransformation.comp {X : Type u} {K : Type v}
    {X' : Type u'} {K' : Type v'}
    {X'' : Type u''} {K'' : Type v''}
    {χ : ConditionalJudgment X K}
    {χ' : ConditionalJudgment X' K'}
    {χ'' : ConditionalJudgment X'' K''}
    (T : CJTransformation χ χ') (T' : CJTransformation χ' χ'') :
    CJTransformation χ χ'' where
  f := T'.f ∘ T.f
  g := T.g ∘ T'.g
  f_preimage_surjective_on_E := by
    intro e he
    -- First find e' in χ'.E such that T.f ⁻¹' e' = e
    obtain ⟨e', he', hfe'⟩ := T.f_preimage_surjective_on_E e he
    -- Then find e'' in χ''.E such that T'.f ⁻¹' e'' = e'
    obtain ⟨e'', he'', hfe''⟩ := T'.f_preimage_surjective_on_E e' he'
    refine ⟨e'', he'', ?_⟩
    rw [Set.preimage_comp, hfe'', hfe']
  preimage_preserves_E := by
    intro e'' he''
    rw [Set.preimage_comp]
    exact T.preimage_preserves_E _ (T'.preimage_preserves_E e'' he'')
  alternatives_closed := by
    intro a'' ha''
    -- g ∘ a'' ∘ f = T.g ∘ T'.g ∘ a'' ∘ T'.f ∘ T.f
    -- = T.g ∘ (T'.g ∘ a'' ∘ T'.f) ∘ T.f
    have h1 : T'.g ∘ a'' ∘ T'.f ∈ χ'.A := T'.alternatives_closed a'' ha''
    have key : (T.g ∘ T'.g) ∘ a'' ∘ (T'.f ∘ T.f) = T.g ∘ (T'.g ∘ a'' ∘ T'.f) ∘ T.f := by
      ext x; simp [Function.comp]
    rw [key]
    exact T.alternatives_closed _ h1
  menus_closed := by
    intro m'' hm''
    have h1 : Set.image (fun b'' => T'.g ∘ b'' ∘ T'.f) m'' ∈ χ'.M :=
      T'.menus_closed m'' hm''
    have key : Set.image (fun b'' => (T.g ∘ T'.g) ∘ b'' ∘ (T'.f ∘ T.f)) m'' =
        Set.image (fun b' => T.g ∘ b' ∘ T.f)
          (Set.image (fun b'' => T'.g ∘ b'' ∘ T'.f) m'') := by
      ext x
      simp only [Set.mem_image]
      constructor
      · rintro ⟨a'', ha'', rfl⟩
        refine ⟨T'.g ∘ a'' ∘ T'.f, ⟨a'', ha'', rfl⟩, ?_⟩
        ext y; simp [Function.comp]
      · rintro ⟨b', ⟨a'', ha'', rfl⟩, rfl⟩
        refine ⟨a'', ha'', ?_⟩
        ext y; simp [Function.comp]
    rw [key]
    exact T.menus_closed _ h1
  choice_preserved := by
    intro e'' he'' m'' hm'' a'' ha''
    -- We need to show:
    -- (T.g ∘ T'.g) ∘ a'' ∘ (T'.f ∘ T.f) ∈
    --   χ.C ((T'.f ∘ T.f) ⁻¹' e'') (image (fun b'' => (T.g ∘ T'.g) ∘ b'' ∘ (T'.f ∘ T.f)) m'')
    -- Step 1: T' maps a'' to χ'.C
    have h1 := T'.choice_preserved e'' he'' m'' hm'' a'' ha''
    -- h1 : T'.g ∘ a'' ∘ T'.f ∈ χ'.C (T'.f ⁻¹' e'') (image (fun b'' => T'.g ∘ b'' ∘ T'.f) m'')
    -- Step 2: T maps the result to χ.C
    have h2 := T.choice_preserved (T'.f ⁻¹' e'') (T'.preimage_preserves_E e'' he'')
      (Set.image (fun b'' => T'.g ∘ b'' ∘ T'.f) m'') (T'.menus_closed m'' hm'')
      (T'.g ∘ a'' ∘ T'.f) h1
    -- h2 : T.g ∘ (T'.g ∘ a'' ∘ T'.f) ∘ T.f ∈
    --   χ.C (T.f ⁻¹' (T'.f ⁻¹' e''))
    --     (image (fun b' => T.g ∘ b' ∘ T.f) (image (fun b'' => T'.g ∘ b'' ∘ T'.f) m''))
    -- Now rewrite to match the composed form
    have hf_eq : (T'.f ∘ T.f) ⁻¹' e'' = T.f ⁻¹' (T'.f ⁻¹' e'') := Set.preimage_comp
    have hcomp_eq : T.g ∘ (T'.g ∘ a'' ∘ T'.f) ∘ T.f = (T.g ∘ T'.g) ∘ a'' ∘ (T'.f ∘ T.f) := by
      ext x; simp [Function.comp]
    have himg_eq : Set.image (fun b' => T.g ∘ b' ∘ T.f)
        (Set.image (fun b'' => T'.g ∘ b'' ∘ T'.f) m'') =
        Set.image (fun b'' => (T.g ∘ T'.g) ∘ b'' ∘ (T'.f ∘ T.f)) m'' := by
      ext x
      simp only [Set.mem_image]
      constructor
      · rintro ⟨b', ⟨a'', ha'', rfl⟩, rfl⟩
        refine ⟨a'', ha'', ?_⟩
        ext y; simp [Function.comp]
      · rintro ⟨a'', ha'', rfl⟩
        refine ⟨T'.g ∘ a'' ∘ T'.f, ⟨a'', ha'', rfl⟩, ?_⟩
        ext y; simp [Function.comp]
    rw [hf_eq, ← hcomp_eq, ← himg_eq]
    exact h2

/-! ## Category laws

The three category-axiom equalities for `CJTransformation`. Together
with the existing `id` and `comp` definitions, these promote the
morphism scaffolding to an actual category (over a fixed pair of
universes/types). The proofs are extensionality on the `f` and `g`
fields followed by `Function.id_comp` / `Function.comp_id`
/ `Function.comp_assoc`. -/

/-- Left-identity law: `(id χ).comp T = T`. -/
@[simp] theorem CJTransformation.id_comp
    {X : Type u} {K : Type v} {X' : Type u'} {K' : Type v'}
    {χ : ConditionalJudgment X K} {χ' : ConditionalJudgment X' K'}
    (T : CJTransformation χ χ') :
    (CJTransformation.id χ).comp T = T := by
  ext <;> rfl

/-- Right-identity law: `T.comp (id χ') = T`. -/
@[simp] theorem CJTransformation.comp_id
    {X : Type u} {K : Type v} {X' : Type u'} {K' : Type v'}
    {χ : ConditionalJudgment X K} {χ' : ConditionalJudgment X' K'}
    (T : CJTransformation χ χ') :
    T.comp (CJTransformation.id χ') = T := by
  ext <;> rfl

/-- Associativity of composition: `(T.comp T').comp T'' = T.comp (T'.comp T'')`. -/
theorem CJTransformation.assoc
    {X : Type u} {K : Type v}
    {X' : Type u'} {K' : Type v'}
    {X'' : Type u''} {K'' : Type v''}
    {X''' : Type*} {K''' : Type*}
    {χ : ConditionalJudgment X K}
    {χ' : ConditionalJudgment X' K'}
    {χ'' : ConditionalJudgment X'' K''}
    {χ''' : ConditionalJudgment X''' K'''}
    (T : CJTransformation χ χ')
    (T' : CJTransformation χ' χ'')
    (T'' : CJTransformation χ'' χ''') :
    (T.comp T').comp T'' = T.comp (T'.comp T'') := by
  ext <;> rfl

end ConditionalChoice
