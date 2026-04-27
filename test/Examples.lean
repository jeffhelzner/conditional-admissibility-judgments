import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import SetAlgebra
import ConditionalJudgment
import Transformation

namespace ConditionalChoice

-- Classical reasoning is used in this test file only, to inspect membership
-- in Set-valued elements of the algebra when constructing concrete Fap witnesses.
-- The core library (src/) remains classical-free.
open Classical

/-! ### Bool Example -/

/-- The full powerset of `Bool` as a `SetAlgebra`. -/
def bool_E : SetAlgebra Bool where
  carrier := Set.univ
  univ_mem := Set.mem_univ _
  union_mem := fun _ _ => Set.mem_univ _
  inter_mem := fun _ _ => Set.mem_univ _
  compl_mem := fun _ => Set.mem_univ _

/-- A concrete conditional judgment on `Bool`:
    - E: full powerset
    - A: {const_true, const_false}
    - M: {{const_false}, {const_true, const_false}}
    - C e m = {const_false} for all e, m -/
def bool_example : ConditionalJudgment Bool Bool where
  X_nonempty := ⟨true⟩
  K_nonempty := ⟨true⟩
  E := bool_E
  A := {fun _ => true, fun _ => false}
  M := {{fun _ => false}, {fun _ => true, fun _ => false}}
  C := fun _ _ => {fun _ => false}
  A_nonempty := ⟨fun _ => true, Set.mem_insert _ _⟩
  M_nonempty := ⟨{fun _ => false}, Set.mem_insert _ _⟩
  M_elements_nonempty := by
    intro m hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · exact ⟨fun _ => false, Set.mem_singleton _⟩
    · exact ⟨fun _ => true, Set.mem_insert _ _⟩
  C_in_M := by
    intro e m _ _
    -- C e m = {fun _ => false} which is the first element of M
    show {fun _ => false} ∈ ({{fun _ => false}, {fun _ => true, fun _ => false}} : Set (Set (Bool → Bool)))
    exact Set.mem_insert _ _
  C_subset_menu := by
    intro e m _he hm a ha
    simp only [Set.mem_singleton_iff] at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · exact ha ▸ Set.mem_singleton _
    · subst ha; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

/-- Explicit verification that `C_in_M` holds for `bool_example`. -/
example : ∀ e m, e ∈ bool_example.E → m ∈ bool_example.M → bool_example.C e m ∈ bool_example.M :=
  bool_example.C_in_M

/-- Explicit verification that `C_subset_menu` holds for `bool_example`. -/
example : ∀ e m, e ∈ bool_example.E → m ∈ bool_example.M → bool_example.C e m ⊆ m :=
  bool_example.C_subset_menu

/-! ### Transformation Example -/

/-- Identity transformation on `bool_example`. -/
def bool_transformation : CJTransformation bool_example bool_example where
  f := id
  g := id
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
    have : Set.image (fun b' => id ∘ b' ∘ id) m' = m' := by
      ext x; simp
    rw [this]
    exact hm'
  choice_preserved := by
    intro e' he' m' hm' a' ha'
    have hf : id ⁻¹' e' = e' := Set.preimage_id
    have hm : Set.image (fun b' => id ∘ b' ∘ id) m' = m' := by
      ext x; simp
    rw [hf, hm]
    simpa using ha'

/-- Explicit verification that `choice_preserved` holds for `bool_transformation`. -/
example : ∀ e', e' ∈ bool_example.E →
    ∀ m', m' ∈ bool_example.M →
    ∀ a', a' ∈ bool_example.C e' m' →
      (bool_transformation.g ∘ a' ∘ bool_transformation.f) ∈
        bool_example.C (bool_transformation.f ⁻¹' e')
          (Set.image (fun b' => bool_transformation.g ∘ b' ∘ bool_transformation.f) m') :=
  bool_transformation.choice_preserved

/-! ### Representation Example -/

/-- Uniform finitely-additive probability on the full powerset of `Bool`. -/
noncomputable def bool_p : Fap bool_E where
  p := fun s =>
    if true ∈ s.val ∧ false ∈ s.val then 1
    else if true ∈ s.val then 1/2
    else if false ∈ s.val then 1/2
    else 0
  nonneg := by
    intro s
    split_ifs <;> norm_num
  p_univ := by
    simp
  additive := by
    intro s t hdisj
    by_cases hts : true ∈ s.val <;> by_cases hfs : false ∈ s.val <;>
      by_cases htt : true ∈ t.val <;> by_cases hft : false ∈ t.val <;>
      simp_all [Set.mem_union, Set.disjoint_left] <;> norm_num

/-- Utility function: u false = 1, u true = 0. This makes const_false
    the EU-maximizer, matching the choice function C e m = {const_false}. -/
noncomputable def bool_u : Bool → ℝ
  | false => 1
  | true => 0

/-- The Bool example has an expected-utility representation with the uniform
    probability `bool_p` and utility `bool_u`. -/
theorem bool_representation : HasEURepresentation bool_example := by
  refine ⟨bool_p, bool_u, ?_⟩
  intro e he m hm a ham hfin hlevel
  -- C e m = {fun _ => false} for all e, m in bool_example
  -- M = {{fun _ => false}, {fun _ => true, fun _ => false}}
  -- All alternatives are constant, so EU = u k by expected_utility_const
  constructor
  · -- Forward: a ∈ C e.val m → a is EU-maximizing
    intro ha_in_C a' ha'_in_m ha'_fin ha'_level
    -- a ∈ C e.val m means a = fun _ => false
    change a ∈ ({fun _ => false} : Set (Bool → Bool)) at ha_in_C
    rw [Set.mem_singleton_iff] at ha_in_C
    -- EU of a = fun _ => false is u false = 1
    -- EU of any a' ∈ m is ≤ 1 (since a' is either const_false or const_true)
    -- m is either {const_false} or {const_true, const_false}
    change m ∈ ({{fun _ => false}, {fun (_ : Bool) => true, fun _ => false}} : Set (Set (Bool → Bool))) at hm
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · -- m = {const_false}, a' ∈ m means a' = const_false
      rw [Set.mem_singleton_iff] at ha'_in_m
      subst ha_in_C; subst ha'_in_m
      -- Both are const_false, EU equal
      exact le_refl _
    · -- m = {const_true, const_false}, a' is either const_true or const_false
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'_in_m
      subst ha_in_C
      rcases ha'_in_m with rfl | rfl
      · -- a' = const_true: EU(const_true) ≤ EU(const_false)
        have h1 := expected_utility_const bool_p bool_u e he true ha'_fin ha'_level
        have h2 := expected_utility_const bool_p bool_u e he false hfin hlevel
        calc expected_utility bool_p bool_u e he (fun x => true) ha'_fin ha'_level
            = bool_u true := h1
          _ = 0 := rfl
          _ ≤ 1 := by norm_num
          _ = bool_u false := rfl
          _ = expected_utility bool_p bool_u e he (fun x => false) hfin hlevel := h2.symm
      · -- a' = const_false: EU(const_false) ≤ EU(const_false)
        exact le_refl _
  · -- Backward: a is EU-maximizing → a ∈ C e.val m
    intro hmax
    -- We need: a ∈ {fun _ => false}, i.e., a = fun _ => false
    change a ∈ ({fun _ => false} : Set (Bool → Bool))
    rw [Set.mem_singleton_iff]
    -- a ∈ m, and a is EU-maximizing. We show a must be const_false.
    change m ∈ ({{fun _ => false}, {fun (_ : Bool) => true, fun _ => false}} : Set (Set (Bool → Bool))) at hm
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · -- m = {const_false}, a ∈ m means a = const_false
      rw [Set.mem_singleton_iff] at ham
      exact ham
    · -- m = {const_true, const_false}, a ∈ m means a = const_true or const_false
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ham
      rcases ham with rfl | rfl
      · -- a = const_true. But then EU(const_true) = 0 and EU(const_false) = 1,
        -- so const_false has higher EU, contradicting a being maximal.
        exfalso
        have h_false_in : (fun (_ : Bool) => false) ∈ ({fun (_ : Bool) => true, fun _ => false} : Set (Bool → Bool)) :=
          Set.mem_insert_of_mem _ (Set.mem_singleton _)
        have hfalse_fin : ((fun (_ : Bool) => false) '' e.val).Finite :=
          image_const_finite false _
        have hfalse_level : ∀ k, (fun (_ : Bool) => false) ⁻¹' {k} ∩ e.val ∈ bool_example.E.carrier := by
          intro k; exact Set.mem_univ _
        have := hmax (fun _ => false) h_false_in hfalse_fin hfalse_level
        have h1 := expected_utility_const bool_p bool_u e he true hfin hlevel
        have h2 := expected_utility_const bool_p bool_u e he false hfalse_fin hfalse_level
        -- this : EU(const_false) ≤ EU(const_true), i.e., 1 ≤ 0
        have : bool_u false ≤ bool_u true := by
          have := h2 ▸ h1 ▸ this
          exact this
        simp [bool_u] at this
        linarith
      · -- a = const_false, which is what we want
        rfl

end ConditionalChoice
