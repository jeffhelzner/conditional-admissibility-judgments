/-
# Concrete non-identity `CJTransformation`s

This module constructs three concrete morphisms in the category of
conditional judgments, none of which is the identity. Their existence
discharges Stage B.2 of the diachronic-layer plan: until the morphism
layer has at least one named non-identity arrow, the categorical
scaffolding is empty.

The three transformations exhibit three different ways a morphism can
arise in this framework:

1. **State refinement** (`stateRefinementTransformation`): pulling a
   coarse judgment back along a 2-to-1 surjection of state spaces
   (`refine42 : Fin 4 → Fin 2`). The source judgment lives over the
   *finer* state space; its set algebra is the pullback of the
   coarser powerset, which is exactly what `f_preimage_surjective_on_E`
   demands. `g` is the identity on consequences.

2. **Consequence relabeling** (`relabelTransformation`): pushing a
   judgment forward along a non-identity permutation
   `swap01 : Fin 3 ≃ Fin 3`. `f := id` on states; `g := swap01.symm`
   on consequences.

3. **Identity-on-state restriction-of-acts**
   (`restrictionOfActsTransformation`): `f := id`, `g := id`, with the
   *target* judgment having a strictly smaller act/menu space than
   the source. (Direction is from full to restricted: with identity
   maps, each axiom universally quantifies over the *target* and
   asserts a property of the corresponding *source*.)

The constructions all use a "trivial-choice" pattern, `C e m := m`,
which keeps the focus on the structural fields of `CJTransformation`
rather than on choice arithmetic.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import SetAlgebra
import ConditionalJudgment
import Transformation
import Category

namespace ConditionalChoice

namespace TransformationExamples

universe u v

/-- The full powerset on a type, as a `SetAlgebra`. -/
def fullPowerset (X : Type u) : SetAlgebra X where
  carrier := Set.univ
  univ_mem := trivial
  union_mem := fun _ _ => trivial
  inter_mem := fun _ _ => trivial
  compl_mem := fun _ => trivial

/-- Pullback of a set algebra along a function. -/
def pullbackAlgebra {X : Type u} {X' : Type*} (f : X → X')
    (E' : SetAlgebra X') : SetAlgebra X where
  carrier := { e | ∃ e', e' ∈ E'.carrier ∧ f ⁻¹' e' = e }
  univ_mem := ⟨Set.univ, E'.univ_mem, by ext; simp⟩
  union_mem := by
    rintro s t ⟨s', hs', rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨s' ∪ t', E'.union_mem hs' ht', Set.preimage_union⟩
  inter_mem := by
    rintro s t ⟨s', hs', rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨s' ∩ t', E'.inter_mem hs' ht', Set.preimage_inter⟩
  compl_mem := by
    rintro s ⟨s', hs', rfl⟩
    refine ⟨Set.compl s', E'.compl_mem hs', ?_⟩
    ext x; rfl

/-! ## Example 1: state refinement -/

/-- The collapsing map `0,1 ↦ 0`, `2,3 ↦ 1`. -/
def refine42 : Fin 4 → Fin 2 := fun i => if i.val < 2 then 0 else 1

/-- Constant act on `Fin n` taking value `k : Fin 2`. -/
@[reducible] def constAct (n : ℕ) (k : Fin 2) : Fin n → Fin 2 := fun _ => k

/-- Source judgment over the finer state space `Fin 4`, with set
    algebra equal to the pullback of the powerset on `Fin 2`.
    Defined directly (without going through a helper) so that field
    projections reduce by `rfl`. -/
noncomputable def fineJudgment : ConditionalJudgment (Fin 4) (Fin 2) where
  X_nonempty := ⟨0⟩
  K_nonempty := ⟨0⟩
  E := pullbackAlgebra refine42 (fullPowerset (Fin 2))
  A := ({constAct 4 0, constAct 4 1} : Set (Fin 4 → Fin 2))
  M := ({{constAct 4 0}, {constAct 4 1},
         ({constAct 4 0, constAct 4 1} : Set _)}
          : Set (Set (Fin 4 → Fin 2)))
  C := fun _ m => m
  A_nonempty := ⟨constAct 4 0, Or.inl rfl⟩
  M_nonempty := ⟨{constAct 4 0}, Or.inl rfl⟩
  M_elements_nonempty := by
    intro m hm
    rcases hm with rfl | rfl | rfl
    · exact ⟨constAct 4 0, rfl⟩
    · exact ⟨constAct 4 1, rfl⟩
    · exact ⟨constAct 4 0, Or.inl rfl⟩
  C_in_M := by intro _ _ _ hm; exact hm
  C_subset_menu := by intro _ _ _ _; exact subset_rfl

/-- Target judgment over the coarser state space `Fin 2`. -/
noncomputable def coarseJudgment : ConditionalJudgment (Fin 2) (Fin 2) where
  X_nonempty := ⟨0⟩
  K_nonempty := ⟨0⟩
  E := fullPowerset (Fin 2)
  A := ({constAct 2 0, constAct 2 1} : Set (Fin 2 → Fin 2))
  M := ({{constAct 2 0}, {constAct 2 1},
         ({constAct 2 0, constAct 2 1} : Set _)}
          : Set (Set (Fin 2 → Fin 2)))
  C := fun _ m => m
  A_nonempty := ⟨constAct 2 0, Or.inl rfl⟩
  M_nonempty := ⟨{constAct 2 0}, Or.inl rfl⟩
  M_elements_nonempty := by
    intro m hm
    rcases hm with rfl | rfl | rfl
    · exact ⟨constAct 2 0, rfl⟩
    · exact ⟨constAct 2 1, rfl⟩
    · exact ⟨constAct 2 0, Or.inl rfl⟩
  C_in_M := by intro _ _ _ hm; exact hm
  C_subset_menu := by intro _ _ _ _; exact subset_rfl

/-- Composing a constant target-act with `id ∘ _ ∘ refine42` yields
    the corresponding constant source-act. -/
theorem id_const_refine42 (k : Fin 2) :
    ((id : Fin 2 → Fin 2) ∘ (constAct 2 k) ∘ refine42 : Fin 4 → Fin 2)
      = constAct 4 k := by
  funext _; rfl

private theorem image_const_singleton_refine42 (k : Fin 2) :
    Set.image (fun b' => (id : Fin 2 → Fin 2) ∘ b' ∘ refine42)
      ({constAct 2 k} : Set _) = ({constAct 4 k} : Set _) := by
  ext a
  simp only [Set.mem_image, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨b', rfl, rfl⟩; exact (id_const_refine42 k)
  · rintro rfl; exact ⟨constAct 2 k, rfl, id_const_refine42 k⟩

private theorem image_const_pair_refine42 :
    Set.image (fun b' => (id : Fin 2 → Fin 2) ∘ b' ∘ refine42)
      ({constAct 2 0, constAct 2 1} : Set _) =
        ({constAct 4 0, constAct 4 1} : Set (Fin 4 → Fin 2)) := by
  ext a
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨b', hb', rfl⟩
    rcases hb' with rfl | rfl
    · exact Or.inl (id_const_refine42 0)
    · exact Or.inr (id_const_refine42 1)
  · rintro (rfl | rfl)
    · exact ⟨constAct 2 0, Or.inl rfl, id_const_refine42 0⟩
    · exact ⟨constAct 2 1, Or.inr rfl, id_const_refine42 1⟩

/-- The state-refinement transformation: `f := refine42`, `g := id`. -/
noncomputable def stateRefinementTransformation :
    CJTransformation fineJudgment coarseJudgment where
  f := refine42
  g := id
  f_preimage_surjective_on_E := by
    intro e he
    -- `he : e ∈ fineJudgment.E`, which by definition is the pullback algebra.
    obtain ⟨e', he', hpre⟩ := he
    exact ⟨e', he', hpre⟩
  preimage_preserves_E := by
    intro e' _
    -- `e'` is in `coarseJudgment.E = fullPowerset (Fin 2)`, so trivially in.
    -- The preimage is in the pullback algebra by construction.
    exact ⟨e', trivial, rfl⟩
  alternatives_closed := by
    intro a' ha'
    -- ha' : a' ∈ {constAct 2 0, constAct 2 1}
    rcases ha' with rfl | rfl
    · rw [id_const_refine42 0]; exact Or.inl rfl
    · rw [id_const_refine42 1]; exact Or.inr rfl
  menus_closed := by
    intro m' hm'
    rcases hm' with rfl | rfl | rfl
    · rw [image_const_singleton_refine42 0]; exact Or.inl rfl
    · rw [image_const_singleton_refine42 1]; exact Or.inr (Or.inl rfl)
    · rw [image_const_pair_refine42]; exact Or.inr (Or.inr rfl)
  choice_preserved := by
    intro _ _ _ _ a' ha'
    -- `coarseJudgment.C e' m' = m'`, so `ha' : a' ∈ m'`.
    -- Goal: `g ∘ a' ∘ f ∈ fineJudgment.C (f ⁻¹' e') (image ... m') = image ... m'`.
    exact ⟨a', ha', rfl⟩

/-- **Corollary (state refinement).** The transformation is genuinely
    non-identity: its `f`-component collapses two distinct states. -/
theorem stateRefinementTransformation_collapses :
    stateRefinementTransformation.f 0 = stateRefinementTransformation.f 1 := by
  decide

/-! ## Example 2: consequence relabeling -/

/-- The non-trivial permutation of `Fin 3` swapping `0` and `1`. -/
def swap01 : Fin 3 ≃ Fin 3 :=
  { toFun := fun i =>
      if i.val = 0 then 1 else if i.val = 1 then 0 else i
    invFun := fun i =>
      if i.val = 0 then 1 else if i.val = 1 then 0 else i
    left_inv := by intro i; fin_cases i <;> rfl
    right_inv := by intro i; fin_cases i <;> rfl }

/-- Constant `Fin 1 → Fin 3` act with value `k`. -/
@[reducible] def constAct₁ (k : Fin 3) : Fin 1 → Fin 3 := fun _ => k

/-- Source judgment over `(Fin 1, Fin 3)`. -/
noncomputable def baseJudgment : ConditionalJudgment (Fin 1) (Fin 3) where
  X_nonempty := ⟨0⟩
  K_nonempty := ⟨0⟩
  E := fullPowerset (Fin 1)
  A := ({constAct₁ 0, constAct₁ 1, constAct₁ 2} : Set (Fin 1 → Fin 3))
  M := ({{constAct₁ 0}, {constAct₁ 1}, {constAct₁ 2},
         ({constAct₁ 0, constAct₁ 1, constAct₁ 2} : Set _)}
          : Set (Set (Fin 1 → Fin 3)))
  C := fun _ m => m
  A_nonempty := ⟨constAct₁ 0, Or.inl rfl⟩
  M_nonempty := ⟨{constAct₁ 0}, Or.inl rfl⟩
  M_elements_nonempty := by
    intro m hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact ⟨constAct₁ 0, rfl⟩
    · exact ⟨constAct₁ 1, rfl⟩
    · exact ⟨constAct₁ 2, rfl⟩
    · exact ⟨constAct₁ 0, Or.inl rfl⟩
  C_in_M := by intro _ _ _ hm; exact hm
  C_subset_menu := by intro _ _ _ _; exact subset_rfl

/-- The relabeled judgment: acts of the form `constAct₁ (swap01 k)`. -/
noncomputable def relabeledJudgment : ConditionalJudgment (Fin 1) (Fin 3) where
  X_nonempty := ⟨0⟩
  K_nonempty := ⟨0⟩
  E := fullPowerset (Fin 1)
  A := ({constAct₁ (swap01 0), constAct₁ (swap01 1), constAct₁ (swap01 2)}
        : Set (Fin 1 → Fin 3))
  M := ({{constAct₁ (swap01 0)}, {constAct₁ (swap01 1)}, {constAct₁ (swap01 2)},
         ({constAct₁ (swap01 0), constAct₁ (swap01 1), constAct₁ (swap01 2)}
           : Set _)} : Set (Set (Fin 1 → Fin 3)))
  C := fun _ m => m
  A_nonempty := ⟨constAct₁ (swap01 0), Or.inl rfl⟩
  M_nonempty := ⟨{constAct₁ (swap01 0)}, Or.inl rfl⟩
  M_elements_nonempty := by
    intro m hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact ⟨constAct₁ (swap01 0), rfl⟩
    · exact ⟨constAct₁ (swap01 1), rfl⟩
    · exact ⟨constAct₁ (swap01 2), rfl⟩
    · exact ⟨constAct₁ (swap01 0), Or.inl rfl⟩
  C_in_M := by intro _ _ _ hm; exact hm
  C_subset_menu := by intro _ _ _ _; exact subset_rfl

/-- Pulling back `constAct₁ (swap01 k)` through `swap01.symm` gives
    `constAct₁ k`. -/
theorem swap_const_pullback (k : Fin 3) :
    (swap01.symm ∘ constAct₁ (swap01 k) ∘ id : Fin 1 → Fin 3)
      = constAct₁ k := by
  funext _; show swap01.symm (swap01 k) = k
  exact swap01.symm_apply_apply k

private theorem image_swap_singleton (k : Fin 3) :
    Set.image (fun b' => swap01.symm ∘ b' ∘ id)
      ({constAct₁ (swap01 k)} : Set (Fin 1 → Fin 3))
        = ({constAct₁ k} : Set _) := by
  ext a
  simp only [Set.mem_image, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨b, rfl, rfl⟩; exact swap_const_pullback k
  · rintro rfl; exact ⟨constAct₁ (swap01 k), rfl, swap_const_pullback k⟩

private theorem image_swap_full :
    Set.image (fun b' => swap01.symm ∘ b' ∘ id)
      ({constAct₁ (swap01 0), constAct₁ (swap01 1), constAct₁ (swap01 2)}
        : Set (Fin 1 → Fin 3)) =
      ({constAct₁ 0, constAct₁ 1, constAct₁ 2} : Set _) := by
  ext a
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨b, hb, rfl⟩
    rcases hb with rfl | rfl | rfl
    · exact Or.inl (swap_const_pullback 0)
    · exact Or.inr (Or.inl (swap_const_pullback 1))
    · exact Or.inr (Or.inr (swap_const_pullback 2))
  · rintro (rfl | rfl | rfl)
    · exact ⟨constAct₁ (swap01 0), Or.inl rfl, swap_const_pullback 0⟩
    · exact ⟨constAct₁ (swap01 1), Or.inr (Or.inl rfl), swap_const_pullback 1⟩
    · exact ⟨constAct₁ (swap01 2), Or.inr (Or.inr rfl), swap_const_pullback 2⟩

/-- The relabeling transformation: `f := id`, `g := swap01.symm`. -/
noncomputable def relabelTransformation :
    CJTransformation baseJudgment relabeledJudgment where
  f := id
  g := swap01.symm
  f_preimage_surjective_on_E := by
    intro e _
    exact ⟨e, trivial, Set.preimage_id⟩
  preimage_preserves_E := by intro _ _; trivial
  alternatives_closed := by
    intro a' ha'
    rcases ha' with rfl | rfl | rfl
    · rw [swap_const_pullback 0]; exact Or.inl rfl
    · rw [swap_const_pullback 1]; exact Or.inr (Or.inl rfl)
    · rw [swap_const_pullback 2]; exact Or.inr (Or.inr rfl)
  menus_closed := by
    intro m' hm'
    rcases hm' with rfl | rfl | rfl | rfl
    · rw [image_swap_singleton 0]; exact Or.inl rfl
    · rw [image_swap_singleton 1]; exact Or.inr (Or.inl rfl)
    · rw [image_swap_singleton 2]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [image_swap_full]; exact Or.inr (Or.inr (Or.inr rfl))
  choice_preserved := by
    intro _ _ _ _ a' ha'
    exact ⟨a', ha', rfl⟩

/-- **Corollary (relabeling).** The transformation has a non-identity
    consequence map: `swap01.symm 0 = 1`. -/
theorem relabelTransformation_g_ne_id :
    relabelTransformation.g (0 : Fin 3) ≠ (0 : Fin 3) := by
  show swap01.symm 0 ≠ 0
  decide

/-! ## Example 3: identity-on-state restriction-of-acts -/

/-- Source judgment with both constant acts. -/
noncomputable def fullActJudgment : ConditionalJudgment (Fin 1) (Fin 2) where
  X_nonempty := ⟨0⟩
  K_nonempty := ⟨0⟩
  E := fullPowerset (Fin 1)
  A := ({(fun _ : Fin 1 => (0 : Fin 2)), fun _ => 1} : Set (Fin 1 → Fin 2))
  M := ({{(fun _ : Fin 1 => (0 : Fin 2))}, {fun _ => 1},
         ({(fun _ : Fin 1 => (0 : Fin 2)), fun _ => 1} : Set _)}
          : Set (Set (Fin 1 → Fin 2)))
  C := fun _ m => m
  A_nonempty := ⟨fun _ => 0, Or.inl rfl⟩
  M_nonempty := ⟨{fun _ => 0}, Or.inl rfl⟩
  M_elements_nonempty := by
    intro m hm
    rcases hm with rfl | rfl | rfl
    · exact ⟨fun _ => 0, rfl⟩
    · exact ⟨fun _ => 1, rfl⟩
    · exact ⟨fun _ => 0, Or.inl rfl⟩
  C_in_M := by intro _ _ _ hm; exact hm
  C_subset_menu := by intro _ _ _ _; exact subset_rfl

/-- Target judgment restricted to the single constant act `const 0`. -/
noncomputable def restrictedActJudgment : ConditionalJudgment (Fin 1) (Fin 2) where
  X_nonempty := ⟨0⟩
  K_nonempty := ⟨0⟩
  E := fullPowerset (Fin 1)
  A := ({(fun _ : Fin 1 => (0 : Fin 2))} : Set (Fin 1 → Fin 2))
  M := ({{(fun _ : Fin 1 => (0 : Fin 2))}} : Set (Set (Fin 1 → Fin 2)))
  C := fun _ m => m
  A_nonempty := ⟨fun _ => 0, rfl⟩
  M_nonempty := ⟨{fun _ => 0}, rfl⟩
  M_elements_nonempty := by
    intro m hm
    rcases hm with rfl
    exact ⟨fun _ => 0, rfl⟩
  C_in_M := by intro _ _ _ hm; exact hm
  C_subset_menu := by intro _ _ _ _; exact subset_rfl

/-- The restriction-of-acts transformation: `f := id`, `g := id`. -/
noncomputable def restrictionOfActsTransformation :
    CJTransformation fullActJudgment restrictedActJudgment where
  f := id
  g := id
  f_preimage_surjective_on_E := by
    intro e _
    exact ⟨e, trivial, Set.preimage_id⟩
  preimage_preserves_E := by intro _ _; trivial
  alternatives_closed := by
    intro a' ha'
    -- ha' : a' ∈ {fun _ => 0}
    rcases ha' with rfl
    -- Goal: id ∘ (fun _ => 0) ∘ id ∈ fullActJudgment.A
    show (fun _ : Fin 1 => (0 : Fin 2)) ∈ _
    exact Or.inl rfl
  menus_closed := by
    intro m' hm'
    rcases hm' with rfl
    have him : Set.image
        (fun b' => (id : Fin 2 → Fin 2) ∘ b' ∘ (id : Fin 1 → Fin 1))
        ({fun _ : Fin 1 => (0 : Fin 2)} : Set _) =
        ({fun _ => 0} : Set _) := by
      ext a
      simp only [Set.mem_image, Set.mem_singleton_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨b, rfl, rfl⟩; rfl
      · rintro rfl; exact ⟨fun _ => 0, rfl, rfl⟩
    rw [him]
    exact Or.inl rfl
  choice_preserved := by
    intro _ _ _ _ a' ha'
    exact ⟨a', ha', rfl⟩

/-- **Corollary (restriction).** The target judgment's act space is a
    strict subset of the source's. -/
theorem restrictionOfActsTransformation_target_strictly_smaller :
    restrictedActJudgment.A ⊆ fullActJudgment.A ∧
      restrictedActJudgment.A ≠ fullActJudgment.A := by
  refine ⟨?_, ?_⟩
  · intro a ha
    rcases ha with rfl
    exact Or.inl rfl
  · intro h
    have h1 : (fun _ : Fin 1 => (1 : Fin 2)) ∈ fullActJudgment.A :=
      Or.inr rfl
    rw [← h] at h1
    rcases h1 with h1
    have := congrFun h1 0
    simp at this

end TransformationExamples

end ConditionalChoice
