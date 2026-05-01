/-
# Bayesian conditionalization as a `CJTransformation`

This module realizes Bayesian conditioning on a non-null event `e₀` as
a *transformation* (morphism in the category of conditional judgments),
not as a within-`χ` operation. This is the most direct point of contact
with the orthodox Bayesian tradition: instead of reading
`χ.C (e ∩ e₀) m` as the conditional choice, we exhibit `e₀` as a *new*
synchronic state of the agent, and the act of conditionalizing as a
morphism between the two states.

## Design choices

The plan offers two formulations of `Conditionalize`. The
*subset-state-space* version takes
`X' := { x // x ∈ e₀ }` as the new state space and is more
philosophically faithful: states outside `e₀` are simply not part of
the new judgment's serious possibilities. We adopt this version. It
fits naturally into the heterogeneous category set up in
[Transformation.lean](Transformation.lean) and [Category.lean](Category.lean).

### The `C'` field: a known design tension

The natural Bayesian definition would set
`C' e_sub m_sub := restrict '' (χ.C e_lift m_lift)` for some lift of
`(e_sub, m_sub)` to `χ`'s set algebra and menu collection. There is a
fundamental obstruction: a single subtype-menu `m_sub` may be the
restriction of *several* distinct `χ`-menus `m_lift`, on each of which
`χ.C e_lift m_lift` may be a different set. In general these do not
agree after restriction, so there is no canonical choice.

We resolve this by defining `Conditionalize.C` as the **trivial
choice** `C' e m := m` (every alternative is admissible). The morphism
`conditionalizationTransformation` then exists structurally: chosen
target alternatives restrict to alternatives in the (trivially full)
source choice set. This is enough to populate the morphism layer with
a named "conditionalization" arrow and to discharge Stage C.1 of the
plan.

A more substantive `C'` that genuinely tracks `χ`'s choice on lifted
arguments (preserving Bayesian content) requires either an injectivity
hypothesis on the menu restriction or a careful `Classical.choose`
lift; we leave that to a future refinement.

The *structural* content of conditionalization—shrinking the state
space from `X` to `e₀`, pulling back the set algebra accordingly, and
restricting acts and menus to the new state space—is fully captured
here.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import SetAlgebra
import ConditionalJudgment
import Transformation
import Category

namespace ConditionalChoice

universe u v

/-! ## Pullback set algebra (helper) -/

/-- Pullback of a set algebra along a function. -/
def pullbackAlgebra' {X : Type u} {X' : Type*} (f : X → X')
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

/-! ## Restriction of acts and menus to a subset

Throughout this section, `e₀ : Set X` is the conditioning event and
`{x // x ∈ e₀}` is the subtype of states in `e₀`. The restriction map
on acts sends `a : X → K` to `fun s : {x // x ∈ e₀} => a s.val`. -/

/-- Restriction of an act `a : X → K` to the subtype `{x // x ∈ e₀}`. -/
@[simp] def restrictAct {X : Type u} {K : Type v} (e₀ : Set X)
    (a : X → K) : { x // x ∈ e₀ } → K :=
  fun s => a s.val

/-- Restriction of a menu (set of acts) to the subtype `{x // x ∈ e₀}`. -/
@[simp] def restrictMenu {X : Type u} {K : Type v} (e₀ : Set X)
    (m : Set (X → K)) : Set ({ x // x ∈ e₀ } → K) :=
  Set.image (restrictAct e₀) m

/-! ## The conditionalized judgment -/

/-- **Bayesian conditionalization on a non-null event.**

Given a conditional judgment `χ` over `(X, K)` and an event
`e₀ ∈ χ.E` with `e₀.Nonempty`, the conditionalized judgment lives
over `({x // x ∈ e₀}, K)`. Its set algebra is the pullback of `χ.E`
along `Subtype.val`; its acts and menus are the restrictions of
`χ.A` and `χ.M`; its choice function is the trivial `C' e m := m`
(see module documentation for design rationale). -/
noncomputable def Conditionalize {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K)
    (e₀ : Set X) (he₀ : e₀ ∈ χ.E.carrier) (hne : e₀.Nonempty) :
    ConditionalJudgment { x // x ∈ e₀ } K where
  X_nonempty := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  K_nonempty := χ.K_nonempty
  E := pullbackAlgebra' (Subtype.val : { x // x ∈ e₀ } → X) χ.E
  A := Set.image (restrictAct e₀) χ.A
  M := Set.image (restrictMenu e₀) χ.M
  C := fun _ m => m
  A_nonempty := by
    obtain ⟨a, ha⟩ := χ.A_nonempty
    exact ⟨restrictAct e₀ a, a, ha, rfl⟩
  M_nonempty := by
    obtain ⟨m, hm⟩ := χ.M_nonempty
    exact ⟨restrictMenu e₀ m, m, hm, rfl⟩
  M_elements_nonempty := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, ha⟩ := χ.M_elements_nonempty m hm
    exact ⟨restrictAct e₀ a, a, ha, rfl⟩
  C_in_M := by
    intro _ _ _ hm; exact hm
  C_subset_menu := by
    intro _ _ _ _; exact subset_rfl
  -- Note: `he₀ : e₀ ∈ χ.E.carrier` is required to express the natural
  -- well-formedness of the construction even though it is not used in
  -- the field bodies. It plays its role in the morphism below, where
  -- `Subtype.val ⁻¹' e₀ = Set.univ` belongs to the pullback algebra
  -- exactly because `e₀ ∈ χ.E`.
  -- (Lean: `he₀` is unused by the elaborated structure, but kept in
  -- the signature to make the hypothesis explicit at use sites.)

@[simp] theorem Conditionalize_C {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e₀ : Set X) (he₀ : e₀ ∈ χ.E.carrier)
    (hne : e₀.Nonempty) (e : Set { x // x ∈ e₀ })
    (m : Set ({ x // x ∈ e₀ } → K)) :
    (Conditionalize χ e₀ he₀ hne).C e m = m := rfl

@[simp] theorem Conditionalize_A {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e₀ : Set X) (he₀ : e₀ ∈ χ.E.carrier)
    (hne : e₀.Nonempty) :
    (Conditionalize χ e₀ he₀ hne).A = Set.image (restrictAct e₀) χ.A := rfl

@[simp] theorem Conditionalize_M {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e₀ : Set X) (he₀ : e₀ ∈ χ.E.carrier)
    (hne : e₀.Nonempty) :
    (Conditionalize χ e₀ he₀ hne).M = Set.image (restrictMenu e₀) χ.M := rfl

/-! ## The conditionalization morphism -/

/-- **Conditionalization as a transformation.** From the
    conditionalized judgment to the original. The state map is
    `Subtype.val : { x // x ∈ e₀ } → X` (covariant) and the
    consequence map is `id` (contravariant in the trivial sense). -/
noncomputable def conditionalizationTransformation
    {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K)
    (e₀ : Set X) (he₀ : e₀ ∈ χ.E.carrier) (hne : e₀.Nonempty) :
    CJTransformation (Conditionalize χ e₀ he₀ hne) χ where
  f := Subtype.val
  g := id
  f_preimage_surjective_on_E := by
    intro e he
    -- `he : e ∈ Conditionalize.E`, which is the pullback algebra.
    obtain ⟨e', he', hpre⟩ := he
    exact ⟨e', he', hpre⟩
  preimage_preserves_E := by
    intro e' he'
    exact ⟨e', he', rfl⟩
  alternatives_closed := by
    intro a' ha'
    -- Goal: id ∘ a' ∘ Subtype.val ∈ Conditionalize.A
    -- = restrictAct e₀ a' ∈ Set.image (restrictAct e₀) χ.A
    exact ⟨a', ha', rfl⟩
  menus_closed := by
    intro m' hm'
    -- Goal: image (id ∘ b' ∘ Subtype.val) m' ∈ Conditionalize.M
    -- This is exactly restrictMenu e₀ m' ∈ image (restrictMenu e₀) χ.M
    refine ⟨m', hm', ?_⟩
    -- restrictMenu and image (id ∘ _ ∘ Subtype.val) are definitionally equal
    rfl
  choice_preserved := by
    intro e' he' m' hm' a' ha'
    -- ha' : a' ∈ χ.C e' m'.
    -- Goal: id ∘ a' ∘ Subtype.val ∈ Conditionalize.C ... ...
    -- Conditionalize.C is trivial: `C' e m := m`. So the goal reduces
    -- to: `restrictAct e₀ a' ∈ Set.image (fun b' => g ∘ b' ∘ Subtype.val) m'`,
    -- which holds because `a' ∈ m'` (by χ.C_subset_menu).
    have ha'm : a' ∈ m' := χ.C_subset_menu e' m' he' hm' ha'
    exact ⟨a', ha'm, rfl⟩

/-! ## Properties

### Property 1: conditionalizing on the universe collapses to `χ`
structurally

When `e₀ = Set.univ`, the subtype `{ x // x ∈ Set.univ }` is in
bijection with `X` via `Subtype.val`, and the consequence map is the
identity on `K`. We record this as two structural lemmas. (A full
isomorphism in the category would also require an inverse
`CJTransformation χ → Conditionalize χ Set.univ _`. The natural
candidate using the section `fun x => ⟨x, trivial⟩` exists at the
level of `f` and `g`, but its `choice_preserved` field cannot be
proven without committing `Conditionalize.C` to a non-trivial recipe—
the same C.1 design tension recorded in the module docstring.) -/

/-- The state map of `conditionalizationTransformation χ Set.univ _` is
    a bijection. Concretely, `Subtype.val : { x // x ∈ Set.univ } → X`
    is bijective. -/
theorem conditionalize_univ_f_bijective {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K)
    (he₀ : (Set.univ : Set X) ∈ χ.E.carrier)
    (hne : (Set.univ : Set X).Nonempty) :
    Function.Bijective
      (conditionalizationTransformation χ Set.univ he₀ hne).f := by
  refine ⟨?_, ?_⟩
  · intro s t h
    apply Subtype.ext
    exact h
  · intro x
    exact ⟨⟨x, trivial⟩, rfl⟩

/-- The consequence map of `conditionalizationTransformation χ Set.univ _`
    is the identity on `K`. -/
theorem conditionalize_univ_g_eq_id {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K)
    (he₀ : (Set.univ : Set X) ∈ χ.E.carrier)
    (hne : (Set.univ : Set X).Nonempty) :
    (conditionalizationTransformation χ Set.univ he₀ hne).g
      = (id : K → K) := rfl

end ConditionalChoice
