-- Expected utility is a finite sum over the (finite) range of the act on the
-- supposition `e`. Neither the consequence space `K` nor the state space `X`
-- is required to be finite; the finiteness assumption is localized as a
-- per-act hypothesis `(a '' e.val).Finite`. This is the form needed for
-- cardinal-utility / vNM extensions where `K` is closed under mixtures and
-- is therefore typically infinite.

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import SetAlgebra

namespace ConditionalChoice

universe u v

/-- A conditional judgment of admissibility over state space X
    and consequence space K. The choice function C maps a supposition
    (an element of the set algebra E) and a menu (a set of alternatives)
    to the subset of the menu that the decision maker judges admissible
    under that supposition. -/
structure ConditionalJudgment (X : Type u) (K : Type v) where
  /-- Nonemptiness of the state space. -/
  X_nonempty : Nonempty X
  /-- Nonemptiness of the consequence space. -/
  K_nonempty : Nonempty K
  /-- The Boolean algebra of subsets of X representing propositions the
      agent can suppose. Conditioning `C e m` is suppositional reasoning
      within the synchronic state `χ`; genuine learning that breaks out
      of `χ` is modeled by a `CJTransformation` to a different structure. -/
  E : SetAlgebra X
  /-- The set of available alternatives (acts mapping states to consequences). -/
  A : Set (X → K)
  /-- The set of available menus (sets of alternatives). -/
  M : Set (Set (X → K))
  /-- The conditional choice function: C e m is the set of alternatives in m
      that the decision maker judges admissible given e. -/
  C : Set X → Set (X → K) → Set (X → K)
  /-- The set of alternatives is nonempty. -/
  A_nonempty : A.Nonempty
  /-- The set of menus is nonempty. -/
  M_nonempty : M.Nonempty
  /-- Every menu is nonempty. -/
  M_elements_nonempty : ∀ m ∈ M, Set.Nonempty m
  /-- The choice from any valid e ∈ E and menu is itself a valid menu. -/
  C_in_M : ∀ e m, e ∈ E → m ∈ M → C e m ∈ M
  /-- The choice from any valid e ∈ E and menu is a subset of that menu. -/
  C_subset_menu : ∀ e m, e ∈ E → m ∈ M → C e m ⊆ m

/-- Wrapper restating `C_subset_menu`. -/
theorem ConditionalJudgment.choice_subset_menu {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e : Set X) (m : Set (X → K))
    (he : e ∈ χ.E) (hm : m ∈ χ.M) : χ.C e m ⊆ m :=
  χ.C_subset_menu e m he hm

/-- Wrapper restating `C_in_M`. -/
theorem ConditionalJudgment.choice_mem_menu {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e : Set X) (m : Set (X → K))
    (he : e ∈ χ.E) (hm : m ∈ χ.M) : χ.C e m ∈ χ.M :=
  χ.C_in_M e m he hm

/-! ### Finitely-Additive Probability -/

/-- A finitely-additive probability measure on a set algebra. The measure
    assigns a real-valued probability to each member of the algebra,
    satisfying nonnegativity, normalization (p(univ) = 1), and finite
    additivity for disjoint sets. -/
structure Fap {X : Type u} (E : SetAlgebra X) where
  p : { s // s ∈ E.carrier } → ℝ
  nonneg : ∀ s, 0 ≤ p s
  p_univ : p ⟨Set.univ, E.univ_mem⟩ = 1
  additive : ∀ (s t : { s // s ∈ E.carrier }),
    Disjoint s.val t.val →
    p ⟨s.val ∪ t.val, E.union_mem s.prop t.prop⟩ = p s + p t

/-- The probability of the empty set is zero (derived from additivity and normalization). -/
theorem Fap.p_empty {X : Type u} {E : SetAlgebra X} (p : Fap E) :
    p.p ⟨∅, E.empty_mem⟩ = 0 := by
  have h := p.additive ⟨∅, E.empty_mem⟩ ⟨Set.univ, E.univ_mem⟩ disjoint_bot_left
  have hunion : (⟨∅ ∪ Set.univ, E.union_mem E.empty_mem E.univ_mem⟩ : { s // s ∈ E.carrier }) =
    ⟨Set.univ, E.univ_mem⟩ := Subtype.ext (Set.empty_union _)
  rw [hunion] at h
  linarith [p.p_univ]

/-! ### Expected Utility -/

/-- Expected utility of alternative `a` given supposition `e` with `p(e) ≠ 0`.
    Computed as a finite sum over the (finite) range of `a` on `e.val`:
    `EU(p,u,e,a) = (1 / p(e)) * Σ_{k ∈ a''e} u(k) * p(a⁻¹'{k} ∩ e)`.

    The consequence space `K` is *not* required to be finite. Finiteness is
    instead a per-act hypothesis `hfin : (a '' e.val).Finite`, asserting that
    `a` takes only finitely many values on `e.val` (i.e., `a` has finite
    support relative to `e`). Consequences outside `a '' e.val` would
    contribute zero (their level sets intersected with `e` are empty), so
    summing only over `a '' e.val` yields the same value as summing over a
    larger Finset.

    The `hlevel` argument witnesses that each level set `a⁻¹'{k} ∩ e` belongs
    to the set algebra, which is needed to apply the probability measure. -/
noncomputable def expected_utility {X : Type u} {K : Type v}
    {E : SetAlgebra X} (p : Fap E) (u : K → ℝ)
    (e : { s // s ∈ E.carrier }) (_he : p.p e ≠ 0)
    (a : X → K)
    (hfin : (a '' e.val).Finite)
    (hlevel : ∀ k, a ⁻¹' {k} ∩ e.val ∈ E.carrier) : ℝ :=
  (1 / p.p e) *
    hfin.toFinset.sum (fun k =>
      u k * p.p ⟨a ⁻¹' {k} ∩ e.val, hlevel k⟩)

/-- A constant alternative `fun _ => k` has finite range on any set. -/
theorem image_const_finite {X : Type u} {K : Type v} (k : K) (s : Set X) :
    ((fun (_ : X) => k) '' s).Finite :=
  (Set.finite_singleton k).subset (by
    rintro k' ⟨x, _, rfl⟩; exact Set.mem_singleton _)

/-- The expected utility of a constant alternative `fun _ => k` equals `u k`
    (when `p.p e ≠ 0`). -/
theorem expected_utility_const {X : Type u} {K : Type v}
    {E : SetAlgebra X} (p : Fap E) (u : K → ℝ)
    (e : { s // s ∈ E.carrier }) (he : p.p e ≠ 0)
    (k : K)
    (hfin : ((fun (_ : X) => k) '' e.val).Finite)
    (hlevel : ∀ k', (fun (_ : X) => k) ⁻¹' {k'} ∩ e.val ∈ E.carrier) :
    expected_utility p u e he (fun _ => k) hfin hlevel = u k := by
  -- `p e ≠ 0` forces `e.val` to be nonempty (else `p e = p_empty = 0`).
  have hne : e.val.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply he
    have hsub : e = (⟨e.val, e.prop⟩ : { s // s ∈ E.carrier }) := by cases e; rfl
    rw [hsub]
    have hpe : (⟨e.val, e.prop⟩ : { s // s ∈ E.carrier }) =
        ⟨∅, E.empty_mem⟩ := Subtype.ext hempty
    rw [hpe]; exact p.p_empty
  -- The image of a constant on a nonempty set is `{k}`.
  have himg : (fun (_ : X) => k) '' e.val = {k} := by
    ext k'
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, rfl⟩; rfl
    · rintro rfl; exact ⟨hne.choose, hne.choose_spec, rfl⟩
  -- The level set at `k` equals `e.val`.
  have hpre_eq : (fun (_ : X) => k) ⁻¹' {k} ∩ e.val = e.val := by ext x; simp
  -- `hfin.toFinset = {k}`.
  have htoFinset : hfin.toFinset = ({k} : Finset K) := by
    ext k'
    rw [Set.Finite.mem_toFinset, himg, Finset.mem_singleton, Set.mem_singleton_iff]
  simp only [expected_utility, htoFinset, Finset.sum_singleton]
  have hsub : (⟨(fun (_ : X) => k) ⁻¹' {k} ∩ e.val, hlevel k⟩ :
      { s // s ∈ E.carrier }) = ⟨e.val, e.prop⟩ := Subtype.ext hpre_eq
  rw [hsub, show (⟨e.val, e.prop⟩ : { s // s ∈ E.carrier }) = e from by cases e; rfl]
  field_simp

/-! ### Helper Definitions -/

@[simp] def preimageSet {X : Type u} {X' : Type*} (f : X → X') (s : Set X') : Set X :=
  f ⁻¹' s

@[simp] def composeAlternative {X : Type u} {K : Type v} {X' : Type*} {K' : Type*}
    (g : K' → K) (a' : X' → K') (f : X → X') : X → K :=
  g ∘ a' ∘ f

@[simp] def transformMenu {X : Type u} {K : Type v} {X' : Type*} {K' : Type*}
    (g : K' → K) (f : X → X') (m' : Set (X' → K')) : Set (X → K) :=
  Set.image (fun b' => g ∘ b' ∘ f) m'

/-! ### HasEURepresentation -/

/-- A conditional judgment has an expected-utility representation if there exist
    a finitely-additive probability and a utility function such that the choice
    function selects exactly the EU-maximizing alternatives from each menu,
    for each non-null supposition. EU is computed via the finite-support form
    of `expected_utility`; the per-act hypotheses `hfin`, `hfin'` witness that
    each act takes only finitely many values on `e.val`. -/
def HasEURepresentation {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) : Prop :=
  ∃ (p : Fap χ.E) (u : K → ℝ),
    ∀ (e : { s // s ∈ χ.E.carrier }),
      (he : p.p e ≠ 0) →
      ∀ m ∈ χ.M,
        ∀ a ∈ m,
          (hfin : (a '' e.val).Finite) →
          (ha : ∀ k, a ⁻¹' {k} ∩ e.val ∈ χ.E.carrier) →
          (a ∈ χ.C e.val m ↔
            ∀ a' ∈ m,
              (hfin' : (a' '' e.val).Finite) →
              (ha' : ∀ k, a' ⁻¹' {k} ∩ e.val ∈ χ.E.carrier) →
              expected_utility p u e he a' hfin' ha' ≤
                expected_utility p u e he a hfin ha)

end ConditionalChoice
