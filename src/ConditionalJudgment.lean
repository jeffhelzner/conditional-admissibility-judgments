-- Expected utility is a finite sum over the consequence space K (Fintype K).
-- The state space X is unconstrained, allowing infinite (even uncountable) state spaces.

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import SetAlgebra

namespace ConditionalChoice

universe u v

/-- A conditional judgment of admissibility over state space X
    and consequence space K. The choice function C maps an element of
    the set algebra E and a menu (a set of alternatives) to the subset
    of the menu that the decision maker judges admissible. -/
structure ConditionalJudgment (X : Type u) (K : Type v) where
  /-- Nonemptiness of the state space. -/
  X_nonempty : Nonempty X
  /-- Nonemptiness of the consequence space. -/
  K_nonempty : Nonempty K
  /-- The Boolean algebra of subsets of X representing things the agent
      could learn. -/
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

/-- Expected utility of alternative `a` given `e` with `p(e) ≠ 0`.
    Computed as a finite sum over the consequence space K:
    `EU(p,u,e,a) = (1 / p(e)) * Σ_{k ∈ K} u(k) * p(a⁻¹'{k} ∩ e)`.

    Consequences not in the range of `a` contribute zero (their level sets are
    empty, so the probability term vanishes). This requires only `Fintype K`,
    not `Fintype X`, allowing the state space to be infinite.

    The `hlevel` argument witnesses that each level set `a⁻¹'{k} ∩ e` belongs
    to the set algebra, which is needed to apply the probability measure. -/
noncomputable def expected_utility {X : Type u} {K : Type v}
    [Fintype K] [DecidableEq K]
    {E : SetAlgebra X} (p : Fap E) (u : K → ℝ)
    (e : { s // s ∈ E.carrier }) (_he : p.p e ≠ 0)
    (a : X → K)
    (hlevel : ∀ k, a ⁻¹' {k} ∩ e.val ∈ E.carrier) : ℝ :=
  (1 / p.p e) *
    Finset.univ.sum (fun k =>
      u k * p.p ⟨a ⁻¹' {k} ∩ e.val, hlevel k⟩)

/-- The expected utility of a constant alternative `fun _ => k` equals `u k`
    (when `p.p e ≠ 0`). -/
theorem expected_utility_const {X : Type u} {K : Type v}
    [Fintype K] [DecidableEq K]
    {E : SetAlgebra X} (p : Fap E) (u : K → ℝ)
    (e : { s // s ∈ E.carrier }) (he : p.p e ≠ 0)
    (k : K)
    (hlevel : ∀ k', (fun (_ : X) => k) ⁻¹' {k'} ∩ e.val ∈ E.carrier) :
    expected_utility p u e he (fun _ => k) hlevel = u k := by
  simp only [expected_utility]
  -- For k' ≠ k the level set is empty; for k' = k it equals e
  have hpre_eq : (fun (_ : X) => k) ⁻¹' {k} ∩ e.val = e.val := by ext x; simp
  have hpre_ne : ∀ k', k' ≠ k → (fun (_ : X) => k) ⁻¹' {k'} ∩ e.val = ∅ := by
    intro k' hk'; ext x; simp [Ne.symm hk']
  -- The sum reduces to the single k-th term
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (fun k' _ hk' => by
    have : (⟨(fun (_ : X) => k) ⁻¹' {k'} ∩ e.val, hlevel k'⟩ : { s // s ∈ E.carrier }) =
        ⟨∅, E.empty_mem⟩ := Subtype.ext (hpre_ne k' hk')
    rw [this, p.p_empty, mul_zero])]
  have hsub : (⟨(fun (_ : X) => k) ⁻¹' {k} ∩ e.val, hlevel k⟩ : { s // s ∈ E.carrier }) =
      ⟨e.val, e.prop⟩ := Subtype.ext hpre_eq
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
    for each non-null element of the set algebra. -/
def HasEURepresentation {X : Type u} {K : Type v} [Fintype K] [DecidableEq K]
    (χ : ConditionalJudgment X K) : Prop :=
  ∃ (p : Fap χ.E) (u : K → ℝ),
    ∀ (e : { s // s ∈ χ.E.carrier }),
      (he : p.p e ≠ 0) →
      ∀ m ∈ χ.M,
        ∀ a ∈ m,
          (ha : ∀ k, a ⁻¹' {k} ∩ e.val ∈ χ.E.carrier) →
          (a ∈ χ.C e.val m ↔
            ∀ a' ∈ m,
              (ha' : ∀ k, a' ⁻¹' {k} ∩ e.val ∈ χ.E.carrier) →
              expected_utility p u e he a' ha' ≤
                expected_utility p u e he a ha)

end ConditionalChoice
