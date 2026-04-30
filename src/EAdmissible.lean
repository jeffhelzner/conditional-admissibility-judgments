/-
# E-admissibility as a named predicate

Levi's E-admissibility predicate is the workhorse of the
credal-set / imprecise-probability tradition. An act `a` is
*E-admissible* from a menu `m` against a family `Rℛ` of preference
relations iff `a ∈ m` and *some* `R ∈ Rℛ` makes `a` `R`-maximal in
`m`.

This module names that predicate as a first-class object, separate
from the revealed-preference predicate `MultiRepresentable`. It is
extensionally identical to `multiMaxSet` (defined in
`MultiRepresentable.lean`), but receives its own name so theorems
that quantify over E-admissibility can be stated directly.

The key theorems:

* `EAdmissible_subset_menu` — E-admissibility is a sub-menu predicate.
* `EAdmissible_singleton` — the singleton menu is its own
  E-admissible set.
* `eAdmissible_eq_maxSet_of_singleton` — E-admissibility against a
  singleton family `{R}` collapses to ordinary `R`-maximization.
* `multiRepresentable_iff_C_eq_eAdmissible` — `MultiRepresentable` is
  precisely the claim that the choice function `C` *is*
  E-admissibility relative to `Rℛ`.
-/

import MultiRepresentable

namespace ConditionalChoice

universe u v

/-- The set of E-admissible alternatives in `m` against the family
    `Rℛ`: those `a ∈ m` such that some `R ∈ Rℛ` makes `a` `R`-maximal
    in `m`. Extensionally equal to `multiMaxSet`. -/
def EAdmissible {X : Type u} {K : Type v}
    (Rℛ : Set ((X → K) → (X → K) → Prop))
    (m : Set (X → K)) : Set (X → K) :=
  { a | a ∈ m ∧ ∃ R ∈ Rℛ, ∀ b ∈ m, R a b }

/-- `EAdmissible` and `multiMaxSet` are definitionally the same set. -/
theorem eAdmissible_eq_multiMaxSet {X : Type u} {K : Type v}
    (Rℛ : Set ((X → K) → (X → K) → Prop)) (m : Set (X → K)) :
    EAdmissible Rℛ m = multiMaxSet Rℛ m := rfl

/-- E-admissible alternatives are members of the menu. -/
theorem eAdmissible_subset_menu {X : Type u} {K : Type v}
    (Rℛ : Set ((X → K) → (X → K) → Prop)) (m : Set (X → K)) :
    EAdmissible Rℛ m ⊆ m := by
  rintro a ⟨ha, _⟩; exact ha

/-- A singleton menu `{a}` is its own E-admissible set, provided some
    `R ∈ Rℛ` is reflexive at `a`. -/
theorem eAdmissible_singleton {X : Type u} {K : Type v}
    {Rℛ : Set ((X → K) → (X → K) → Prop)} {a : X → K}
    (hne : Rℛ.Nonempty) (hrefl : ∀ R ∈ Rℛ, R a a) :
    EAdmissible Rℛ ({a} : Set _) = ({a} : Set _) := by
  ext b
  simp only [EAdmissible, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hb, _⟩; exact hb
  · rintro rfl
    obtain ⟨R, hR⟩ := hne
    refine ⟨rfl, R, hR, ?_⟩
    intro b hb
    subst hb
    exact hrefl R hR

/-- E-admissibility against a singleton family `{R}` collapses to
    ordinary `R`-maximization. -/
theorem eAdmissible_eq_maxSet_of_singleton {X : Type u} {K : Type v}
    (R : (X → K) → (X → K) → Prop) (m : Set (X → K)) :
    EAdmissible ({R} : Set _) m = { a | a ∈ m ∧ ∀ b ∈ m, R a b } := by
  rw [eAdmissible_eq_multiMaxSet, multiMaxSet_singleton]

/-- `MultiRepresentable χ e Rℛ` is exactly the claim that the choice
    function on event `e` *is* E-admissibility against `Rℛ`. -/
theorem multiRepresentable_iff_C_eq_eAdmissible {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e : Set X)
    (Rℛ : Set ((X → K) → (X → K) → Prop)) :
    MultiRepresentable χ e Rℛ ↔ ∀ m ∈ χ.M, χ.C e m = EAdmissible Rℛ m :=
  Iff.rfl

end ConditionalChoice
