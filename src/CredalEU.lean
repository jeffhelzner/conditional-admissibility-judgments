/-
# Credal-set EU representation

A `ConditionalJudgment` admits a *credal-set EU representation* on
event `e` if there is a non-empty family `P` of finitely-additive
priors (each non-null on `e`) and a single utility `u : K → ℝ` such
that, on every menu, the choice set is exactly the set of acts that
some `p ∈ P` makes EU-maximal.

This is the synchronic capstone of the SEU/Levi axis: it strictly
generalizes the single-prior EU representation of
`HasEURepresentation`, and feeds directly into the multi-relation
revealed-preference layer (`MultiRepresentable`) via the family of
EU-induced weak orders `R_p`, one per `p ∈ P`.

The headline content:

* `credalRfam_refl`, `credalRfam_trans` — for every `p ∈ H.P`, the
  EU-induced relation `credalRfam H p hp` is reflexive on `χ.A` and
  transitive through `χ.A`.
* `hasCredalEURepresentation_implies_multiRepresentable` — under
  `MenuClosure`, the credal-set EU representation entails
  `MultiRepresentable χ e.val { R | ∃ p ∈ H.P, R = credalRfam H p hp }`
  (the analogue of `HasEURepresentation → WARP`).
* `singleton_credalEU_iff_eu_at` — when `P = {p₀}`, the credal-set
  representation collapses to the single-prior EU representation at
  `e` (with prior `p₀` and the same utility `u`).
-/

import MultiRepresentable
import EUImpliesWARP

namespace ConditionalChoice

universe u v

/-! ## The credal-set EU representation -/

/-- A credal-set EU representation of `χ` on event `e`: a non-empty
    family `P` of priors (each non-null on `e`) and a utility `u` such
    that, on every menu, the choice equals the EU-admissible set with
    respect to `P`. The finite-range and level-set witnesses for acts
    in `χ.A` are bundled into the structure so the EU formula applies
    uniformly throughout. -/
structure HasCredalEURepresentation
    {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : { s // s ∈ χ.E.carrier }) where
  /-- The credal set: a family of finitely-additive priors. -/
  P : Set (Fap χ.E)
  /-- The utility on consequences. -/
  u : K → ℝ
  /-- The credal set is non-empty. -/
  P_nonempty : P.Nonempty
  /-- Every act in `χ.A` has finite range on `e`. -/
  finite_acts : ∀ a ∈ χ.A, (a '' e.val).Finite
  /-- Every level set of every act in `χ.A` lies in `χ.E.carrier`. -/
  level_in_E : ∀ a ∈ χ.A, ∀ k, a ⁻¹' {k} ∩ e.val ∈ χ.E.carrier
  /-- Each prior is non-null on `e`. -/
  pos_on_e : ∀ p ∈ P, p.p e ≠ 0
  /-- The choice equals the credal-set EU-admissible set on every
      menu. -/
  represented :
    ∀ m ∈ χ.M, ∀ a ∈ m,
      (a ∈ χ.C e.val m ↔
        ∃ p, ∃ hp : p ∈ P,
          ∀ b ∈ m, ∀ (ha : a ∈ χ.A) (hb : b ∈ χ.A),
            expected_utility p u e (pos_on_e p hp) b
                (finite_acts b hb) (level_in_E b hb) ≤
              expected_utility p u e (pos_on_e p hp) a
                (finite_acts a ha) (level_in_E a ha))

/-! ## The EU-induced relation under each prior -/

/-- The EU-induced weak order on `(X → K)` under prior `p ∈ H.P`.
    Off `χ.A` it is *vacuously* true (no membership witness available),
    so it is globally reflexive; on `χ.A` it is the EU comparison. -/
def credalRfam {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    {e : { s // s ∈ χ.E.carrier }}
    (H : HasCredalEURepresentation χ e)
    (p : Fap χ.E) (hp : p ∈ H.P) :
    (X → K) → (X → K) → Prop :=
  fun a b =>
    ∀ (ha : a ∈ χ.A) (hb : b ∈ χ.A),
      expected_utility p H.u e (H.pos_on_e p hp) b
          (H.finite_acts b hb) (H.level_in_E b hb) ≤
        expected_utility p H.u e (H.pos_on_e p hp) a
          (H.finite_acts a ha) (H.level_in_E a ha)

/-- `credalRfam` is globally reflexive: every act is `credalRfam`-related
    to itself, vacuously off `χ.A` and by `le_refl` on `χ.A`. -/
theorem credalRfam_refl {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    {e : { s // s ∈ χ.E.carrier }}
    {H : HasCredalEURepresentation χ e}
    {p : Fap χ.E} {hp : p ∈ H.P}
    (a : X → K) : credalRfam H p hp a a := by
  intro _ _; exact le_refl _

/-- `credalRfam` is transitive *through* `χ.A`: if the intermediate
    member belongs to `χ.A`, then `R a b → R b c → R a c`. -/
theorem credalRfam_trans {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    {e : { s // s ∈ χ.E.carrier }}
    {H : HasCredalEURepresentation χ e}
    {p : Fap χ.E} {hp : p ∈ H.P}
    {a b c : X → K} (hb : b ∈ χ.A) :
    credalRfam H p hp a b → credalRfam H p hp b c →
      credalRfam H p hp a c := by
  intro hab hbc ha hc
  exact le_trans (hbc hb hc) (hab ha hb)

/-! ## The credal family of EU-induced relations -/

/-- The set of EU-induced weak orders, one per prior in `H.P`. This is
    the family `Rℛ` against which the credal-set representation is
    multi-rationalizable. -/
def credalRfamilySet {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    {e : { s // s ∈ χ.E.carrier }}
    (H : HasCredalEURepresentation χ e) :
    Set ((X → K) → (X → K) → Prop) :=
  { R | ∃ p, ∃ hp : p ∈ H.P, R = credalRfam H p hp }

/-! ## The bridge to multi-representability -/

/-- **Bridging theorem.** A credal-set EU representation entails
    multi-representability against the family of EU-induced relations.
    This is the analogue of `HasEURepresentation → WARP`. -/
theorem hasCredalEURepresentation_implies_multiRepresentable
    {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    {e : { s // s ∈ χ.E.carrier }}
    (H : HasCredalEURepresentation χ e) :
    MultiRepresentable χ e.val (credalRfamilySet H) := by
  intro m hm
  ext a
  simp only [multiMaxSet, credalRfamilySet, Set.mem_setOf_eq]
  constructor
  · intro ha_C
    have ham : a ∈ m := χ.choice_subset_menu e.val m e.prop hm ha_C
    obtain ⟨p, hp, hmax⟩ := (H.represented m hm a ham).mp ha_C
    refine ⟨ham, credalRfam H p hp, ⟨p, hp, rfl⟩, ?_⟩
    intro b hb ha hbA
    exact hmax b hb ha hbA
  · rintro ⟨ham, R, ⟨p, hp, rfl⟩, hmax⟩
    apply (H.represented m hm a ham).mpr
    refine ⟨p, hp, ?_⟩
    intro b hb ha hbA
    exact hmax b hb ha hbA

/-! ## The single-prior collapse -/

/-- The single-prior EU representation localized to a fixed event `e`,
    in the same per-act-witness style as `credalRfam`. This matches the
    shape of `HasEURepresentation` but is parameterized by `e`, `p`, and
    `u`, and bundles the well-formedness witnesses. -/
structure HasEURepresentationAt
    {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : { s // s ∈ χ.E.carrier }) (p : Fap χ.E) (u : K → ℝ) where
  pos_on_e : p.p e ≠ 0
  finite_acts : ∀ a ∈ χ.A, (a '' e.val).Finite
  level_in_E : ∀ a ∈ χ.A, ∀ k, a ⁻¹' {k} ∩ e.val ∈ χ.E.carrier
  represented :
    ∀ m ∈ χ.M, ∀ a ∈ m,
      (a ∈ χ.C e.val m ↔
        ∀ b ∈ m, ∀ (ha : a ∈ χ.A) (hb : b ∈ χ.A),
          expected_utility p u e pos_on_e b
              (finite_acts b hb) (level_in_E b hb) ≤
            expected_utility p u e pos_on_e a
              (finite_acts a ha) (level_in_E a ha))

/-- **Singleton credal collapse.** If `H : HasCredalEURepresentation χ e`
    has a singleton credal set `H.P = {p₀}`, then `H` is equivalent to
    a single-prior EU representation at `e` with prior `p₀` and utility
    `H.u`. -/
def hasCredalEURepresentation_of_singleton_eu
    {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    {e : { s // s ∈ χ.E.carrier }} {p₀ : Fap χ.E} {u : K → ℝ}
    (S : HasEURepresentationAt χ e p₀ u) :
    HasCredalEURepresentation χ e where
  P := ({p₀} : Set _)
  u := u
  P_nonempty := ⟨p₀, rfl⟩
  finite_acts := S.finite_acts
  level_in_E := S.level_in_E
  pos_on_e := by
    intro p hp; rw [Set.mem_singleton_iff] at hp; subst hp; exact S.pos_on_e
  represented := by
    intro m hm a ham
    rw [S.represented m hm a ham]
    constructor
    · intro hmax
      refine ⟨p₀, rfl, ?_⟩
      intro b hb ha hbA
      exact hmax b hb ha hbA
    · rintro ⟨p, hp, hmax⟩
      rw [Set.mem_singleton_iff] at hp; subst hp
      intro b hb ha hbA
      exact hmax b hb ha hbA

/-- The converse: from a credal-set representation with `H.P = {p₀}`,
    extract a single-prior EU representation at `e`. -/
def singleton_credalEU_to_eu
    {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    {e : { s // s ∈ χ.E.carrier }}
    (H : HasCredalEURepresentation χ e)
    {p₀ : Fap χ.E} (hP : H.P = ({p₀} : Set _)) :
    HasEURepresentationAt χ e p₀ H.u where
  pos_on_e := H.pos_on_e p₀ (by rw [hP]; rfl)
  finite_acts := H.finite_acts
  level_in_E := H.level_in_E
  represented := by
    intro m hm a ham
    rw [H.represented m hm a ham]
    constructor
    · rintro ⟨p, hp, hmax⟩
      rw [hP, Set.mem_singleton_iff] at hp; subst hp
      intro b hb ha hbA
      exact hmax b hb ha hbA
    · intro hmax
      refine ⟨p₀, by rw [hP]; rfl, ?_⟩
      intro b hb ha hbA
      exact hmax b hb ha hbA

end ConditionalChoice
