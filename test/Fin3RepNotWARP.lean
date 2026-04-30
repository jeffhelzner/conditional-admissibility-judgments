/-
# A `Fin 3` Counterexample: Representable without WARP

This file constructs a concrete `ConditionalJudgment Unit (Fin 3)`
that is `Representable` on its (unique non-trivial) event yet whose
revealed-preference relation `R_e` is *not* transitive — and hence,
by the sharp equivalence proved in `RevealedPreference.lean`, also
fails WARP.

The construction follows §8.4 of
`prompts/PLAN_FOR_REVEALED_PREFERENCE_ON_A.md`, relabelling
`(a, a', b)` as `(act 0, act 1, act 2)`.

## What is and is not proved here

The conceptually meaningful facts about this example are
**representability**, the **direct WARP failure**, and the
**non-transitivity of `R_e`**. All three are established below
without invoking `MenuClosure`; they are independent statements
about `fin3_judgment`, `fin3_C`, and `RevealedPref`.

`MenuClosure fin3_judgment` *also* holds — every singleton, pair,
and triple drawn from `fin3_A` is one of the seven menus in
`fin3_M`, and every menu is a subset of `fin3_A`. Its proof is
rote case analysis (9 unordered pairs, 27 unordered triples) and
is omitted here as a documentation-only fact; it would be needed
only to derive `¬ TransitiveOnAlt` *via* the equivalence theorem
`warpAt_iff_representable_and_transitive`, but here we prove
non-transitivity directly.

## The choice function

With `act k := (fun _ => k) : Unit → Fin 3` for `k : Fin 3`:

* `C({act 0, act 1})        = {act 0, act 1}`,
* `C({act 0, act 2})        = {act 0}`,
* `C({act 1, act 2})        = {act 2}`,
* `C({act 0, act 1, act 2}) = {act 0}`,
* singletons are returned unchanged.
-/

import RevealedPreference
import MultiRepresentable
import StrictIndiffIncomp

namespace ConditionalChoice

open Classical

/-! ## Acts and basic algebraic facts -/

/-- The constant act on `Unit` taking value `k`. -/
@[reducible] def act (k : Fin 3) : Unit → Fin 3 := fun _ => k

theorem act_injective : Function.Injective act := by
  intro i j h
  exact congrArg (· ()) h

theorem act_ne {i j : Fin 3} (h : i ≠ j) : act i ≠ act j :=
  fun heq => h (act_injective heq)

theorem act01_ne : act 0 ≠ act 1 := act_ne (by decide)
theorem act02_ne : act 0 ≠ act 2 := act_ne (by decide)
theorem act12_ne : act 1 ≠ act 2 := act_ne (by decide)
theorem act10_ne : act 1 ≠ act 0 := act_ne (by decide)
theorem act20_ne : act 2 ≠ act 0 := act_ne (by decide)
theorem act21_ne : act 2 ≠ act 1 := act_ne (by decide)

/-! ## The set algebra and alternative space -/

/-- The full powerset of `Unit` as a `SetAlgebra`. -/
def unit_E : SetAlgebra Unit where
  carrier := Set.univ
  univ_mem := trivial
  union_mem := fun _ _ => trivial
  inter_mem := fun _ _ => trivial
  compl_mem := fun _ => trivial

/-- The three alternatives. -/
def fin3_A : Set (Unit → Fin 3) := {act 0, act 1, act 2}

theorem act0_mem_A : act 0 ∈ fin3_A := Or.inl rfl
theorem act1_mem_A : act 1 ∈ fin3_A := Or.inr (Or.inl rfl)
theorem act2_mem_A : act 2 ∈ fin3_A := Or.inr (Or.inr rfl)

/-! ## The set of menus -/

/-- The seven nonempty submenus of `fin3_A`. -/
def fin3_M : Set (Set (Unit → Fin 3)) :=
  { ({act 0} : Set _),
    ({act 1} : Set _),
    ({act 2} : Set _),
    ({act 0, act 1} : Set _),
    ({act 0, act 2} : Set _),
    ({act 1, act 2} : Set _),
    ({act 0, act 1, act 2} : Set _) }

theorem mem_fin3_M_iff (m : Set (Unit → Fin 3)) :
    m ∈ fin3_M ↔
      m = {act 0} ∨ m = {act 1} ∨ m = {act 2} ∨
      m = {act 0, act 1} ∨ m = {act 0, act 2} ∨ m = {act 1, act 2} ∨
      m = {act 0, act 1, act 2} := by
  unfold fin3_M
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

/-! ## The choice function -/

/-- The choice function on `fin3_M`. -/
noncomputable def fin3_C : Set Unit → Set (Unit → Fin 3) → Set (Unit → Fin 3) :=
  fun _ m =>
    if m = ({act 0, act 1, act 2} : Set _) then ({act 0} : Set _)
    else if m = ({act 0, act 2} : Set _) then ({act 0} : Set _)
    else if m = ({act 1, act 2} : Set _) then ({act 2} : Set _)
    else m

/-! ### Distinctness of the seven defining menus -/

private theorem menu_ne :
    ({act 0, act 1} : Set (Unit → Fin 3)) ≠ ({act 0, act 1, act 2} : Set _) ∧
    ({act 0, act 1} : Set (Unit → Fin 3)) ≠ ({act 0, act 2} : Set _) ∧
    ({act 0, act 1} : Set (Unit → Fin 3)) ≠ ({act 1, act 2} : Set _) ∧
    ({act 0, act 2} : Set (Unit → Fin 3)) ≠ ({act 0, act 1, act 2} : Set _) ∧
    ({act 1, act 2} : Set (Unit → Fin 3)) ≠ ({act 0, act 1, act 2} : Set _) ∧
    ({act 1, act 2} : Set (Unit → Fin 3)) ≠ ({act 0, act 2} : Set _) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have : act 2 ∈ ({act 0, act 1} : Set (Unit → Fin 3)) := by
      rw [h]; exact Or.inr (Or.inr rfl)
    rcases this with h | h
    · exact act20_ne h
    · rw [Set.mem_singleton_iff] at h; exact act21_ne h
  · intro h
    have : act 1 ∈ ({act 0, act 2} : Set (Unit → Fin 3)) := by
      rw [← h]; exact Or.inr rfl
    rcases this with h | h
    · exact act10_ne h
    · rw [Set.mem_singleton_iff] at h; exact act12_ne h
  · intro h
    have : act 0 ∈ ({act 1, act 2} : Set (Unit → Fin 3)) := by
      rw [← h]; exact Or.inl rfl
    rcases this with h | h
    · exact act01_ne h
    · rw [Set.mem_singleton_iff] at h; exact act02_ne h
  · intro h
    have : act 1 ∈ ({act 0, act 2} : Set (Unit → Fin 3)) := by
      rw [h]; exact Or.inr (Or.inl rfl)
    rcases this with h | h
    · exact act10_ne h
    · rw [Set.mem_singleton_iff] at h; exact act12_ne h
  · intro h
    have : act 0 ∈ ({act 1, act 2} : Set (Unit → Fin 3)) := by
      rw [h]; exact Or.inl rfl
    rcases this with h | h
    · exact act01_ne h
    · rw [Set.mem_singleton_iff] at h; exact act02_ne h
  · intro h
    have : act 1 ∈ ({act 0, act 2} : Set (Unit → Fin 3)) := by
      rw [← h]; exact Or.inl rfl
    rcases this with h | h
    · exact act10_ne h
    · rw [Set.mem_singleton_iff] at h; exact act12_ne h

theorem fin3_C_full (e : Set Unit) :
    fin3_C e ({act 0, act 1, act 2} : Set _) = ({act 0} : Set _) := by
  unfold fin3_C; rw [if_pos rfl]

theorem fin3_C_pair02 (e : Set Unit) :
    fin3_C e ({act 0, act 2} : Set _) = ({act 0} : Set _) := by
  unfold fin3_C
  rw [if_neg menu_ne.2.2.2.1, if_pos rfl]

theorem fin3_C_pair12 (e : Set Unit) :
    fin3_C e ({act 1, act 2} : Set _) = ({act 2} : Set _) := by
  unfold fin3_C
  rw [if_neg menu_ne.2.2.2.2.1, if_neg menu_ne.2.2.2.2.2, if_pos rfl]

theorem fin3_C_pair01 (e : Set Unit) :
    fin3_C e ({act 0, act 1} : Set _) = ({act 0, act 1} : Set _) := by
  unfold fin3_C
  rw [if_neg menu_ne.1, if_neg menu_ne.2.1, if_neg menu_ne.2.2.1]

theorem fin3_C_singleton_of_A (e : Set Unit) {a : Unit → Fin 3}
    (_ha : a ∈ fin3_A) : fin3_C e ({a} : Set _) = ({a} : Set _) := by
  unfold fin3_C
  have h_full : ({a} : Set _) ≠ ({act 0, act 1, act 2} : Set _) := by
    intro h
    have h0 : (act 0 : Unit → Fin 3) ∈ ({a} : Set _) := by
      rw [h]; exact Or.inl rfl
    have h1 : (act 1 : Unit → Fin 3) ∈ ({a} : Set _) := by
      rw [h]; exact Or.inr (Or.inl rfl)
    rw [Set.mem_singleton_iff] at h0 h1
    exact act01_ne (h0.trans h1.symm)
  have h_pair02 : ({a} : Set _) ≠ ({act 0, act 2} : Set _) := by
    intro h
    have h0 : (act 0 : Unit → Fin 3) ∈ ({a} : Set _) := by
      rw [h]; exact Or.inl rfl
    have h2 : (act 2 : Unit → Fin 3) ∈ ({a} : Set _) := by
      rw [h]; exact Or.inr rfl
    rw [Set.mem_singleton_iff] at h0 h2
    exact act02_ne (h0.trans h2.symm)
  have h_pair12 : ({a} : Set _) ≠ ({act 1, act 2} : Set _) := by
    intro h
    have h1 : (act 1 : Unit → Fin 3) ∈ ({a} : Set _) := by
      rw [h]; exact Or.inl rfl
    have h2 : (act 2 : Unit → Fin 3) ∈ ({a} : Set _) := by
      rw [h]; exact Or.inr rfl
    rw [Set.mem_singleton_iff] at h1 h2
    exact act12_ne (h1.trans h2.symm)
  rw [if_neg h_full, if_neg h_pair02, if_neg h_pair12]

theorem fin3_C_singleton (e : Set Unit) (k : Fin 3) :
    fin3_C e ({act k} : Set _) = ({act k} : Set _) := by
  apply fin3_C_singleton_of_A
  fin_cases k
  · exact act0_mem_A
  · exact act1_mem_A
  · exact act2_mem_A

/-! ## The conditional judgment -/

noncomputable def fin3_judgment : ConditionalJudgment Unit (Fin 3) where
  X_nonempty := ⟨()⟩
  K_nonempty := ⟨0⟩
  E := unit_E
  A := fin3_A
  M := fin3_M
  C := fin3_C
  A_nonempty := ⟨act 0, act0_mem_A⟩
  M_nonempty := ⟨{act 0}, by unfold fin3_M; exact Or.inl rfl⟩
  M_elements_nonempty := by
    intro m hm
    rw [mem_fin3_M_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨act 0, rfl⟩
    · exact ⟨act 1, rfl⟩
    · exact ⟨act 2, rfl⟩
    · exact ⟨act 0, Or.inl rfl⟩
    · exact ⟨act 0, Or.inl rfl⟩
    · exact ⟨act 1, Or.inl rfl⟩
    · exact ⟨act 0, Or.inl rfl⟩
  C_in_M := by
    intro e m _ hm
    rw [mem_fin3_M_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [fin3_C_singleton]; unfold fin3_M; exact Or.inl rfl
    · rw [fin3_C_singleton]; unfold fin3_M; exact Or.inr (Or.inl rfl)
    · rw [fin3_C_singleton]; unfold fin3_M; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [fin3_C_pair01]; unfold fin3_M
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [fin3_C_pair02]; unfold fin3_M; exact Or.inl rfl
    · rw [fin3_C_pair12]; unfold fin3_M
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [fin3_C_full]; unfold fin3_M; exact Or.inl rfl
  C_subset_menu := by
    intro e m _ hm
    rw [mem_fin3_M_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [fin3_C_singleton]
    · rw [fin3_C_singleton]
    · rw [fin3_C_singleton]
    · rw [fin3_C_pair01]
    · rw [fin3_C_pair02]; intro x hx
      rw [Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
    · rw [fin3_C_pair12]; intro x hx
      rw [Set.mem_singleton_iff] at hx; subst hx; exact Or.inr rfl
    · rw [fin3_C_full]; intro x hx
      rw [Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl

/-! ## Witnessed `RevealedPref` facts -/

/-- Shorthand for the unique non-trivial event. -/
private abbrev univE : Set Unit := Set.univ

@[simp] theorem fin3_judgment_M : fin3_judgment.M = fin3_M := rfl
@[simp] theorem fin3_judgment_C : fin3_judgment.C = fin3_C := rfl
@[simp] theorem fin3_judgment_A : fin3_judgment.A = fin3_A := rfl
@[simp] theorem fin3_judgment_E : fin3_judgment.E = unit_E := rfl

theorem R_01 : RevealedPref fin3_judgment univE (act 0) (act 1) := by
  refine ⟨{act 0, act 1}, ?_, Or.inl rfl, Or.inr rfl, ?_⟩
  · change ({act 0, act 1} : Set _) ∈ fin3_M
    unfold fin3_M; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · change (act 0 : Unit → Fin 3) ∈ fin3_C univE _
    rw [fin3_C_pair01]; exact Or.inl rfl

theorem R_10 : RevealedPref fin3_judgment univE (act 1) (act 0) := by
  refine ⟨{act 0, act 1}, ?_, Or.inr rfl, Or.inl rfl, ?_⟩
  · change ({act 0, act 1} : Set _) ∈ fin3_M
    unfold fin3_M; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · change (act 1 : Unit → Fin 3) ∈ fin3_C univE _
    rw [fin3_C_pair01]; exact Or.inr rfl

theorem R_02 : RevealedPref fin3_judgment univE (act 0) (act 2) := by
  refine ⟨{act 0, act 2}, ?_, Or.inl rfl, Or.inr rfl, ?_⟩
  · change ({act 0, act 2} : Set _) ∈ fin3_M
    unfold fin3_M; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · change (act 0 : Unit → Fin 3) ∈ fin3_C univE _
    rw [fin3_C_pair02]; rfl

theorem R_21 : RevealedPref fin3_judgment univE (act 2) (act 1) := by
  refine ⟨{act 1, act 2}, ?_, Or.inr rfl, Or.inl rfl, ?_⟩
  · change ({act 1, act 2} : Set _) ∈ fin3_M
    unfold fin3_M; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · change (act 2 : Unit → Fin 3) ∈ fin3_C univE _
    rw [fin3_C_pair12]; rfl

theorem R_self (k : Fin 3) (hk : act k ∈ fin3_A) :
    RevealedPref fin3_judgment univE (act k) (act k) := by
  refine ⟨{act k}, ?_, rfl, rfl, ?_⟩
  · change ({act k} : Set _) ∈ fin3_M
    fin_cases k
    · unfold fin3_M; exact Or.inl rfl
    · unfold fin3_M; exact Or.inr (Or.inl rfl)
    · unfold fin3_M; exact Or.inr (Or.inr (Or.inl rfl))
  · change (act k : Unit → Fin 3) ∈ fin3_C univE _
    rw [fin3_C_singleton_of_A _ hk]; rfl

theorem R_00 : RevealedPref fin3_judgment univE (act 0) (act 0) :=
  R_self 0 act0_mem_A
theorem R_11 : RevealedPref fin3_judgment univE (act 1) (act 1) :=
  R_self 1 act1_mem_A
theorem R_22 : RevealedPref fin3_judgment univE (act 2) (act 2) :=
  R_self 2 act2_mem_A

/-- `act 1` is *not* revealed at-least-as-good as `act 2`. -/
theorem not_R_12 : ¬ RevealedPref fin3_judgment univE (act 1) (act 2) := by
  rintro ⟨m, hm, h1, h2, hC⟩
  change m ∈ fin3_M at hm
  change (act 1 : Unit → Fin 3) ∈ fin3_C univE m at hC
  rw [mem_fin3_M_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Set.mem_singleton_iff] at h1; exact act10_ne h1
  · rw [Set.mem_singleton_iff] at h2; exact act21_ne h2
  · rw [Set.mem_singleton_iff] at h1; exact act12_ne h1
  · rcases h2 with h | h
    · exact act20_ne h
    · rw [Set.mem_singleton_iff] at h; exact act21_ne h
  · rcases h1 with h | h
    · exact act10_ne h
    · rw [Set.mem_singleton_iff] at h; exact act12_ne h
  · rw [fin3_C_pair12] at hC
    rw [Set.mem_singleton_iff] at hC
    exact act12_ne hC
  · rw [fin3_C_full] at hC
    rw [Set.mem_singleton_iff] at hC
    exact act10_ne hC

/-- `act 2` is *not* revealed at-least-as-good as `act 0`. -/
theorem not_R_20 : ¬ RevealedPref fin3_judgment univE (act 2) (act 0) := by
  rintro ⟨m, hm, h2, h0, hC⟩
  change m ∈ fin3_M at hm
  change (act 2 : Unit → Fin 3) ∈ fin3_C univE m at hC
  rw [mem_fin3_M_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Set.mem_singleton_iff] at h2; exact act20_ne h2
  · rw [Set.mem_singleton_iff] at h0; exact act01_ne h0
  · rw [Set.mem_singleton_iff] at h0; exact act02_ne h0
  · rcases h2 with h | h
    · exact act20_ne h
    · rw [Set.mem_singleton_iff] at h; exact act21_ne h
  · rw [fin3_C_pair02] at hC
    rw [Set.mem_singleton_iff] at hC
    exact act20_ne hC
  · rcases h0 with h | h
    · exact act01_ne h
    · rw [Set.mem_singleton_iff] at h; exact act02_ne h
  · rw [fin3_C_full] at hC
    rw [Set.mem_singleton_iff] at hC
    exact act20_ne hC

/-! ## Non-transitivity of `R_e` -/

/-- The revealed-preference relation `R_e` on `fin3_judgment` is not
    transitive on `fin3_A`: `act 1 R_e act 0` and `act 0 R_e act 2`
    hold but `act 1 R_e act 2` fails. -/
theorem not_TransitiveOnAlt :
    ¬ TransitiveOnAlt fin3_judgment univE := by
  intro hTr
  exact not_R_12 (hTr (act 1) (act 0) (act 2)
    act1_mem_A act0_mem_A act2_mem_A R_10 R_02)

/-! ## Direct WARP failure -/

/-- WARP fails on `fin3_judgment` at `Set.univ`: with the menus
    `m = {act 0, act 1, act 2}` and `m' = {act 0, act 1}` and the
    elements `(a, a') = (act 1, act 0)`, both alternatives are common
    to the two menus, `act 1 ∈ C(m')` and `act 0 ∈ C(m)`, yet WARP
    would force `act 1 ∈ C(m) = {act 0}`. -/
theorem not_WARPAt :
    ¬ WARPAt fin3_judgment univE := by
  intro hWARP
  have hm : ({act 0, act 1} : Set _) ∈ fin3_judgment.M := by
    change ({act 0, act 1} : Set _) ∈ fin3_M
    unfold fin3_M; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hm' : ({act 0, act 1, act 2} : Set _) ∈ fin3_judgment.M := by
    change ({act 0, act 1, act 2} : Set _) ∈ fin3_M
    unfold fin3_M
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  -- Apply WARP with (m, m') = (pair01, triple), (a, a') = (act 1, act 0).
  have h := hWARP ({act 0, act 1} : Set _)
                  ({act 0, act 1, act 2} : Set _) hm hm'
                  (act 1) (act 0)
                  (Or.inr rfl)               -- act 1 ∈ pair01
                  (Or.inr (Or.inl rfl))      -- act 1 ∈ triple
                  (Or.inl rfl)               -- act 0 ∈ pair01
                  (Or.inl rfl)               -- act 0 ∈ triple
                  (by change (act 1 : Unit → Fin 3) ∈ fin3_C univE _
                      rw [fin3_C_pair01]; exact Or.inr rfl)
                  (by change (act 0 : Unit → Fin 3) ∈ fin3_C univE _
                      rw [fin3_C_full]; rfl)
  -- h : act 1 ∈ C({act 0, act 1, act 2}) = {act 0}.
  have hh : (act 1 : Unit → Fin 3) ∈ fin3_C univE
              ({act 0, act 1, act 2} : Set _) := h
  rw [fin3_C_full] at hh
  have h' : (act 1 : Unit → Fin 3) ∈ ({act 0} : Set _) := hh
  rw [Set.mem_singleton_iff] at h'
  exact act10_ne h'

/-! ## Representability -/

theorem maxSet_singleton (k : Fin 3) (hk : act k ∈ fin3_A) :
    maxSet fin3_judgment univE ({act k} : Set _) = ({act k} : Set _) := by
  ext x
  simp only [maxSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  refine ⟨fun ⟨hx, _⟩ => hx, fun hx => ?_⟩
  refine ⟨hx, ?_⟩
  intro y hy; rw [hy, hx]; exact R_self k hk

theorem maxSet_pair01 :
    maxSet fin3_judgment univE ({act 0, act 1} : Set _)
      = ({act 0, act 1} : Set _) := by
  ext x
  constructor
  · rintro ⟨hx, _⟩; exact hx
  · intro hx
    refine ⟨hx, ?_⟩
    intro y hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact R_00
      · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact R_01
    · rw [Set.mem_singleton_iff] at hx; rw [hx]
      rcases hy with rfl | hy
      · exact R_10
      · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact R_11

theorem maxSet_pair02 :
    maxSet fin3_judgment univE ({act 0, act 2} : Set _)
      = ({act 0} : Set _) := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    rcases hx with rfl | hx
    · exact rfl
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exfalso
      exact not_R_20 (hmax (act 0) (Or.inl rfl))
  · intro hx; rw [Set.mem_singleton_iff] at hx; rw [hx]
    refine ⟨Or.inl rfl, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · exact R_00
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact R_02

theorem maxSet_pair12 :
    maxSet fin3_judgment univE ({act 1, act 2} : Set _)
      = ({act 2} : Set _) := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    rcases hx with rfl | hx
    · exfalso
      exact not_R_12 (hmax (act 2) (Or.inr rfl))
    · rw [Set.mem_singleton_iff] at hx; subst hx; rfl
  · intro hx; rw [Set.mem_singleton_iff] at hx; subst hx
    refine ⟨Or.inr rfl, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · exact R_21
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact R_22

theorem maxSet_full :
    maxSet fin3_judgment univE ({act 0, act 1, act 2} : Set _)
      = ({act 0} : Set _) := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    rcases hx with rfl | hx
    · exact rfl
    rcases hx with rfl | hx
    · exfalso
      exact not_R_12 (hmax (act 2) (Or.inr (Or.inr rfl)))
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exfalso
      exact not_R_20 (hmax (act 0) (Or.inl rfl))
  · intro hx; rw [Set.mem_singleton_iff] at hx; rw [hx]
    refine ⟨Or.inl rfl, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · exact R_00
    rcases hy with rfl | hy
    · exact R_01
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact R_02

/-- **Representability**: `fin3_C` equals `maxSet R_e` on every menu. -/
theorem fin3_representable : Representable fin3_judgment univE := by
  intro m hm
  change m ∈ fin3_M at hm
  change fin3_C univE m = _
  rw [mem_fin3_M_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [fin3_C_singleton_of_A _ act0_mem_A,
        maxSet_singleton 0 act0_mem_A]
  · rw [fin3_C_singleton_of_A _ act1_mem_A,
        maxSet_singleton 1 act1_mem_A]
  · rw [fin3_C_singleton_of_A _ act2_mem_A,
        maxSet_singleton 2 act2_mem_A]
  · rw [fin3_C_pair01, maxSet_pair01]
  · rw [fin3_C_pair02, maxSet_pair02]
  · rw [fin3_C_pair12, maxSet_pair12]
  · rw [fin3_C_full, maxSet_full]

/-! ## Summary -/

/-- The headline theorem: `fin3_judgment` is `Representable` yet
    its revealed-preference relation `R_e` is not transitive on
    `fin3_A`, and consequently WARP fails. This realizes §8.4 of
    `prompts/PLAN_FOR_REVEALED_PREFERENCE_ON_A.md` and confirms that
    representability and transitivity of `R_e` are independent
    components of WARP. -/
theorem fin3_summary :
    Representable fin3_judgment univE ∧
    ¬ TransitiveOnAlt fin3_judgment univE ∧
    ¬ WARPAt fin3_judgment univE :=
  ⟨fin3_representable, not_TransitiveOnAlt, not_WARPAt⟩

/-! ## Multi-rationalizability by weak orders fails on this example

A *weak order* on `fin3_A` is a binary relation that is reflexive,
total, and transitive on the three alternatives. The proposition
`MultiRepresentable fin3_judgment univE ℛ` would say that on every
menu, the choice set is the union of `R`-maxima for `R ∈ ℛ`.

We show below that **no** family of weak orders on `fin3_A`
multi-rationalizes `fin3_judgment`. The argument uses three menu
facts:

* From `act 2 ∉ C({act 0, act 2}) = {act 0}`: every `R ∈ ℛ` must
  satisfy `R (act 0) (act 2)` (otherwise totality of `R` would give
  `R (act 2) (act 0)`, making `act 2` `R`-max in `{act 0, act 2}` and
  hence admissible — contradiction).
* From `act 1 ∉ C({act 1, act 2}) = {act 2}`: every `R ∈ ℛ` must
  satisfy `¬ R (act 1) (act 2)` (otherwise `act 1` would be `R`-max
  in `{act 1, act 2}` since `R (act 1) (act 1)` always holds).
  Combined with totality, every `R ∈ ℛ` has `R (act 2) (act 1)`
  strictly (i.e., `R (act 2) (act 1) ∧ ¬ R (act 1) (act 2)`).
* By transitivity in each `R ∈ ℛ`: from `R (act 0) (act 2)` and
  `R (act 2) (act 1)`, we get `R (act 0) (act 1)`. We also showed
  `¬ R (act 1) (act 2)`; combined with `R (act 0) (act 2)` and
  transitivity’s contrapositive, `¬ R (act 1) (act 0)`. Hence no
  `R ∈ ℛ` has `act 1` as `R`-max in `{act 0, act 1}`, contradicting
  `act 1 ∈ C({act 0, act 1})`.

This demonstrates that single-relation representability is *strictly
weaker* than multi-rationalizability by weak orders — the `Fin 3`
example sits between the two.
-/

/-- A weak order on `fin3_A`: reflexive at each `act k`, total on
    pairs from `fin3_A`, and transitive on triples from `fin3_A`. -/
structure WeakOrderOnA (R : (Unit → Fin 3) → (Unit → Fin 3) → Prop) : Prop where
  refl : ∀ a ∈ fin3_A, R a a
  total : ∀ a ∈ fin3_A, ∀ b ∈ fin3_A, R a b ∨ R b a
  trans : ∀ a ∈ fin3_A, ∀ b ∈ fin3_A, ∀ c ∈ fin3_A,
    R a b → R b c → R a c

/-- **Negative result**: no family of weak orders on `fin3_A`
    multi-rationalizes `fin3_judgment` on the universal event.

    Despite being `Representable` (by its own induced relation `R_e`),
    `fin3_judgment` is not multi-rationalizable by any family of
    weak orders. This shows the rep-without-WARP `Fin 3` example does
    *not* serve as a witness for Levi-style E-admissibility, and
    motivates the search for a separate, genuinely Levi-flavored
    example (typically two priors over a binary state space). -/
theorem fin3_not_multiRepresentable_by_weakOrders :
    ¬ ∃ ℛ : Set ((Unit → Fin 3) → (Unit → Fin 3) → Prop),
      (∀ R ∈ ℛ, WeakOrderOnA R) ∧
      MultiRepresentable fin3_judgment univE ℛ := by
  rintro ⟨ℛ, hWO, hMR⟩
  -- From `act 1 ∈ C({act 0, act 1}) = {act 0, act 1}` we extract a
  -- relation `R ∈ ℛ` with `act 1` as `R`-max in `{act 0, act 1}`.
  have h1_mem : (act 1 : Unit → Fin 3) ∈ fin3_judgment.C univE
                  ({act 0, act 1} : Set _) := by
    change (act 1 : Unit → Fin 3) ∈ fin3_C univE _
    rw [fin3_C_pair01]; exact Or.inr rfl
  have hm01 : ({act 0, act 1} : Set _) ∈ fin3_judgment.M := by
    change ({act 0, act 1} : Set _) ∈ fin3_M
    unfold fin3_M; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rw [hMR _ hm01] at h1_mem
  obtain ⟨_, R, hRℛ, hRmax⟩ := h1_mem
  have hWO_R := hWO R hRℛ
  -- (1) From `act 2 ∉ C({act 0, act 2}) = {act 0}`: R (act 0) (act 2).
  have hR_02 : R (act 0) (act 2) := by
    -- Suppose not. Then by totality: R (act 2) (act 0).
    by_contra hneg
    rcases hWO_R.total (act 0) act0_mem_A (act 2) act2_mem_A with h | h
    · exact hneg h
    -- Then `act 2` is R-max in {act 0, act 2}: needs R (act 2) (act 0)
    -- and R (act 2) (act 2). So `act 2 ∈ multiMaxSet ℛ _`.
    have h2_max : (act 2 : Unit → Fin 3) ∈ multiMaxSet ℛ
                    ({act 0, act 2} : Set _) := by
      refine ⟨Or.inr rfl, R, hRℛ, ?_⟩
      intro y hy
      rcases hy with rfl | hy
      · exact h
      · rw [Set.mem_singleton_iff] at hy; subst hy
        exact hWO_R.refl (act 2) act2_mem_A
    -- But C({act 0, act 2}) = {act 0}, so multiMaxSet = {act 0} too.
    have hm02 : ({act 0, act 2} : Set _) ∈ fin3_judgment.M := by
      change ({act 0, act 2} : Set _) ∈ fin3_M
      unfold fin3_M; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    rw [← hMR _ hm02] at h2_max
    have h2_in_C : (act 2 : Unit → Fin 3) ∈ fin3_C univE
                    ({act 0, act 2} : Set _) := h2_max
    rw [fin3_C_pair02] at h2_in_C
    rw [Set.mem_singleton_iff] at h2_in_C
    exact act20_ne h2_in_C
  -- (2) From `act 1 ∉ C({act 1, act 2}) = {act 2}`: ¬ R (act 1) (act 2).
  have hRn_12 : ¬ R (act 1) (act 2) := by
    intro h12
    -- Then `act 1` is R-max in {act 1, act 2}: needs R (act 1) (act 1)
    -- (refl) and R (act 1) (act 2) (assumption).
    have h1_max : (act 1 : Unit → Fin 3) ∈ multiMaxSet ℛ
                    ({act 1, act 2} : Set _) := by
      refine ⟨Or.inl rfl, R, hRℛ, ?_⟩
      intro y hy
      rcases hy with rfl | hy
      · exact hWO_R.refl (act 1) act1_mem_A
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact h12
    have hm12 : ({act 1, act 2} : Set _) ∈ fin3_judgment.M := by
      change ({act 1, act 2} : Set _) ∈ fin3_M
      unfold fin3_M
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    rw [← hMR _ hm12] at h1_max
    have h1_in_C : (act 1 : Unit → Fin 3) ∈ fin3_C univE
                    ({act 1, act 2} : Set _) := h1_max
    rw [fin3_C_pair12] at h1_in_C
    rw [Set.mem_singleton_iff] at h1_in_C
    exact act12_ne h1_in_C
  -- (3) Combining (2) with totality: R (act 2) (act 1).
  have hR_21 : R (act 2) (act 1) := by
    rcases hWO_R.total (act 1) act1_mem_A (act 2) act2_mem_A with h | h
    · exact absurd h hRn_12
    · exact h
  -- (4) Transitivity: R (act 0) (act 2) and R (act 2) (act 1) give
  --     R (act 0) (act 1).
  have hR_01 : R (act 0) (act 1) :=
    hWO_R.trans (act 0) act0_mem_A (act 2) act2_mem_A (act 1) act1_mem_A
      hR_02 hR_21
  -- (5) Final contradiction. From `hRmax`: ∀ a' ∈ {act 0, act 1},
  --     R (act 1) a'. In particular `R (act 1) (act 0)`. We will
  --     contradict this: combined with R (act 0) (act 2), transitivity
  --     would give R (act 1) (act 2), contradicting hRn_12.
  have hR_10 : R (act 1) (act 0) := hRmax (act 0) (Or.inl rfl)
  have hR_12 : R (act 1) (act 2) :=
    hWO_R.trans (act 1) act1_mem_A (act 0) act0_mem_A (act 2) act2_mem_A
      hR_10 hR_02
  exact hRn_12 hR_12

/-! ## Incomparability is empty in this example

Even though WARP fails on `fin3_judgment`, every pair of alternatives
is comparable: for each pair, there is a witness menu putting at
least one direction of `R_e` in force. So this example separates
*non-transitivity* of `R_e` from *incomparability*. -/

/-- For each ordered pair `(act i, act j)` with `i ≠ j`, at least one
    direction of `RevealedPref fin3_judgment univE` holds. Hence
    `¬ Incomp` for every distinct pair in `fin3_A`. -/
theorem fin3_no_incomp (a b : Unit → Fin 3)
    (ha : a ∈ fin3_A) (hb : b ∈ fin3_A) :
    ¬ Incomp fin3_judgment univE a b := by
  rintro ⟨hab, hba⟩
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact hab R_00
    rcases hb with rfl | hb
    · exact hab R_01
    · rw [Set.mem_singleton_iff] at hb; subst hb; exact hab R_02
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact hba R_01
    rcases hb with rfl | hb
    · exact hab R_11
    · rw [Set.mem_singleton_iff] at hb; subst hb; exact hba R_21
  · rw [Set.mem_singleton_iff] at ha; subst ha
    rcases hb with rfl | hb
    · exact hba R_02
    rcases hb with rfl | hb
    · exact hab R_21
    · rw [Set.mem_singleton_iff] at hb; subst hb; exact hab R_22

end ConditionalChoice
