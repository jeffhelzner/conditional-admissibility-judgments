/-
# A Two-Prior Levi Example: Multi-Representable but not Representable

This file constructs a concrete `ConditionalJudgment (Fin 2) (Fin 3)`
that is *multi-representable* by a family of two weak orders on
alternatives — corresponding to Levi-style E-admissibility under a
credal set with two priors and a fixed utility — but is **not**
representable by any single relation.

## The example

* `X = Fin 2`         (binary state space)
* `K = Fin 3`         (three consequences, with utility `u(k) := k.val`)
* Three acts:
  - `aS x := 1`           (the *safe* constant act)
  - `a0 := (2, 0)`        (bets on state 0)
  - `a1 := (0, 2)`        (bets on state 1)
* Two integer-weighted priors:
  - `R0 := λ a b. 7·u(a 0) + 3·u(a 1) ≥ 7·u(b 0) + 3·u(b 1)` (favors state 0)
  - `R1 := λ a b. 3·u(a 0) + 7·u(a 1) ≥ 3·u(b 0) + 7·u(b 1)` (favors state 1)

EU table:

| act  | EU under R0 | EU under R1 |
|------|-------------|-------------|
| `aS` | 10          | 10          |
| `a0` | 14          | 6           |
| `a1` | 6           | 14          |

Hence `R0` orders `a0 ≻ aS ≻ a1` and `R1` orders `a1 ≻ aS ≻ a0`.

The choice function on the seven menus picks every act in every menu
*except* the safe act `aS` is excluded from the full triple. This is
the canonical Levi/SSK pattern: `aS` is admissible against any single
gamble, but inadmissible against the menu of *both* gambles.

## What is proved

* `levi_multiRepresentable`:
  `MultiRepresentable levi_judgment univE ({R0, R1} : Set _)`.
* `levi_not_representable`:
  `¬ Representable levi_judgment univE`.
* `levi_cautiousIncomp_a0_a1`, `levi_cautiousIncomp_aS_a0`,
  `levi_cautiousIncomp_aS_a1`: every distinct pair is `CautiousIncomp`.
-/

import RevealedPreference
import MultiRepresentable
import StrictIndiffIncomp

namespace ConditionalChoice

open Classical

/-! ## Acts on a binary state space -/

/-- The safe constant act with utility 1 in every state. -/
@[reducible] def aS : Fin 2 → Fin 3 := fun _ => 1

/-- The "bet on state 0" act: utility 2 on state 0, utility 0 on state 1. -/
@[reducible] def a0 : Fin 2 → Fin 3 := fun s => if s = 0 then 2 else 0

/-- The "bet on state 1" act: utility 0 on state 0, utility 2 on state 1. -/
@[reducible] def a1 : Fin 2 → Fin 3 := fun s => if s = 0 then 0 else 2

/-! ### Distinctness -/

theorem aS_ne_a0 : aS ≠ a0 := by
  intro h; have := congrArg (fun f => (f 0).val) h
  simp [aS, a0] at this
theorem aS_ne_a1 : aS ≠ a1 := by
  intro h; have := congrArg (fun f => (f 1).val) h
  simp [aS, a1] at this
theorem a0_ne_a1 : a0 ≠ a1 := by
  intro h; have := congrArg (fun f => (f 0).val) h
  simp [a0, a1] at this
theorem a0_ne_aS : a0 ≠ aS := fun h => aS_ne_a0 h.symm
theorem a1_ne_aS : a1 ≠ aS := fun h => aS_ne_a1 h.symm
theorem a1_ne_a0 : a1 ≠ a0 := fun h => a0_ne_a1 h.symm

/-! ## Set algebra and alternative space -/

/-- The full powerset on `Fin 2`. -/
def fin2_E : SetAlgebra (Fin 2) where
  carrier := Set.univ
  univ_mem := trivial
  union_mem := fun _ _ => trivial
  inter_mem := fun _ _ => trivial
  compl_mem := fun _ => trivial

def levi_A : Set (Fin 2 → Fin 3) := {aS, a0, a1}

theorem aS_mem_A : aS ∈ levi_A := Or.inl rfl
theorem a0_mem_A : a0 ∈ levi_A := Or.inr (Or.inl rfl)
theorem a1_mem_A : a1 ∈ levi_A := Or.inr (Or.inr rfl)

/-! ## Menus -/

/-- The seven non-empty submenus of `levi_A`. -/
def levi_M : Set (Set (Fin 2 → Fin 3)) :=
  { ({aS} : Set _),
    ({a0} : Set _),
    ({a1} : Set _),
    ({aS, a0} : Set _),
    ({aS, a1} : Set _),
    ({a0, a1} : Set _),
    ({aS, a0, a1} : Set _) }

theorem mem_levi_M_iff (m : Set (Fin 2 → Fin 3)) :
    m ∈ levi_M ↔
      m = {aS} ∨ m = {a0} ∨ m = {a1} ∨
      m = {aS, a0} ∨ m = {aS, a1} ∨ m = {a0, a1} ∨
      m = {aS, a0, a1} := by
  unfold levi_M
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

/-! ## Choice function -/

noncomputable def levi_C : Set (Fin 2) → Set (Fin 2 → Fin 3) →
    Set (Fin 2 → Fin 3) :=
  fun _ m =>
    if m = ({aS, a0, a1} : Set _) then ({a0, a1} : Set _)
    else m

theorem levi_C_full (e : Set (Fin 2)) :
    levi_C e ({aS, a0, a1} : Set _) = ({a0, a1} : Set _) := by
  unfold levi_C; rw [if_pos rfl]

theorem levi_C_other {e : Set (Fin 2)} {m : Set (Fin 2 → Fin 3)}
    (hne : m ≠ ({aS, a0, a1} : Set _)) : levi_C e m = m := by
  unfold levi_C; rw [if_neg hne]

/-! ### Distinctness of menus -/

private theorem singleton_ne_full (a : Fin 2 → Fin 3) :
    ({a} : Set (Fin 2 → Fin 3)) ≠ ({aS, a0, a1} : Set _) := by
  intro h
  have h0 : a0 ∈ ({a} : Set (Fin 2 → Fin 3)) := by
    rw [h]; exact Or.inr (Or.inl rfl)
  have h1 : a1 ∈ ({a} : Set (Fin 2 → Fin 3)) := by
    rw [h]; exact Or.inr (Or.inr rfl)
  rw [Set.mem_singleton_iff] at h0 h1
  exact a0_ne_a1 (h0.trans h1.symm)

private theorem pair_aS_a0_ne_full :
    ({aS, a0} : Set (Fin 2 → Fin 3)) ≠ ({aS, a0, a1} : Set _) := by
  intro h
  have : a1 ∈ ({aS, a0} : Set (Fin 2 → Fin 3)) := by
    rw [h]; exact Or.inr (Or.inr rfl)
  rcases this with h | h
  · exact a1_ne_aS h
  · rw [Set.mem_singleton_iff] at h; exact a1_ne_a0 h

private theorem pair_aS_a1_ne_full :
    ({aS, a1} : Set (Fin 2 → Fin 3)) ≠ ({aS, a0, a1} : Set _) := by
  intro h
  have : a0 ∈ ({aS, a1} : Set (Fin 2 → Fin 3)) := by
    rw [h]; exact Or.inr (Or.inl rfl)
  rcases this with h | h
  · exact a0_ne_aS h
  · rw [Set.mem_singleton_iff] at h; exact a0_ne_a1 h

private theorem pair_a0_a1_ne_full :
    ({a0, a1} : Set (Fin 2 → Fin 3)) ≠ ({aS, a0, a1} : Set _) := by
  intro h
  have : aS ∈ ({a0, a1} : Set (Fin 2 → Fin 3)) := by
    rw [h]; exact Or.inl rfl
  rcases this with h | h
  · exact aS_ne_a0 h
  · rw [Set.mem_singleton_iff] at h; exact aS_ne_a1 h

theorem levi_C_singleton (e : Set (Fin 2)) (a : Fin 2 → Fin 3) :
    levi_C e ({a} : Set _) = ({a} : Set _) :=
  levi_C_other (singleton_ne_full a)

theorem levi_C_pair_aS_a0 (e : Set (Fin 2)) :
    levi_C e ({aS, a0} : Set _) = ({aS, a0} : Set _) :=
  levi_C_other pair_aS_a0_ne_full

theorem levi_C_pair_aS_a1 (e : Set (Fin 2)) :
    levi_C e ({aS, a1} : Set _) = ({aS, a1} : Set _) :=
  levi_C_other pair_aS_a1_ne_full

theorem levi_C_pair_a0_a1 (e : Set (Fin 2)) :
    levi_C e ({a0, a1} : Set _) = ({a0, a1} : Set _) :=
  levi_C_other pair_a0_a1_ne_full

/-! ## The conditional judgment -/

noncomputable def levi_judgment : ConditionalJudgment (Fin 2) (Fin 3) where
  X_nonempty := ⟨0⟩
  K_nonempty := ⟨0⟩
  E := fin2_E
  A := levi_A
  M := levi_M
  C := levi_C
  A_nonempty := ⟨aS, aS_mem_A⟩
  M_nonempty := ⟨{aS}, Or.inl rfl⟩
  M_elements_nonempty := by
    intro m hm
    rw [mem_levi_M_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨aS, rfl⟩
    · exact ⟨a0, rfl⟩
    · exact ⟨a1, rfl⟩
    · exact ⟨aS, Or.inl rfl⟩
    · exact ⟨aS, Or.inl rfl⟩
    · exact ⟨a0, Or.inl rfl⟩
    · exact ⟨aS, Or.inl rfl⟩
  C_in_M := by
    intro e m _ hm
    rw [mem_levi_M_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [levi_C_singleton]; exact Or.inl rfl
    · rw [levi_C_singleton]; exact Or.inr (Or.inl rfl)
    · rw [levi_C_singleton]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [levi_C_pair_aS_a0]
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [levi_C_pair_aS_a1]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · rw [levi_C_pair_a0_a1]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · rw [levi_C_full]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  C_subset_menu := by
    intro e m _ hm
    rw [mem_levi_M_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [levi_C_singleton]
    · rw [levi_C_singleton]
    · rw [levi_C_singleton]
    · rw [levi_C_pair_aS_a0]
    · rw [levi_C_pair_aS_a1]
    · rw [levi_C_pair_a0_a1]
    · rw [levi_C_full]; intro x hx
      rcases hx with rfl | hx
      · exact Or.inr (Or.inl rfl)
      · rw [Set.mem_singleton_iff] at hx; subst hx
        exact Or.inr (Or.inr rfl)

@[simp] theorem levi_judgment_M : levi_judgment.M = levi_M := rfl
@[simp] theorem levi_judgment_C : levi_judgment.C = levi_C := rfl
@[simp] theorem levi_judgment_A : levi_judgment.A = levi_A := rfl
@[simp] theorem levi_judgment_E : levi_judgment.E = fin2_E := rfl

private abbrev univE : Set (Fin 2) := Set.univ

/-! ## The two priors / weak orders -/

def eu (p0 p1 : ℕ) (a : Fin 2 → Fin 3) : ℕ :=
  p0 * (a 0).val + p1 * (a 1).val

theorem eu_aS (p0 p1 : ℕ) : eu p0 p1 aS = p0 + p1 := by
  unfold eu; simp [aS]
theorem eu_a0 (p0 p1 : ℕ) : eu p0 p1 a0 = 2 * p0 := by
  unfold eu; simp [a0]; ring
theorem eu_a1 (p0 p1 : ℕ) : eu p0 p1 a1 = 2 * p1 := by
  unfold eu; simp [a1]; ring

/-- The EU-induced weak preorder under prior weights `(p₀, p₁)`. -/
def Rfam (p0 p1 : ℕ) : (Fin 2 → Fin 3) → (Fin 2 → Fin 3) → Prop :=
  fun a b => eu p0 p1 b ≤ eu p0 p1 a

def R0 : (Fin 2 → Fin 3) → (Fin 2 → Fin 3) → Prop := Rfam 7 3
def R1 : (Fin 2 → Fin 3) → (Fin 2 → Fin 3) → Prop := Rfam 3 7

/-! ### Numerical EU values -/

theorem eu_R0_aS : eu 7 3 aS = 10 := by rw [eu_aS]
theorem eu_R0_a0 : eu 7 3 a0 = 14 := by rw [eu_a0]
theorem eu_R0_a1 : eu 7 3 a1 = 6  := by rw [eu_a1]
theorem eu_R1_aS : eu 3 7 aS = 10 := by rw [eu_aS]
theorem eu_R1_a0 : eu 3 7 a0 = 6  := by rw [eu_a0]
theorem eu_R1_a1 : eu 3 7 a1 = 14 := by rw [eu_a1]

/-! ### Strict-preference facts -/

theorem R0_a0_aS : R0 a0 aS := by
  unfold R0 Rfam; rw [eu_R0_aS, eu_R0_a0]; decide
theorem R0_aS_a1 : R0 aS a1 := by
  unfold R0 Rfam; rw [eu_R0_aS, eu_R0_a1]; decide
theorem R0_a0_a1 : R0 a0 a1 := by
  unfold R0 Rfam; rw [eu_R0_a0, eu_R0_a1]; decide
theorem not_R0_a1_aS : ¬ R0 a1 aS := by
  unfold R0 Rfam; rw [eu_R0_aS, eu_R0_a1]; decide
theorem not_R0_aS_a0 : ¬ R0 aS a0 := by
  unfold R0 Rfam; rw [eu_R0_aS, eu_R0_a0]; decide
theorem not_R0_a1_a0 : ¬ R0 a1 a0 := by
  unfold R0 Rfam; rw [eu_R0_a0, eu_R0_a1]; decide

theorem R1_a1_aS : R1 a1 aS := by
  unfold R1 Rfam; rw [eu_R1_aS, eu_R1_a1]; decide
theorem R1_aS_a0 : R1 aS a0 := by
  unfold R1 Rfam; rw [eu_R1_aS, eu_R1_a0]; decide
theorem R1_a1_a0 : R1 a1 a0 := by
  unfold R1 Rfam; rw [eu_R1_a0, eu_R1_a1]; decide
theorem not_R1_a0_aS : ¬ R1 a0 aS := by
  unfold R1 Rfam; rw [eu_R1_aS, eu_R1_a0]; decide
theorem not_R1_aS_a1 : ¬ R1 aS a1 := by
  unfold R1 Rfam; rw [eu_R1_aS, eu_R1_a1]; decide
theorem not_R1_a0_a1 : ¬ R1 a0 a1 := by
  unfold R1 Rfam; rw [eu_R1_a0, eu_R1_a1]; decide

theorem R0_refl (a : Fin 2 → Fin 3) : R0 a a := by
  unfold R0 Rfam; exact le_refl _
theorem R1_refl (a : Fin 2 → Fin 3) : R1 a a := by
  unfold R1 Rfam; exact le_refl _

/-! ## The family ℛ = {R0, R1} -/

def Rℛ : Set ((Fin 2 → Fin 3) → (Fin 2 → Fin 3) → Prop) := {R0, R1}

theorem R0_mem : R0 ∈ Rℛ := Or.inl rfl
theorem R1_mem : R1 ∈ Rℛ := Or.inr rfl

/-! ## Multi-representability -/

private theorem multiMax_singleton (a : Fin 2 → Fin 3) :
    multiMaxSet Rℛ ({a} : Set _) = ({a} : Set _) := by
  ext x
  unfold multiMaxSet
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, _⟩; exact hx
  · intro hx; subst hx
    refine ⟨rfl, R0, R0_mem, ?_⟩
    intro a' ha'; subst ha'
    exact R0_refl _

private theorem multiMax_pair_aS_a0 :
    multiMaxSet Rℛ ({aS, a0} : Set _) = ({aS, a0} : Set _) := by
  ext x
  unfold multiMaxSet
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, _⟩; exact hx
  · rintro (rfl | rfl)
    · refine ⟨Or.inl rfl, R1, R1_mem, ?_⟩
      rintro a' (rfl | rfl)
      · exact R1_refl _
      · exact R1_aS_a0
    · refine ⟨Or.inr rfl, R0, R0_mem, ?_⟩
      rintro a' (rfl | rfl)
      · exact R0_a0_aS
      · exact R0_refl _

private theorem multiMax_pair_aS_a1 :
    multiMaxSet Rℛ ({aS, a1} : Set _) = ({aS, a1} : Set _) := by
  ext x
  unfold multiMaxSet
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, _⟩; exact hx
  · rintro (rfl | rfl)
    · refine ⟨Or.inl rfl, R0, R0_mem, ?_⟩
      rintro a' (rfl | rfl)
      · exact R0_refl _
      · exact R0_aS_a1
    · refine ⟨Or.inr rfl, R1, R1_mem, ?_⟩
      rintro a' (rfl | rfl)
      · exact R1_a1_aS
      · exact R1_refl _

private theorem multiMax_pair_a0_a1 :
    multiMaxSet Rℛ ({a0, a1} : Set _) = ({a0, a1} : Set _) := by
  ext x
  unfold multiMaxSet
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, _⟩; exact hx
  · rintro (rfl | rfl)
    · refine ⟨Or.inl rfl, R0, R0_mem, ?_⟩
      rintro a' (rfl | rfl)
      · exact R0_refl _
      · exact R0_a0_a1
    · refine ⟨Or.inr rfl, R1, R1_mem, ?_⟩
      rintro a' (rfl | rfl)
      · exact R1_a1_a0
      · exact R1_refl _

private theorem multiMax_full :
    multiMaxSet Rℛ ({aS, a0, a1} : Set _) = ({a0, a1} : Set _) := by
  ext x
  unfold multiMaxSet
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, R, hR, hmax⟩
    rcases hx with rfl | hx
    · exfalso
      rcases hR with rfl | rfl
      · exact not_R0_aS_a0 (hmax a0 (Or.inr (Or.inl rfl)))
      · exact not_R1_aS_a1 (hmax a1 (Or.inr (Or.inr rfl)))
    · exact hx
  · rintro (rfl | rfl)
    · refine ⟨Or.inr (Or.inl rfl), R0, R0_mem, ?_⟩
      rintro a' (rfl | rfl | rfl)
      · exact R0_a0_aS
      · exact R0_refl _
      · exact R0_a0_a1
    · refine ⟨Or.inr (Or.inr rfl), R1, R1_mem, ?_⟩
      rintro a' (rfl | rfl | rfl)
      · exact R1_a1_aS
      · exact R1_a1_a0
      · exact R1_refl _

theorem levi_multiRepresentable :
    MultiRepresentable levi_judgment univE Rℛ := by
  intro m hm
  change m ∈ levi_M at hm
  rw [mem_levi_M_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change levi_C univE _ = _
    rw [levi_C_singleton]; exact (multiMax_singleton aS).symm
  · change levi_C univE _ = _
    rw [levi_C_singleton]; exact (multiMax_singleton a0).symm
  · change levi_C univE _ = _
    rw [levi_C_singleton]; exact (multiMax_singleton a1).symm
  · change levi_C univE _ = _
    rw [levi_C_pair_aS_a0]; exact multiMax_pair_aS_a0.symm
  · change levi_C univE _ = _
    rw [levi_C_pair_aS_a1]; exact multiMax_pair_aS_a1.symm
  · change levi_C univE _ = _
    rw [levi_C_pair_a0_a1]; exact multiMax_pair_a0_a1.symm
  · change levi_C univE _ = _
    rw [levi_C_full]; exact multiMax_full.symm

/-! ## The example is not single-relation representable

Every two-element menu has both elements admissible, so `R_e` is the
total relation on the three acts. Hence `maxSet` of the full menu is
the full menu — but `C` of the full menu is `{a0, a1}`. -/

private theorem revealedPref_aS_a0 :
    RevealedPref levi_judgment univE aS a0 := by
  refine ⟨{aS, a0}, ?_, Or.inl rfl, Or.inr rfl, ?_⟩
  · change ({aS, a0} : Set _) ∈ levi_M
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · change aS ∈ levi_C univE _
    rw [levi_C_pair_aS_a0]; exact Or.inl rfl

private theorem revealedPref_aS_a1 :
    RevealedPref levi_judgment univE aS a1 := by
  refine ⟨{aS, a1}, ?_, Or.inl rfl, Or.inr rfl, ?_⟩
  · change ({aS, a1} : Set _) ∈ levi_M
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · change aS ∈ levi_C univE _
    rw [levi_C_pair_aS_a1]; exact Or.inl rfl

theorem levi_not_representable : ¬ Representable levi_judgment univE := by
  intro hRep
  set m : Set (Fin 2 → Fin 3) := ({aS, a0, a1} : Set _) with hm_def
  have hm : m ∈ levi_judgment.M := by
    change m ∈ levi_M
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have haS_in_max : aS ∈ maxSet levi_judgment univE m := by
    refine ⟨Or.inl rfl, ?_⟩
    rintro a' (rfl | rfl | rfl)
    · -- aS R aS via singleton
      refine ⟨{aS}, ?_, rfl, rfl, ?_⟩
      · change ({aS} : Set _) ∈ levi_M
        exact Or.inl rfl
      · change aS ∈ levi_C univE _
        rw [levi_C_singleton]; rfl
    · exact revealedPref_aS_a0
    · exact revealedPref_aS_a1
  have haS_notin_C : aS ∉ levi_judgment.C univE m := by
    change aS ∉ levi_C univE m
    rw [hm_def, levi_C_full]
    rintro (h | h)
    · exact aS_ne_a0 h
    · rw [Set.mem_singleton_iff] at h; exact aS_ne_a1 h
  rw [hRep m hm] at haS_notin_C
  exact haS_notin_C haS_in_max

/-! ## Genuine cautious incomparability -/

theorem levi_cautiousIncomp_a0_a1 : CautiousIncomp Rℛ a0 a1 := by
  refine ⟨?_, ?_⟩
  · intro hC; exact not_R1_a0_a1 (hC R1 R1_mem)
  · intro hC; exact not_R0_a1_a0 (hC R0 R0_mem)

theorem levi_cautiousIncomp_aS_a0 : CautiousIncomp Rℛ aS a0 := by
  refine ⟨?_, ?_⟩
  · intro hC; exact not_R0_aS_a0 (hC R0 R0_mem)
  · intro hC; exact not_R1_a0_aS (hC R1 R1_mem)

theorem levi_cautiousIncomp_aS_a1 : CautiousIncomp Rℛ aS a1 := by
  refine ⟨?_, ?_⟩
  · intro hC; exact not_R1_aS_a1 (hC R1 R1_mem)
  · intro hC; exact not_R0_a1_aS (hC R0 R0_mem)

/-! ## Headline summary -/

theorem levi_summary :
    MultiRepresentable levi_judgment univE Rℛ ∧
    ¬ Representable levi_judgment univE ∧
    CautiousIncomp Rℛ a0 a1 ∧
    CautiousIncomp Rℛ aS a0 ∧
    CautiousIncomp Rℛ aS a1 :=
  ⟨ levi_multiRepresentable,
    levi_not_representable,
    levi_cautiousIncomp_a0_a1,
    levi_cautiousIncomp_aS_a0,
    levi_cautiousIncomp_aS_a1 ⟩

/-! ## Alternative-level totality and the absence of `Incomp`

The example exhibits genuine `CautiousIncomp` at the multi-relation
layer, but the alternative-level revealed-preference relation `R_e`
is *total* on `levi_A` — every pair menu returns both elements, so
each pair has both directions of `R_e`. Consequently the
alternative-level `Incomp` predicate (from `StrictIndiffIncomp.lean`)
is empty on `levi_A`.

This is the formal residence of the conceptual point: incomparability
in the Levi/SSK sense is *not* visible at the level of a single
revealed-preference relation reading off `C`. The witness layer that
makes incomparability formally available is the multi-relation layer
(`Cautious` / `CautiousIncomp`). -/

private theorem revealedPref_a0_aS :
    RevealedPref levi_judgment univE a0 aS := by
  refine ⟨{aS, a0}, ?_, Or.inr rfl, Or.inl rfl, ?_⟩
  · change ({aS, a0} : Set _) ∈ levi_M
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · change a0 ∈ levi_C univE _
    rw [levi_C_pair_aS_a0]; exact Or.inr rfl

private theorem revealedPref_a1_aS :
    RevealedPref levi_judgment univE a1 aS := by
  refine ⟨{aS, a1}, ?_, Or.inr rfl, Or.inl rfl, ?_⟩
  · change ({aS, a1} : Set _) ∈ levi_M
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · change a1 ∈ levi_C univE _
    rw [levi_C_pair_aS_a1]; exact Or.inr rfl

private theorem revealedPref_a0_a1 :
    RevealedPref levi_judgment univE a0 a1 := by
  refine ⟨{a0, a1}, ?_, Or.inl rfl, Or.inr rfl, ?_⟩
  · change ({a0, a1} : Set _) ∈ levi_M
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · change a0 ∈ levi_C univE _
    rw [levi_C_pair_a0_a1]; exact Or.inl rfl

private theorem revealedPref_a1_a0 :
    RevealedPref levi_judgment univE a1 a0 := by
  refine ⟨{a0, a1}, ?_, Or.inr rfl, Or.inl rfl, ?_⟩
  · change ({a0, a1} : Set _) ∈ levi_M
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · change a1 ∈ levi_C univE _
    rw [levi_C_pair_a0_a1]; exact Or.inr rfl

private theorem revealedPref_refl (a : Fin 2 → Fin 3) (ha : a ∈ levi_A) :
    RevealedPref levi_judgment univE a a := by
  refine ⟨{a}, ?_, rfl, rfl, ?_⟩
  · change ({a} : Set _) ∈ levi_M
    rcases ha with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · change a ∈ levi_C univE _
    rw [levi_C_singleton]; rfl

/-- `R_e` is total on `levi_A`: every pair of alternatives has at
    least one direction of `RevealedPref` in force. -/
theorem levi_alt_R_total (a b : Fin 2 → Fin 3)
    (ha : a ∈ levi_A) (hb : b ∈ levi_A) :
    RevealedPref levi_judgment univE a b ∨
    RevealedPref levi_judgment univE b a := by
  rcases ha with rfl | rfl | rfl
  · rcases hb with rfl | rfl | rfl
    · exact Or.inl (revealedPref_refl _ aS_mem_A)
    · exact Or.inl revealedPref_aS_a0
    · exact Or.inl revealedPref_aS_a1
  · rcases hb with rfl | rfl | rfl
    · exact Or.inl revealedPref_a0_aS
    · exact Or.inl (revealedPref_refl _ a0_mem_A)
    · exact Or.inl revealedPref_a0_a1
  · rcases hb with rfl | rfl | rfl
    · exact Or.inl revealedPref_a1_aS
    · exact Or.inl revealedPref_a1_a0
    · exact Or.inl (revealedPref_refl _ a1_mem_A)

/-- The alternative-level `Incomp` predicate is empty on `levi_A`,
    even though the multi-relation `CautiousIncomp` is non-empty.
    This is the precise sense in which Levi/SSK incomparability is a
    multi-relation phenomenon, not visible at the single-relation
    revealed-preference layer. -/
theorem levi_no_alt_incomp (a b : Fin 2 → Fin 3)
    (ha : a ∈ levi_A) (hb : b ∈ levi_A) :
    ¬ Incomp levi_judgment univE a b := by
  intro ⟨hab, hba⟩
  rcases levi_alt_R_total a b ha hb with h | h
  · exact hab h
  · exact hba h

end ConditionalChoice
