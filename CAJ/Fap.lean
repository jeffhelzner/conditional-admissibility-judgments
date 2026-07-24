import CAJ.SetAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Closure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finitely additive probability and credal convexity

A `Fap E` is a finitely additive probability measure on a set algebra `E`:
nonnegative, normalized, and additive on disjoint members. This is the
probability notion matching the merely finite closure of `SetAlgebra`
(no countable additivity).

Credal states are *sets* of `Fap`s. Mixtures are defined directly on `Fap`
(pointwise convex combination) — we deliberately avoid Mathlib's `Convex`,
which would require a module structure on `Fap E`. `MixtureClosed` classes
are those closed under binary mixtures, and `convexHull` is the induced
closure operator on `Set (Fap E)` (intersection of all mixture-closed
supersets), the credal-side counterpart of `commensurationClosure` on the
judgment side. Keeping the two closure operators separate is the point of
the convexity wedge (M4/M5): commensuration closure never forces convex
closure.
-/

namespace CAJ

universe u

/-- A finitely additive probability measure on the set algebra `E`:
a nonnegative, normalized, finitely additive assignment of reals to the
members of `E`. -/
structure Fap {X : Type u} (E : SetAlgebra X) where
  /-- The probability assignment on members of the algebra. -/
  p : {s : Set X // s ∈ E} → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ s, 0 ≤ p s
  /-- Normalization: the sure event has probability 1. -/
  p_univ : p ⟨Set.univ, E.univ_mem⟩ = 1
  /-- Finite additivity on disjoint members. -/
  additive : ∀ s t : {s : Set X // s ∈ E}, Disjoint s.val t.val →
    p ⟨s.val ∪ t.val, E.union_mem s.2 t.2⟩ = p s + p t

namespace Fap

variable {X : Type u} {E : SetAlgebra X}

@[ext]
theorem ext {p q : Fap E} (h : ∀ s, p.p s = q.p s) : p = q := by
  have hp : p.p = q.p := funext h
  cases p; cases q; cases hp; rfl

/-- The null event has probability 0. -/
theorem p_empty (p : Fap E) : p.p ⟨∅, E.empty_mem⟩ = 0 := by
  have h := p.additive ⟨∅, E.empty_mem⟩ ⟨Set.univ, E.univ_mem⟩ disjoint_bot_left
  have hu : (⟨(∅ : Set X) ∪ Set.univ, E.union_mem E.empty_mem E.univ_mem⟩ :
      {s : Set X // s ∈ E}) = ⟨Set.univ, E.univ_mem⟩ :=
    Subtype.ext (Set.empty_union _)
  rw [hu, p.p_univ] at h
  linarith

/-- Monotonicity along inclusion of members. -/
theorem mono (p : Fap E) {s t : {s : Set X // s ∈ E}} (h : s.val ⊆ t.val) :
    p.p s ≤ p.p t := by
  have hdiff : t.val \ s.val ∈ E := by
    rw [Set.diff_eq]
    exact E.inter_mem t.2 (E.compl_mem s.2)
  have hadd := p.additive s ⟨t.val \ s.val, hdiff⟩
    (Set.disjoint_left.mpr fun _ ha hmem => hmem.2 ha)
  have hun : (⟨s.val ∪ t.val \ s.val, E.union_mem s.2 hdiff⟩ :
      {s : Set X // s ∈ E}) = t :=
    Subtype.ext (Set.union_diff_cancel h)
  rw [hun] at hadd
  have := p.nonneg ⟨t.val \ s.val, hdiff⟩
  linarith

theorem p_le_one (p : Fap E) (s : {s : Set X // s ∈ E}) : p.p s ≤ 1 := by
  have h := p.mono (t := ⟨Set.univ, E.univ_mem⟩) (Set.subset_univ s.val)
  rwa [p.p_univ] at h

/-! ## Mixtures

Convex combinations are defined directly on `Fap` — no ambient module
structure is assumed or needed. -/

/-- The `t`-mixture of two finitely additive probabilities:
`(mix t _ _ p q).p s = t * p.p s + (1 - t) * q.p s`. -/
def mix (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (p q : Fap E) : Fap E where
  p s := t * p.p s + (1 - t) * q.p s
  nonneg s := add_nonneg (mul_nonneg ht₀ (p.nonneg s))
    (mul_nonneg (by linarith) (q.nonneg s))
  p_univ := by rw [p.p_univ, q.p_univ]; ring
  additive s s' hd := by rw [p.additive s s' hd, q.additive s s' hd]; ring

@[simp]
theorem mix_p (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (p q : Fap E)
    (s : {s : Set X // s ∈ E}) :
    (mix t ht₀ ht₁ p q).p s = t * p.p s + (1 - t) * q.p s :=
  rfl

@[simp]
theorem mix_zero (p q : Fap E) : mix 0 le_rfl zero_le_one p q = q :=
  ext fun s => by simp

@[simp]
theorem mix_one (p q : Fap E) : mix 1 zero_le_one le_rfl p q = p :=
  ext fun s => by simp

@[simp]
theorem mix_self (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (p : Fap E) :
    mix t ht₀ ht₁ p p = p :=
  ext fun s => by rw [mix_p]; ring

/-! ## Convex hull as a closure operator -/

/-- A class of finitely additive probabilities is mixture-closed if it
contains every binary mixture of its members. -/
def MixtureClosed (P : Set (Fap E)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1),
    mix t ht₀ ht₁ p q ∈ P

/-- Mixture-closedness is stable under arbitrary intersections. -/
theorem mixtureClosed_sInter {𝒬 : Set (Set (Fap E))}
    (h : ∀ Q ∈ 𝒬, MixtureClosed Q) : MixtureClosed (⋂₀ 𝒬) :=
  fun p hp q hq t ht₀ ht₁ =>
    Set.mem_sInter.mpr fun Q hQ =>
      h Q hQ p (Set.mem_sInter.mp hp Q hQ) q (Set.mem_sInter.mp hq Q hQ) t ht₀ ht₁

/-- The convex hull of a class of finitely additive probabilities — the
least mixture-closed extension — as a closure operator on `Set (Fap E)`.
This is the credal-side closure; contrast it with the judgment-side
`commensurationClosure`, which closes under joins, not mixtures. -/
def convexHull : ClosureOperator (Set (Fap E)) where
  toFun P := ⋂₀ {Q | P ⊆ Q ∧ MixtureClosed Q}
  monotone' _ _ h :=
    Set.sInter_subset_sInter fun _ hQ => ⟨h.trans hQ.1, hQ.2⟩
  le_closure' _ := fun _ hq => Set.mem_sInter.mpr fun _ hQ => hQ.1 hq
  idempotent' P := by
    apply subset_antisymm
    · exact Set.sInter_subset_of_mem
        ⟨subset_rfl, mixtureClosed_sInter fun _ hQ => hQ.2⟩
    · refine Set.sInter_subset_sInter fun Q hQ => ⟨?_, hQ.2⟩
      exact Set.Subset.trans
        (fun _ hq => Set.mem_sInter.mpr fun _ hR => hR.1 hq) hQ.1

theorem subset_convexHull (P : Set (Fap E)) : P ⊆ convexHull P :=
  convexHull.le_closure' P

/-- The convex hull of any class is mixture-closed. -/
theorem mixtureClosed_convexHull (P : Set (Fap E)) :
    MixtureClosed (convexHull P) :=
  mixtureClosed_sInter fun _ hQ => hQ.2

/-- Minimality: the convex hull is contained in every mixture-closed
extension of the base class. -/
theorem convexHull_le {P Q : Set (Fap E)} (hPQ : P ⊆ Q)
    (hQ : MixtureClosed Q) : convexHull P ⊆ Q :=
  Set.sInter_subset_of_mem ⟨hPQ, hQ⟩

/-- The closed classes of the convex hull operator are exactly the
mixture-closed ones. -/
theorem isClosed_convexHull_iff {P : Set (Fap E)} :
    convexHull.IsClosed P ↔ MixtureClosed P := by
  rw [convexHull.isClosed_iff]
  constructor
  · intro h
    rw [← h]
    exact mixtureClosed_convexHull P
  · intro h
    exact subset_antisymm (convexHull_le subset_rfl h) (subset_convexHull P)

end Fap

end CAJ
