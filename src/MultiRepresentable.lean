/-
# Multi-Rationalizability

Levi's theory of E-admissibility, and more broadly the
Seidenfeld–Schervish–Kadane / Walley imprecise-probability tradition,
generalize subjective expected utility theory by replacing a *single*
prior–utility pair with a *family* (typically a credal set of priors,
or a set of utility functions, or both). Their choice rule is *not*
rationalizable by a single weak order on alternatives: an alternative
is admissible from a menu iff it is best under *some* member of the
family.

This module formalizes the corresponding revealed-preference layer.
A `ConditionalJudgment` is *multi-representable* on event `e` by a
family of relations `ℛ` if its choice function picks, on every menu,
exactly the alternatives that are maximal under *some* member of `ℛ`.
The single-relation case (`ℛ = {R}`) recovers `Representable`.

Two preference notions arise immediately at the multi-relation layer:

* the *cautious* (a.k.a. unanimity, Bewley) relation
  `Cautious ℛ a b := ∀ R ∈ ℛ, R a b`, which is reflexive and
  transitive when each `R ∈ ℛ` is, but typically *not total* — and so
  exhibits genuine **incomparability**;
* the *bold* (E-admissible) acceptance, captured directly by
  `MultiRepresentable`.

Levi, Seidenfeld, and others insist on distinguishing incomparability
from indifference. Single-relation rationalizability conflates the two
under WARP (totality forces no incomparable pair); multi-rationalizability
does not. The development here makes that distinction first-class.

## A negative result on the `Fin 3` rep-without-WARP example

The `Fin 3` example in `test/Fin3RepNotWARP.lean` is `Representable`
without WARP, but it is **not** multi-rationalizable by a family of
weak orders. Every weak order in such a family would have to satisfy
`act 0 ≥ act 2` (since `act 2 ∉ C({act 0, act 2})`) and
`act 2 > act 1` strictly (since `act 1 ∉ C({act 1, act 2})`); by
transitivity `act 0 > act 1` strictly in every member; but then no
member would have `act 1` maximal in `{act 0, act 1}`, contradicting
`act 1 ∈ C({act 0, act 1})`. The formal proof is given below as
`fin3_not_multiRepresentable_by_weakOrders` (in the dedicated test
file; cross-referenced here for orientation).

This shows multi-rationalizability by weak orders is *strictly
stronger* than single-relation representability — exactly the gap a
genuinely Levi-style example needs to fall into.
-/

import RevealedPreference

namespace ConditionalChoice

universe u v

/-! ## The multi-representability predicate -/

/-- The set of alternatives in `m` that are `R`-maximal for some
    `R ∈ ℛ`. -/
def multiMaxSet {X : Type u} {K : Type v}
    (ℛ : Set ((X → K) → (X → K) → Prop)) (m : Set (X → K)) : Set (X → K) :=
  { a | a ∈ m ∧ ∃ R ∈ ℛ, ∀ a' ∈ m, R a a' }

/-- `χ.C e ·` is *multi-representable* by the family `ℛ` of relations
    on `X → K` if, on every menu, the choice set is exactly the union
    of the `R`-maximal sets, ranging over `R ∈ ℛ`. -/
def MultiRepresentable {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e : Set X)
    (ℛ : Set ((X → K) → (X → K) → Prop)) : Prop :=
  ∀ m ∈ χ.M, χ.C e m = multiMaxSet ℛ m

/-! ## Reduction to the single-relation case -/

/-- For the singleton family `{R}`, the multi-max set is the ordinary
    `R`-max set. -/
theorem multiMaxSet_singleton {X : Type u} {K : Type v}
    (R : (X → K) → (X → K) → Prop) (m : Set (X → K)) :
    multiMaxSet ({R} : Set _) m = { a | a ∈ m ∧ ∀ a' ∈ m, R a a' } := by
  ext a
  simp only [multiMaxSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hm, R', rfl, hmax⟩
    exact ⟨hm, hmax⟩
  · rintro ⟨hm, hmax⟩
    exact ⟨hm, R, rfl, hmax⟩

/-- For the singleton family `{R_e}` where `R_e := RevealedPref χ e`,
    `MultiRepresentable` reduces to `Representable`. -/
theorem multiRepresentable_singleton_iff_representable {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e : Set X) :
    MultiRepresentable χ e ({RevealedPref χ e} : Set _) ↔
      Representable χ e := by
  unfold MultiRepresentable Representable
  constructor
  · intro h m hm
    rw [h m hm, multiMaxSet_singleton]
    rfl
  · intro h m hm
    rw [h m hm, multiMaxSet_singleton]
    rfl

/-! ## The cautious (unanimity / Bewley) relation -/

/-- The *cautious* preference relation induced by a family `ℛ` of
    relations: `a` is cautiously preferred to `b` iff *every* member of
    `ℛ` ranks `a` above `b`. This is the formal counterpart of Levi's
    "robust dominance" and Bewley's incomplete preference. -/
def Cautious {X : Type u} {K : Type v}
    (ℛ : Set ((X → K) → (X → K) → Prop)) (a b : X → K) : Prop :=
  ∀ R ∈ ℛ, R a b

/-- Cautious incomparability: neither alternative is cautiously
    preferred to the other. Crucially, this is *not* the same as
    cautious indifference (`Cautious ℛ a b ∧ Cautious ℛ b a`). -/
def CautiousIncomp {X : Type u} {K : Type v}
    (ℛ : Set ((X → K) → (X → K) → Prop)) (a b : X → K) : Prop :=
  ¬ Cautious ℛ a b ∧ ¬ Cautious ℛ b a

theorem cautiousIncomp_symm {X : Type u} {K : Type v}
    {ℛ : Set ((X → K) → (X → K) → Prop)} {a b : X → K} :
    CautiousIncomp ℛ a b → CautiousIncomp ℛ b a :=
  fun ⟨h, h'⟩ => ⟨h', h⟩

/-- If every relation in `ℛ` is reflexive at `a`, then `Cautious ℛ` is
    reflexive at `a` (so `CautiousIncomp ℛ a a` is false). -/
theorem cautious_refl {X : Type u} {K : Type v}
    {ℛ : Set ((X → K) → (X → K) → Prop)} {a : X → K}
    (hrefl : ∀ R ∈ ℛ, R a a) : Cautious ℛ a a := hrefl

/-- If every `R ∈ ℛ` is transitive at `(a, b, c)`, then `Cautious ℛ` is
    transitive at `(a, b, c)`. -/
theorem cautious_trans {X : Type u} {K : Type v}
    {ℛ : Set ((X → K) → (X → K) → Prop)} {a b c : X → K}
    (htr : ∀ R ∈ ℛ, R a b → R b c → R a c) :
    Cautious ℛ a b → Cautious ℛ b c → Cautious ℛ a c := by
  intro hab hbc R hR
  exact htr R hR (hab R hR) (hbc R hR)

/-! ## Singleton families: `Cautious {R} = R`

When the family is a singleton, the cautious relation is exactly that
single relation, so `CautiousIncomp` reduces to single-relation
incomparability. This is the precise sense in which incomparability
is *invisible* in the single-relation setting whenever the unique
relation is total — and *visible* the moment we admit a non-singleton
family. -/

theorem cautious_singleton {X : Type u} {K : Type v}
    (R : (X → K) → (X → K) → Prop) (a b : X → K) :
    Cautious ({R} : Set _) a b ↔ R a b := by
  unfold Cautious
  simp only [Set.mem_singleton_iff, forall_eq]

theorem cautiousIncomp_singleton {X : Type u} {K : Type v}
    (R : (X → K) → (X → K) → Prop) (a b : X → K) :
    CautiousIncomp ({R} : Set _) a b ↔ ¬ R a b ∧ ¬ R b a := by
  unfold CautiousIncomp
  rw [cautious_singleton, cautious_singleton]

end ConditionalChoice
