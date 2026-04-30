/-
# Strict Preference, Indifference, and Incomparability

This module develops the standard four-way classification of pairs of
alternatives `(a, b) ∈ χ.A × χ.A` induced by the revealed-preference
relation `R_e`:

|                | `R_e a b`           | `¬ R_e a b`           |
|----------------|---------------------|-----------------------|
| `R_e b a`      | `Indiff χ e a b`    | `StrictPref χ e b a`  |
| `¬ R_e b a`    | `StrictPref χ e a b`| `Incomp χ e a b`      |

`StrictPref` and `Indiff` are already defined in
`RevealedPreference.lean`. We add `Incomp` here, prove its symmetry
and irreflexivity-on-`χ.A`, and establish the conceptually central
theorem:

> Under `MenuClosure` and `WARPAt`, no pair of alternatives in `χ.A`
> is incomparable.

This is the precise sense in which WARP collapses incomparability
into indifference — and the precise feature that fails in Levi's and
Seidenfeld–Schervish–Kadane's settings, where `R_e` is replaced by a
family of weak orders. The connection to `MultiRepresentable.lean`
and `CautiousIncomp` is documented at the end of the file.

We also collect the standard structural facts about `StrictPref` and
`Indiff` under WARP:

* `StrictPref` is asymmetric and transitive on `χ.A`.
* `Indiff` is reflexive, symmetric, and transitive on `χ.A` — i.e.,
  an equivalence relation on `χ.A`.

Pullbacks to consequences are recorded in
`StrictIndiffIncompK.lean` (deferred); within this module we work
purely at the alternative level.
-/

import RevealedPreference

namespace ConditionalChoice

universe u v

/-! ## Incomparability -/

/-- Revealed *incomparability*: neither `a R_e b` nor `b R_e a`. -/
def Incomp {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) (a b : X → K) : Prop :=
  ¬ RevealedPref χ e a b ∧ ¬ RevealedPref χ e b a

theorem incomp_symm {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X} {a b : X → K} :
    Incomp χ e a b → Incomp χ e b a :=
  fun ⟨h, h'⟩ => ⟨h', h⟩

/-- Incomparability is irreflexive on `χ.A`: no alternative is
    incomparable with itself, because `R_e` is reflexive on `χ.A`
    under `MenuClosure`. -/
theorem not_incomp_self {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) {a : X → K} (ha : a ∈ χ.A) :
    ¬ Incomp χ e a a :=
  fun ⟨h, _⟩ => h (revealedPref_refl_at hM he a ha)

/-! ## The trichotomy -/

/-- For any two alternatives, exactly one of the four cells obtains:
    indifference, strict-preference (in either direction), or
    incomparability. The four are pairwise mutually exclusive and
    cover every pair. -/
theorem trichotomy {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X} (a b : X → K) :
    Indiff χ e a b ∨ StrictPref χ e a b ∨ StrictPref χ e b a ∨
      Incomp χ e a b := by
  by_cases hab : RevealedPref χ e a b
  · by_cases hba : RevealedPref χ e b a
    · exact Or.inl ⟨hab, hba⟩
    · exact Or.inr (Or.inl ⟨hab, hba⟩)
  · by_cases hba : RevealedPref χ e b a
    · exact Or.inr (Or.inr (Or.inl ⟨hba, hab⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hab, hba⟩))

/-! ## WARP collapses incomparability

The conceptually central fact: under `MenuClosure` and `WARPAt`,
`R_e` is total on `χ.A`, so `Incomp` is empty on `χ.A`. -/

/-- Under `MenuClosure` and `WARPAt`, no pair of alternatives in
    `χ.A` is incomparable. This is the formal statement of "WARP
    collapses incomparability into indifference." -/
theorem not_incomp_of_warp {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E)
    {a b : X → K} (ha : a ∈ χ.A) (hb : b ∈ χ.A) :
    ¬ Incomp χ e a b := by
  intro ⟨hab, hba⟩
  rcases revealedPref_total_at hM he a b ha hb with h | h
  · exact hab h
  · exact hba h

/-! ## Structural properties of `StrictPref` -/

/-- Strict preference is asymmetric (already noted in
    `RevealedPreference.lean`; restated here for completeness). -/
theorem strictPref_asymm' {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X} {a b : X → K} :
    StrictPref χ e a b → ¬ StrictPref χ e b a :=
  strictPref_asymm

/-- Strict preference is irreflexive on `χ.A` under `MenuClosure`. -/
theorem strictPref_irrefl {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) {a : X → K} (ha : a ∈ χ.A) :
    ¬ StrictPref χ e a a :=
  fun ⟨_, hn⟩ => hn (revealedPref_refl_at hM he a ha)

/-- Under `MenuClosure` and `WARPAt`, strict preference is transitive
    on `χ.A`. -/
theorem strictPref_trans {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) (hWARP : WARPAt χ e)
    {a b c : X → K} (ha : a ∈ χ.A) (hb : b ∈ χ.A) (hc : c ∈ χ.A) :
    StrictPref χ e a b → StrictPref χ e b c → StrictPref χ e a c := by
  rintro ⟨hab, hnba⟩ ⟨hbc, hncb⟩
  have htr := revealedPref_trans_via_warp hM he hWARP
  refine ⟨htr a b c ha hb hc hab hbc, ?_⟩
  intro hca
  -- From hca and hab via transitivity: R_e c b. Combined with hbc
  -- this would give Indiff c b — but hncb says ¬ R_e c b. Contradiction.
  have hcb : RevealedPref χ e c b := htr c a b hc ha hb hca hab
  exact hncb hcb

/-! ## Structural properties of `Indiff` -/

/-- Indifference is reflexive on `χ.A` under `MenuClosure`. -/
theorem indiff_refl {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) {a : X → K} (ha : a ∈ χ.A) :
    Indiff χ e a a :=
  ⟨revealedPref_refl_at hM he a ha, revealedPref_refl_at hM he a ha⟩

/-- Symmetry of indifference (already in `RevealedPreference.lean`;
    restated for the structural-axioms section). -/
theorem indiff_symm' {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X} {a b : X → K} :
    Indiff χ e a b → Indiff χ e b a := indiff_symm

/-- Under `MenuClosure` and `WARPAt`, indifference is transitive on
    `χ.A`. -/
theorem indiff_trans {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) (hWARP : WARPAt χ e)
    {a b c : X → K} (ha : a ∈ χ.A) (hb : b ∈ χ.A) (hc : c ∈ χ.A) :
    Indiff χ e a b → Indiff χ e b c → Indiff χ e a c := by
  rintro ⟨hab, hba⟩ ⟨hbc, hcb⟩
  have htr := revealedPref_trans_via_warp hM he hWARP
  exact ⟨htr a b c ha hb hc hab hbc, htr c b a hc hb ha hcb hba⟩

/-- Under `MenuClosure` and `WARPAt`, indifference is an equivalence
    relation on `χ.A`. -/
theorem indiff_equiv {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) (hWARP : WARPAt χ e) :
    (∀ a ∈ χ.A, Indiff χ e a a) ∧
    (∀ a b : X → K, Indiff χ e a b → Indiff χ e b a) ∧
    (∀ a b c : X → K, a ∈ χ.A → b ∈ χ.A → c ∈ χ.A →
      Indiff χ e a b → Indiff χ e b c → Indiff χ e a c) :=
  ⟨ fun _ ha => indiff_refl hM he ha,
    fun _ _ => indiff_symm,
    fun _ _ _ ha hb hc => indiff_trans hM he hWARP ha hb hc ⟩

end ConditionalChoice
