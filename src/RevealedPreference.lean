/-
# Revealed Preference on Alternatives

This module formalizes the Sen-style theory of revealed preference for a
`ConditionalJudgment χ : ConditionalJudgment X K`, working at the level of
*alternatives* (`χ.A`) rather than consequences. For each event `e ∈ χ.E`
the *base relation* `RevealedPref χ e a a'` is defined, and the standard
choice-consistency axioms (Sen's α, β, γ; WARP) are introduced. The main
theorems address two questions:

* (Q1) Under what conditions on `χ` is `R_e` a *weak ordering* on `χ.A`
  (reflexive, transitive, total)?
* (Q2) Under what conditions on `χ` is `χ.C` *representable* by `R_e`?

See `prompts/PLAN_FOR_REVEALED_PREFERENCE_ON_A.md` for the design plan.

## Findings recorded during implementation

* The plan proposed a `MenuClosure` predicate with three clauses (singleton,
  pair, triple). To formulate `chosen_is_maximal` so that it type-checks
  with the `RevealedPref` defined on alternatives, the additional clause
  `menu_subset_alt : ∀ m ∈ χ.M, m ⊆ χ.A` is needed and has been added.

* The plan listed an "α + γ" route (Route A) to transitivity of `R_e`.
  This is **not provable** under just `MenuClosure`: a counterexample is
  given by a choice function on three alternatives that satisfies α + γ
  (and even is fully representable) yet whose `R_e` is not transitive
  (see `test/RevealedPreferenceExamples.lean`). Only the WARP route to
  transitivity is established here.

* Likewise, the plan listed `representable_iff_warp` as a target. The
  forward direction (`Representable → WARP`) **fails** under `MenuClosure`
  (same counterexample). What does hold under `MenuClosure` is:
  `WARP → Representable`, `Representable → α`, `Representable → γ`,
  `WARP ↔ α ∧ β`. The classical Arrow-Sen equivalence requires stronger
  closure (e.g., `χ.M` containing all finite nonempty subsets of `χ.A`)
  and is deferred.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import ConditionalJudgment

namespace ConditionalChoice

universe u v

/-! ## Choice nonemptiness -/

/-- The choice set `χ.C e m` is nonempty whenever `e ∈ χ.E` and `m ∈ χ.M`.
    This is a direct consequence of `C_in_M` and `M_elements_nonempty`. -/
theorem ConditionalJudgment.choice_nonempty {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) {e : Set X} {m : Set (X → K)}
    (he : e ∈ χ.E) (hm : m ∈ χ.M) : (χ.C e m).Nonempty :=
  χ.M_elements_nonempty _ (χ.C_in_M e m he hm)

/-! ## The revealed-preference relation -/

/-- The revealed-preference relation `R_e` on alternatives:
    `a R_e a'` iff some menu containing both `a` and `a'` is in `χ.M`
    and `a` is admissible from that menu under `e`. -/
def RevealedPref {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) (a a' : X → K) : Prop :=
  ∃ m ∈ χ.M, a ∈ m ∧ a' ∈ m ∧ a ∈ χ.C e m

/-- Strict revealed preference: `a P_e a'` iff `a R_e a'` and not `a' R_e a`. -/
def StrictPref {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) (a a' : X → K) : Prop :=
  RevealedPref χ e a a' ∧ ¬ RevealedPref χ e a' a

/-- Revealed indifference: `a I_e a'` iff `a R_e a'` and `a' R_e a`. -/
def Indiff {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) (a a' : X → K) : Prop :=
  RevealedPref χ e a a' ∧ RevealedPref χ e a' a

theorem strictPref_asymm {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X} {a a' : X → K} :
    StrictPref χ e a a' → ¬ StrictPref χ e a' a := by
  intro ⟨_, hn⟩ ⟨h', _⟩; exact hn h'

theorem indiff_symm {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X} {a a' : X → K} :
    Indiff χ e a a' → Indiff χ e a' a :=
  fun ⟨h, h'⟩ => ⟨h', h⟩

theorem revealedPref_iff_strict_or_indiff {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X} {a a' : X → K} :
    RevealedPref χ e a a' ↔ StrictPref χ e a a' ∨ Indiff χ e a a' := by
  constructor
  · intro h
    by_cases h' : RevealedPref χ e a' a
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl ⟨h, h'⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

/-! ## Closure conditions on `χ.M`

The Sen-style theorems require that pair- and triple-submenus drawn from
`χ.A` are themselves elements of `χ.M`. We bundle this as a structural
predicate. The clause `menu_subset_alt` (every menu is a subset of the
alternative space) is a discovered necessity beyond the original plan;
without it `chosen_is_maximal` cannot quote `pair_mem` for an arbitrary
member of a menu. -/

/-- Closure conditions on `χ.M` needed for the standard revealed-preference
    theorems. -/
structure MenuClosure {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) : Prop where
  /-- Every menu is a subset of `χ.A`. -/
  menu_subset_alt : ∀ m ∈ χ.M, m ⊆ χ.A
  /-- Every singleton drawn from `χ.A` is a menu. -/
  singleton_mem : ∀ a ∈ χ.A, ({a} : Set (X → K)) ∈ χ.M
  /-- Every (unordered) pair of alternatives is a menu. -/
  pair_mem : ∀ a a' : X → K, a ∈ χ.A → a' ∈ χ.A →
    ({a, a'} : Set (X → K)) ∈ χ.M
  /-- Every (unordered) triple of alternatives is a menu. -/
  triple_mem : ∀ a a' a'' : X → K, a ∈ χ.A → a' ∈ χ.A → a'' ∈ χ.A →
    ({a, a', a''} : Set (X → K)) ∈ χ.M

/-! ## Choice-consistency axioms -/

/-- Sen's α (Chernoff / contraction), per event. If `a` is admissible from
    `m` under `e` and `m' ⊆ m` is also a menu containing `a`, then `a` is
    admissible from `m'`. -/
def AxiomAlphaAt {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) : Prop :=
  ∀ m m', m ∈ χ.M → m' ∈ χ.M → m' ⊆ m →
    ∀ a, a ∈ m' → a ∈ χ.C e m → a ∈ χ.C e m'

/-- Event-uniform Sen's α. -/
def AxiomAlpha {X : Type u} {K : Type v} (χ : ConditionalJudgment X K) : Prop :=
  ∀ e ∈ χ.E, AxiomAlphaAt χ e

/-- Sen's β (expansion of bests), per event. If `m' ⊆ m` and two alternatives
    `a, a'` are both admissible from `m'`, then they agree on admissibility
    from the larger menu `m`. -/
def AxiomBetaAt {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) : Prop :=
  ∀ m m', m ∈ χ.M → m' ∈ χ.M → m' ⊆ m →
    ∀ a a', a ∈ m' → a' ∈ m' →
      a ∈ χ.C e m' → a' ∈ χ.C e m' →
      (a ∈ χ.C e m ↔ a' ∈ χ.C e m)

/-- Event-uniform Sen's β. -/
def AxiomBeta {X : Type u} {K : Type v} (χ : ConditionalJudgment X K) : Prop :=
  ∀ e ∈ χ.E, AxiomBetaAt χ e

/-- Sen's γ (binary form), per event. If `a` is admissible from each of two
    menus `m₁, m₂` (whose union is also a menu), then `a` is admissible from
    the union. -/
def AxiomGammaAt {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) : Prop :=
  ∀ m₁ m₂, m₁ ∈ χ.M → m₂ ∈ χ.M → m₁ ∪ m₂ ∈ χ.M →
    ∀ a, a ∈ χ.C e m₁ → a ∈ χ.C e m₂ → a ∈ χ.C e (m₁ ∪ m₂)

/-- Event-uniform Sen's γ. -/
def AxiomGamma {X : Type u} {K : Type v} (χ : ConditionalJudgment X K) : Prop :=
  ∀ e ∈ χ.E, AxiomGammaAt χ e

/-- The Weak Axiom of Revealed Preference, per event. -/
def WARPAt {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) : Prop :=
  ∀ m m', m ∈ χ.M → m' ∈ χ.M →
    ∀ a a', a ∈ m → a ∈ m' → a' ∈ m → a' ∈ m' →
      a ∈ χ.C e m → a' ∈ χ.C e m' → a ∈ χ.C e m'

/-- Event-uniform WARP. -/
def WARP {X : Type u} {K : Type v} (χ : ConditionalJudgment X K) : Prop :=
  ∀ e ∈ χ.E, WARPAt χ e

/-! ## Equivalences among axioms -/

/-- WARP implies Sen's α. -/
theorem warpAt_imp_alphaAt {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X} (he : e ∈ χ.E)
    (hWARP : WARPAt χ e) : AxiomAlphaAt χ e := by
  intro m m' hm hm' hsub a ha_in_m' ha_in_C
  rcases χ.choice_nonempty he hm' with ⟨a', ha'⟩
  have ha'_in_m' : a' ∈ m' := χ.C_subset_menu e m' he hm' ha'
  have ha'_in_m  : a' ∈ m  := hsub ha'_in_m'
  have ha_in_m   : a  ∈ m  := hsub ha_in_m'
  exact hWARP m m' hm hm' a a' ha_in_m ha_in_m' ha'_in_m ha'_in_m' ha_in_C ha'

/-- WARP implies Sen's β. -/
theorem warpAt_imp_betaAt {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X} (_he : e ∈ χ.E)
    (hWARP : WARPAt χ e) : AxiomBetaAt χ e := by
  intro m m' hm hm' hsub a a' ha_in_m' ha'_in_m' ha_in_C' ha'_in_C'
  have ha_in_m  : a  ∈ m := hsub ha_in_m'
  have ha'_in_m : a' ∈ m := hsub ha'_in_m'
  refine ⟨?_, ?_⟩
  · intro ha_in_C
    -- Apply WARP with menus (m', m), elements (a', a).
    exact hWARP m' m hm' hm a' a ha'_in_m' ha'_in_m ha_in_m' ha_in_m
      ha'_in_C' ha_in_C
  · intro ha'_in_C
    -- Symmetric application.
    exact hWARP m' m hm' hm a a' ha_in_m' ha_in_m ha'_in_m' ha'_in_m
      ha_in_C' ha'_in_C

/-- Sen's α together with β implies WARP, under `MenuClosure`. -/
theorem alphaAt_betaAt_imp_warpAt {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (_he : e ∈ χ.E)
    (hα : AxiomAlphaAt χ e) (hβ : AxiomBetaAt χ e) : WARPAt χ e := by
  intro m m' hm hm' a a' ha_m ha_m' ha'_m ha'_m' ha_C ha'_C
  -- Construct the pair menu {a, a'}.
  have ha_alt  : a  ∈ χ.A := hM.menu_subset_alt m hm ha_m
  have ha'_alt : a' ∈ χ.A := hM.menu_subset_alt m hm ha'_m
  set p : Set (X → K) := ({a, a'} : Set (X → K)) with hp_def
  have hp : p ∈ χ.M := hM.pair_mem a a' ha_alt ha'_alt
  have ha_in_p  : a  ∈ p := by simp [hp_def]
  have ha'_in_p : a' ∈ p := by simp [hp_def]
  have hp_sub_m  : p ⊆ m := by
    intro x hx
    rcases hx with rfl | hx
    · exact ha_m
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact ha'_m
  have hp_sub_m' : p ⊆ m' := by
    intro x hx
    rcases hx with rfl | hx
    · exact ha_m'
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact ha'_m'
  -- α gives a, a' ∈ C(e, p).
  have ha_in_Cp  : a  ∈ χ.C e p := hα m  p hm  hp hp_sub_m  a  ha_in_p  ha_C
  have ha'_in_Cp : a' ∈ χ.C e p := hα m' p hm' hp hp_sub_m' a' ha'_in_p ha'_C
  -- β with (m', p) and elements a, a': a ∈ C(m') ↔ a' ∈ C(m').
  have hβ_iff := hβ m' p hm' hp hp_sub_m' a a' ha_in_p ha'_in_p
                    ha_in_Cp ha'_in_Cp
  exact hβ_iff.mpr ha'_C

/-- WARP is equivalent to (α ∧ β), under `MenuClosure`. -/
theorem warpAt_iff_alphaAt_betaAt {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) :
    WARPAt χ e ↔ AxiomAlphaAt χ e ∧ AxiomBetaAt χ e := by
  refine ⟨fun h => ⟨warpAt_imp_alphaAt he h, warpAt_imp_betaAt he h⟩, ?_⟩
  rintro ⟨hα, hβ⟩
  exact alphaAt_betaAt_imp_warpAt hM he hα hβ

/-! ## Reflexivity, totality, transitivity -/

/-- `R_e` is reflexive on `χ.A` (uses singleton closure). -/
theorem revealedPref_refl_at {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) :
    ∀ a ∈ χ.A, RevealedPref χ e a a := by
  intro a ha
  have hsing : ({a} : Set (X → K)) ∈ χ.M := hM.singleton_mem a ha
  rcases χ.choice_nonempty he hsing with ⟨b, hb⟩
  have hb_in : b ∈ ({a} : Set (X → K)) := χ.C_subset_menu e {a} he hsing hb
  rw [Set.mem_singleton_iff] at hb_in
  refine ⟨{a}, hsing, rfl, rfl, ?_⟩
  exact hb_in ▸ hb

/-- `R_e` is total on `χ.A` (uses pair closure). -/
theorem revealedPref_total_at {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) :
    ∀ a a', a ∈ χ.A → a' ∈ χ.A →
      RevealedPref χ e a a' ∨ RevealedPref χ e a' a := by
  intro a a' ha ha'
  set p : Set (X → K) := ({a, a'} : Set (X → K)) with hp_def
  have hp : p ∈ χ.M := hM.pair_mem a a' ha ha'
  have ha_in  : a  ∈ p := by simp [hp_def]
  have ha'_in : a' ∈ p := by simp [hp_def]
  rcases χ.choice_nonempty he hp with ⟨x, hx⟩
  have hx_in : x ∈ p := χ.C_subset_menu e p he hp hx
  rcases hx_in with rfl | hx_eq
  · exact Or.inl ⟨p, hp, ha_in, ha'_in, hx⟩
  · rw [Set.mem_singleton_iff] at hx_eq; subst hx_eq
    exact Or.inr ⟨p, hp, ha'_in, ha_in, hx⟩

/-- `R_e` is transitive on `χ.A`, under WARP and triple closure. -/
theorem revealedPref_trans_via_warp {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) (hWARP : WARPAt χ e) :
    ∀ a b c : X → K, a ∈ χ.A → b ∈ χ.A → c ∈ χ.A →
      RevealedPref χ e a b → RevealedPref χ e b c → RevealedPref χ e a c := by
  intro a b c ha hb hc hab hbc
  obtain ⟨m₁, hm₁, ha_m₁, hb_m₁, ha_C₁⟩ := hab
  obtain ⟨m₂, hm₂, hb_m₂, hc_m₂, hb_C₂⟩ := hbc
  let t : Set (X → K) := ({a, b, c} : Set (X → K))
  have ht : t ∈ χ.M := hM.triple_mem a b c ha hb hc
  have ha_t : a ∈ t := Set.mem_insert _ _
  have hb_t : b ∈ t := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hc_t : c ∈ t := Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  -- Reduce to showing a ∈ C e t.
  suffices hfinal : a ∈ χ.C e t from
    ⟨t, ht, ha_t, hc_t, hfinal⟩
  rcases χ.choice_nonempty he ht with ⟨x, hx⟩
  have hx_in_t : x ∈ ({a, b, c} : Set (X → K)) := χ.C_subset_menu e t he ht hx
  have hx_eq : x = a ∨ x = b ∨ x = c := by
    rcases hx_in_t with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [Set.mem_singleton_iff] at h; exact Or.inr (Or.inr h)
  rcases hx_eq with rfl | rfl | rfl
  · exact hx
  · -- x = b: WARP on (m₁, t), elements (a, b) gives a ∈ C(t).
    exact hWARP m₁ t hm₁ ht a x ha_m₁ ha_t hb_m₁ hb_t ha_C₁ hx
  · -- x = c: WARP on (m₂, t), elements (b, c) gives b ∈ C(t);
    -- then WARP on (m₁, t), elements (a, b) gives a ∈ C(t).
    have hb_Ct : b ∈ χ.C e t :=
      hWARP m₂ t hm₂ ht b x hb_m₂ hb_t hc_m₂ hc_t hb_C₂ hx
    exact hWARP m₁ t hm₁ ht a b ha_m₁ ha_t hb_m₁ hb_t ha_C₁ hb_Ct

/-- `R_e` is a weak ordering on `χ.A`: reflexive, transitive, total. -/
def WeakOrderingAt {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e : Set X) : Prop :=
  (∀ a ∈ χ.A, RevealedPref χ e a a) ∧
  (∀ a b c : X → K, a ∈ χ.A → b ∈ χ.A → c ∈ χ.A →
      RevealedPref χ e a b → RevealedPref χ e b c → RevealedPref χ e a c) ∧
  (∀ a a', a ∈ χ.A → a' ∈ χ.A →
      RevealedPref χ e a a' ∨ RevealedPref χ e a' a)

/-- Under `MenuClosure` and WARP, `R_e` is a weak ordering. -/
theorem revealedPref_weakOrder_at {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) (hWARP : WARPAt χ e) :
    WeakOrderingAt χ e :=
  ⟨ revealedPref_refl_at hM he,
    revealedPref_trans_via_warp hM he hWARP,
    revealedPref_total_at hM he ⟩

/-! ## Representability

The max-set induced by `R_e` and the predicate that `χ.C e ·` selects
exactly the `R_e`-maxima of each menu. -/

/-- The set of `R_e`-maximal elements of a menu `m`. -/
def maxSet {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) (m : Set (X → K)) : Set (X → K) :=
  { a | a ∈ m ∧ ∀ a' ∈ m, RevealedPref χ e a a' }

/-- `χ.C e ·` is *representable* by `R_e` if it picks exactly the
    `R_e`-maxima from each menu. -/
def Representable {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e : Set X) : Prop :=
  ∀ m ∈ χ.M, χ.C e m = maxSet χ e m

/-- The "easy" half of representability: under α and `MenuClosure`, every
    chosen alternative is `R_e`-maximal. -/
theorem chosen_is_maximal {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) (hα : AxiomAlphaAt χ e) :
    ∀ m ∈ χ.M, χ.C e m ⊆ maxSet χ e m := by
  intro m hm a ha
  have ha_in_m : a ∈ m := χ.C_subset_menu e m he hm ha
  refine ⟨ha_in_m, ?_⟩
  intro a' ha'_in_m
  have ha_alt  : a  ∈ χ.A := hM.menu_subset_alt m hm ha_in_m
  have ha'_alt : a' ∈ χ.A := hM.menu_subset_alt m hm ha'_in_m
  set p : Set (X → K) := ({a, a'} : Set (X → K)) with hp_def
  have hp : p ∈ χ.M := hM.pair_mem a a' ha_alt ha'_alt
  have hp_sub : p ⊆ m := by
    intro x hx
    rcases hx with rfl | hx
    · exact ha_in_m
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact ha'_in_m
  have ha_in_p  : a  ∈ p := by simp [hp_def]
  have ha'_in_p : a' ∈ p := by simp [hp_def]
  exact ⟨p, hp, ha_in_p, ha'_in_p, hα m p hm hp hp_sub a ha_in_p ha⟩

/-- The substantive half of representability: under WARP, every
    `R_e`-maximal alternative is admissible. -/
theorem max_is_chosen_under_warp {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X} (he : e ∈ χ.E)
    (hWARP : WARPAt χ e) :
    ∀ m ∈ χ.M, maxSet χ e m ⊆ χ.C e m := by
  intro m hm a ha
  obtain ⟨ha_in_m, ha_max⟩ := ha
  rcases χ.choice_nonempty he hm with ⟨a', ha'⟩
  have ha'_in_m : a' ∈ m := χ.C_subset_menu e m he hm ha'
  obtain ⟨mw, hmw, ha_in_mw, ha'_in_mw, ha_in_Cmw⟩ := ha_max a' ha'_in_m
  exact hWARP mw m hmw hm a a' ha_in_mw ha_in_m ha'_in_mw ha'_in_m
    ha_in_Cmw ha'

/-- Under `MenuClosure`, WARP implies representability. -/
theorem representable_of_warp {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) (hWARP : WARPAt χ e) :
    Representable χ e := by
  intro m hm
  apply Set.Subset.antisymm
  · exact chosen_is_maximal hM he (warpAt_imp_alphaAt he hWARP) m hm
  · exact max_is_chosen_under_warp he hWARP m hm

/-- Representability implies Sen's α. -/
theorem representable_imp_alphaAt {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X}
    (hRep : Representable χ e) : AxiomAlphaAt χ e := by
  intro m m' hm hm' hsub a ha_in_m' ha_in_C
  rw [hRep m hm] at ha_in_C
  rw [hRep m' hm']
  obtain ⟨_, hmax⟩ := ha_in_C
  refine ⟨ha_in_m', ?_⟩
  intro a' ha'_in_m'
  exact hmax a' (hsub ha'_in_m')

/-- Representability implies Sen's γ. -/
theorem representable_imp_gammaAt {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} {e : Set X}
    (hRep : Representable χ e) : AxiomGammaAt χ e := by
  intro m₁ m₂ hm₁ hm₂ hu a ha_C₁ ha_C₂
  rw [hRep m₁ hm₁] at ha_C₁
  rw [hRep m₂ hm₂] at ha_C₂
  rw [hRep _ hu]
  obtain ⟨ha_in_m₁, hmax₁⟩ := ha_C₁
  obtain ⟨ha_in_m₂, hmax₂⟩ := ha_C₂
  refine ⟨Or.inl ha_in_m₁, ?_⟩
  intro a' ha'
  rcases ha' with ha'_in_m₁ | ha'_in_m₂
  · exact hmax₁ a' ha'_in_m₁
  · exact hmax₂ a' ha'_in_m₂

/-! ## The sharp equivalence: WARP ↔ Representable ∧ transitive `R_e`

Under `MenuClosure`, WARP is *not* equivalent to `Representable` alone:
representability of `χ.C` by the relation `R_e` is consistent with `R_e`
itself failing to be transitive (see the example in
`test/RevealedPreferenceExamples.lean`). The classical Arrow–Sen
equivalence rationalizes `χ.C` by *some* weak order, not necessarily by
`R_e`.

The conceptually clean strengthening is to add transitivity of `R_e` on
`χ.A` as an explicit conjunct. The result below shows that, under
`MenuClosure`, WARP is precisely the conjunction of representability and
transitivity of the revealed relation. -/

/-- Transitivity of `R_e` restricted to `χ.A`. -/
def TransitiveOnAlt {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e : Set X) : Prop :=
  ∀ a b c : X → K, a ∈ χ.A → b ∈ χ.A → c ∈ χ.A →
    RevealedPref χ e a b → RevealedPref χ e b c → RevealedPref χ e a c

/-- Representability together with transitivity of `R_e` on `χ.A` implies
    WARP. (This direction needs no closure beyond what is already used
    to define the witness menus inside the hypothesis.) -/
theorem warpAt_of_representable_of_transitive {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (_he : e ∈ χ.E)
    (hRep : Representable χ e) (hTr : TransitiveOnAlt χ e) :
    WARPAt χ e := by
  intro m m' hm hm' a a' ha_m ha_m' ha'_m ha'_m' ha_C ha'_C'
  -- From `a ∈ C(e, m) = maxSet(m)`: a R_e a'.
  rw [hRep m hm] at ha_C
  obtain ⟨_, ha_max⟩ := ha_C
  have h_a_Re_a' : RevealedPref χ e a a' := ha_max a' ha'_m
  -- From `a' ∈ C(e, m') = maxSet(m')`: a' R_e b for any b ∈ m'.
  rw [hRep m' hm'] at ha'_C'
  obtain ⟨_, ha'_max⟩ := ha'_C'
  -- Show `a ∈ maxSet(m')` and conclude.
  rw [hRep m' hm']
  refine ⟨ha_m', ?_⟩
  intro b hb
  have hb_alt  : b  ∈ χ.A := hM.menu_subset_alt m' hm' hb
  have ha_alt  : a  ∈ χ.A := hM.menu_subset_alt m  hm  ha_m
  have ha'_alt : a' ∈ χ.A := hM.menu_subset_alt m' hm' ha'_m'
  exact hTr a a' b ha_alt ha'_alt hb_alt h_a_Re_a' (ha'_max b hb)

/-- Sharp equivalence: under `MenuClosure`, WARP holds iff `χ.C` is
    representable by `R_e` *and* `R_e` is transitive on `χ.A`. -/
theorem warpAt_iff_representable_and_transitive {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hM : MenuClosure χ)
    {e : Set X} (he : e ∈ χ.E) :
    WARPAt χ e ↔ Representable χ e ∧ TransitiveOnAlt χ e := by
  refine ⟨fun hWARP => ?_, fun ⟨hRep, hTr⟩ =>
    warpAt_of_representable_of_transitive hM he hRep hTr⟩
  refine ⟨representable_of_warp hM he hWARP, ?_⟩
  exact revealedPref_trans_via_warp hM he hWARP

/-! ## Event-independence (definitions only) -/

/-- Event-independence of the revealed-preference relation: `R_e` and
    `R_{e'}` agree on `χ.A` for all events `e, e' ∈ χ.E`. A deeper study
    of this property — in particular its relation to event-independence
    at the level of `C` and to constant-act structure — is deferred to a
    follow-up module. -/
def EventIndependentR {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) : Prop :=
  ∀ e e', e ∈ χ.E → e' ∈ χ.E →
    ∀ a a', a ∈ χ.A → a' ∈ χ.A →
      (RevealedPref χ e a a' ↔ RevealedPref χ e' a a')

end ConditionalChoice
