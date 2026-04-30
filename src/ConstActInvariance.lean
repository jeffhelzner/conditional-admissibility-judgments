/-
# Constant-Act Menu Invariance

This module introduces the axiom that, on any menu consisting solely of
constant acts, the choice function is independent of the conditioning
event. Conceptually this is the choice-function form of Savage's P3 /
state-independence-of-taste:

  *The agent's preferences over consequences alone do not shift with
  the supposition.*

The axiom is stated as a stand-alone predicate on `ConditionalJudgment`
rather than baked into the structure, keeping the base structure honest
about what is bookkeeping and what is substantive.

The principal payoff: combined with α and `HasConstantActs`, the axiom
implies `EventIndependentRK`. Hence there is a single, canonical
"taste over consequences" relation `R^K`, and Levi-style multi-prior
generalizations can fragment *belief* (the credal set) while keeping
*taste* (the utility on `K`) fixed — which is exactly the conceptual
shape of the Levi / SSK / Walley tradition.
-/

import ConstantActs

namespace ConditionalChoice

universe u v

/-! ## All-constant menus -/

/-- A menu is *all-constant* if every act in it is a constant act. -/
def AllConst {X : Type u} {K : Type v} (m : Set (X → K)) : Prop :=
  ∀ a ∈ m, ∃ k : K, a = constAct k

theorem allConst_singleton {X : Type u} {K : Type v} (k : K) :
    AllConst ({constAct k} : Set (X → K)) := by
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  exact ⟨k, ha⟩

theorem allConst_pair {X : Type u} {K : Type v} (k k' : K) :
    AllConst ({constAct k, constAct k'} : Set (X → K)) := by
  intro a ha
  rcases ha with rfl | ha
  · exact ⟨k, rfl⟩
  · rw [Set.mem_singleton_iff] at ha
    exact ⟨k', ha⟩

/-! ## The invariance axiom -/

/-- *Constant-Act Menu Invariance.* On any menu in `χ.M` consisting
    solely of constant acts, the choice function is the same for every
    conditioning event. This is the choice-function analogue of Savage's
    P3: a state-independent taste over consequences. -/
def ConstActMenuInvariant {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) : Prop :=
  ∀ m ∈ χ.M, AllConst m → ∀ e e', e ∈ χ.E → e' ∈ χ.E →
    χ.C e m = χ.C e' m

/-! ## Pair-menu characterization of `R_e^K`

Under α and `HasConstantActs`, the existential `RevealedPrefK χ e k k'`
is equivalent to a single-witness statement at the canonical pair
menu `{constAct k, constAct k'}`. -/

/-- Pair-menu characterization of `RevealedPrefK`: under α and
    `HasConstantActs`, `k R_e^K k'` iff `constAct k` is admissible from
    the canonical pair menu `{constAct k, constAct k'}` under `e`. -/
theorem revealedPrefK_iff_pair {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hC : HasConstantActs χ)
    {e : Set X} (_he : e ∈ χ.E) (hα : AxiomAlphaAt χ e) (k k' : K) :
    RevealedPrefK χ e k k' ↔
      (constAct k : X → K) ∈
        χ.C e ({constAct k, constAct k'} : Set (X → K)) := by
  set p : Set (X → K) := ({constAct k, constAct k'} : Set (X → K)) with hp_def
  have hp : p ∈ χ.M := hM.pair_mem _ _ (hC k) (hC k')
  have hk_in_p  : (constAct k  : X → K) ∈ p := by simp [hp_def]
  have hk'_in_p : (constAct k' : X → K) ∈ p := by simp [hp_def]
  constructor
  · rintro ⟨m, hm, hk_in_m, hk'_in_m, hk_in_C⟩
    have hp_sub : p ⊆ m := by
      intro x hx
      rcases hx with rfl | hx
      · exact hk_in_m
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hk'_in_m
    exact hα m p hm hp hp_sub (constAct k) hk_in_p hk_in_C
  · intro hk_in_Cp
    exact ⟨p, hp, hk_in_p, hk'_in_p, hk_in_Cp⟩

/-! ## Event-independence of the consequence-level relation -/

/-- **Main theorem.** Under `MenuClosure`, `HasConstantActs`,
    event-uniform α, and `ConstActMenuInvariant`, the consequence-level
    revealed-preference relation `R^K` is event-independent. -/
theorem eventIndependentRK_of_constActMenuInvariant
    {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hC : HasConstantActs χ)
    (hα : AxiomAlpha χ) (hCAMI : ConstActMenuInvariant χ) :
    EventIndependentRK χ := by
  intro e e' he he' k k'
  set p : Set (X → K) := ({constAct k, constAct k'} : Set (X → K)) with hp_def
  have hp : p ∈ χ.M := hM.pair_mem _ _ (hC k) (hC k')
  have hp_const : AllConst p := allConst_pair k k'
  have hCeq : χ.C e p = χ.C e' p :=
    hCAMI p hp hp_const e e' he he'
  rw [revealedPrefK_iff_pair hM hC he  (hα e  he ) k k',
      revealedPrefK_iff_pair hM hC he' (hα e' he') k k']
  rw [hp_def] at hCeq
  rw [hCeq]

/-- Event-uniform WARP form: the same conclusion under `WARP` (which is
    strictly stronger than `AxiomAlpha`). -/
theorem eventIndependentRK_of_constActMenuInvariant_warp
    {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hC : HasConstantActs χ)
    (hWARP : WARP χ) (hCAMI : ConstActMenuInvariant χ) :
    EventIndependentRK χ :=
  eventIndependentRK_of_constActMenuInvariant hM hC
    (fun e he => warpAt_imp_alphaAt he (hWARP e he)) hCAMI

/-! ## A canonical, event-free taste relation on `K`

Once `R^K` is event-independent, we may pick *any* event in `χ.E` and
freeze it as a canonical witness. The resulting binary relation on `K`
is the formal residence of "the agent's taste over consequences." -/

/-- A canonical `K`-level relation, defined relative to a chosen
    witness event `e₀ ∈ χ.E`. Under the hypotheses of
    `eventIndependentRK_of_constActMenuInvariant`, it agrees with
    `RevealedPrefK χ e` for every `e ∈ χ.E`. -/
def CanonicalRK {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e₀ : Set X) (k k' : K) : Prop :=
  RevealedPrefK χ e₀ k k'

/-- The canonical relation agrees with every event-indexed `R^K` under
    constant-act menu invariance (and α). -/
theorem canonicalRK_eq {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hC : HasConstantActs χ)
    (hα : AxiomAlpha χ) (hCAMI : ConstActMenuInvariant χ)
    {e₀ : Set X} (he₀ : e₀ ∈ χ.E)
    {e : Set X} (he : e ∈ χ.E) (k k' : K) :
    CanonicalRK χ e₀ k k' ↔ RevealedPrefK χ e k k' := by
  unfold CanonicalRK
  exact eventIndependentRK_of_constActMenuInvariant hM hC hα hCAMI
          e₀ e he₀ he k k'

end ConditionalChoice
