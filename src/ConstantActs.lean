/-
# Constant Acts and the Consequence-Level Relation

This module specializes the alternative-level revealed-preference theory of
`RevealedPreference.lean` to the consequence space `K`, by way of the
constant-act embedding `K ↪ χ.A`, `k ↦ (fun _ => k)`. The resulting
relation `RevealedPrefK χ e k k'` on consequences inherits its formal
properties from the alternative-level theorems whenever the constant acts
are themselves available as alternatives (`HasConstantActs χ`) and the
relevant closure clauses hold.

The philosophical content of this specialization: having extracted a
preference order on alternatives, we now ask what it says about
*consequences*. A consequence `k` is revealed at-least-as-good as `k'`
under supposition `e` precisely when the constant act always-`k` is
revealed at-least-as-good as the constant act always-`k'` under `e`.
This recovers the classical setting in which preferences are ultimately
preferences over consequences.

This module realizes the framework sketched in
`prompts/PROMPT_FOR_REVEALED_PREFERENCE_INVESTIGATION.md`, but as a
specialization of the alternative-level theory developed in
`src/RevealedPreference.lean` rather than an independent construction.
-/

import RevealedPreference

namespace ConditionalChoice

universe u v

/-! ## Constant acts -/

/-- The constant act on `K` taking value `k` everywhere. -/
@[simp] def constAct {X : Type u} {K : Type v} (k : K) : X → K :=
  fun _ => k

/-- A `ConditionalJudgment` *has constant acts* if every consequence is
    realized as a constant alternative. -/
def HasConstantActs {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) : Prop :=
  ∀ k : K, (constAct k : X → K) ∈ χ.A

/-- Two constant acts are equal iff their values are equal (assuming `X` is
    inhabited, which is provided by the `ConditionalJudgment` structure). -/
theorem constAct_injective {X : Type u} {K : Type v}
    [Nonempty X] : Function.Injective (constAct : K → X → K) := by
  intro k k' h
  exact congrArg (fun f => f (Classical.arbitrary X)) h

/-! ## The revealed-preference relation on consequences -/

/-- The revealed-preference relation on `K`, defined as the pullback of
    `RevealedPref` along the constant-act embedding. -/
def RevealedPrefK {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) (k k' : K) : Prop :=
  RevealedPref χ e (constAct k) (constAct k')

/-- Strict revealed preference on consequences. -/
def StrictPrefK {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) (k k' : K) : Prop :=
  RevealedPrefK χ e k k' ∧ ¬ RevealedPrefK χ e k' k

/-- Revealed indifference on consequences. -/
def IndiffK {X : Type u} {K : Type v} (χ : ConditionalJudgment X K)
    (e : Set X) (k k' : K) : Prop :=
  RevealedPrefK χ e k k' ∧ RevealedPrefK χ e k' k

/-! ## Inherited structural properties

Each property of `RevealedPref` transports to `RevealedPrefK` whenever
constant acts are present. The proofs are immediate applications of the
alternative-level theorems. -/

/-- `R_e^K` is reflexive on `K` (uses singleton closure of constant-act
    menus and `HasConstantActs`). -/
theorem revealedPrefK_refl_at {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hC : HasConstantActs χ)
    {e : Set X} (he : e ∈ χ.E) :
    ∀ k : K, RevealedPrefK χ e k k :=
  fun k => revealedPref_refl_at hM he (constAct k) (hC k)

/-- `R_e^K` is total on `K` (uses pair closure of constant-act menus and
    `HasConstantActs`). -/
theorem revealedPrefK_total_at {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hC : HasConstantActs χ)
    {e : Set X} (he : e ∈ χ.E) :
    ∀ k k' : K,
      RevealedPrefK χ e k k' ∨ RevealedPrefK χ e k' k :=
  fun k k' =>
    revealedPref_total_at hM he (constAct k) (constAct k') (hC k) (hC k')

/-- `R_e^K` is transitive on `K` under WARP and triple closure. -/
theorem revealedPrefK_trans_via_warp {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hC : HasConstantActs χ)
    {e : Set X} (he : e ∈ χ.E) (hWARP : WARPAt χ e) :
    ∀ k₁ k₂ k₃ : K,
      RevealedPrefK χ e k₁ k₂ →
      RevealedPrefK χ e k₂ k₃ →
      RevealedPrefK χ e k₁ k₃ :=
  fun k₁ k₂ k₃ =>
    revealedPref_trans_via_warp hM he hWARP
      (constAct k₁) (constAct k₂) (constAct k₃)
      (hC k₁) (hC k₂) (hC k₃)

/-- `R_e^K` is a weak ordering on `K`: reflexive, transitive, total. -/
def WeakOrderingKAt {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) (e : Set X) : Prop :=
  (∀ k : K, RevealedPrefK χ e k k) ∧
  (∀ k₁ k₂ k₃ : K,
      RevealedPrefK χ e k₁ k₂ →
      RevealedPrefK χ e k₂ k₃ →
      RevealedPrefK χ e k₁ k₃) ∧
  (∀ k k' : K,
      RevealedPrefK χ e k k' ∨ RevealedPrefK χ e k' k)

/-- Under `MenuClosure`, `HasConstantActs`, and WARP, `R_e^K` is a weak
    ordering on `K`. -/
theorem revealedPrefK_weakOrder_at {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hC : HasConstantActs χ)
    {e : Set X} (he : e ∈ χ.E) (hWARP : WARPAt χ e) :
    WeakOrderingKAt χ e :=
  ⟨ revealedPrefK_refl_at hM hC he,
    revealedPrefK_trans_via_warp hM hC he hWARP,
    revealedPrefK_total_at hM hC he ⟩

/-! ## Event independence on consequences

Event-independence has cleaner philosophical content at the consequence
level than at the alternative level: it asks whether the agent's
*intrinsic* preferences over consequences shift with the supposition,
distinguishing genuinely state-dependent from state-independent valuation. -/

/-- Event-independence of the consequence-level relation: `R_e^K` and
    `R_{e'}^K` agree on all consequences for all events `e, e' ∈ χ.E`. -/
def EventIndependentRK {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) : Prop :=
  ∀ e e', e ∈ χ.E → e' ∈ χ.E →
    ∀ k k' : K,
      (RevealedPrefK χ e k k' ↔ RevealedPrefK χ e' k k')

/-- If the underlying alternative-level relation is event-independent and
    constant acts are present, then so is the consequence-level relation. -/
theorem eventIndependentRK_of_eventIndependentR {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hC : HasConstantActs χ)
    (hEI : EventIndependentR χ) : EventIndependentRK χ := by
  intro e e' he he' k k'
  exact hEI e e' he he' (constAct k) (constAct k') (hC k) (hC k')

end ConditionalChoice
