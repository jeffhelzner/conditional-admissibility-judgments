/-
# Expected Utility implies Revealed Preference

This module proves the bridging theorem connecting the project's two main
strands: every `ConditionalJudgment` with an expected-utility representation
satisfies the Weak Axiom of Revealed Preference (and hence is `Representable`
in the sense of `RevealedPreference.lean`) on every non-null event.

Conceptually: an EU-maximizing agent is automatically revealed-preference
rational. The agent's preferences over alternatives are governed by the
real-valued ordering induced by expected utility, and that ordering is a
weak order on `χ.A`; the choice function selects exactly the EU-maxima of
each menu, which is precisely what `Representable` demands.

## Technical preliminaries

`HasEURepresentation` parameterizes EU equivalences over non-null events
`e ∈ χ.E.carrier` with `p e ≠ 0`, and the EU computation requires
per-act witnesses of finite range (`hfin`) and level-set membership
(`hlev`). To apply the representation theorem we therefore introduce
a regularity predicate `EUWellFormed χ` asserting that every act in
`χ.A` has finite range on every event and that all its level sets lie
in `χ.E`. This is the standard "well-behaved" condition under which
the finite-support EU machinery applies uniformly.

WARP is then provable on every non-null event. On *null* events the EU
representation provides no constraint on `χ.C`, and accordingly the
bridging theorem is silent there — a finding consistent with the
classical theory: null events are exactly those on which EU-maximization
imposes no rationality constraint.
-/

import RevealedPreference
import ConstantActs

namespace ConditionalChoice

universe u v

/-! ## Regularity of acts for EU computation -/

/-- Every act in `χ.A` has finite range on every event in `χ.E` and all its
    level sets lie in `χ.E`. This is the structural assumption under which
    the finite-support EU machinery applies uniformly to every act. -/
def EUWellFormed {X : Type u} {K : Type v}
    (χ : ConditionalJudgment X K) : Prop :=
  ∀ a ∈ χ.A, ∀ (e : { s // s ∈ χ.E.carrier }),
    (a '' e.val).Finite ∧ ∀ k, a ⁻¹' {k} ∩ e.val ∈ χ.E.carrier

/-- The finite-range component of `EUWellFormed` for a specific act and event. -/
theorem EUWellFormed.finite {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hWF : EUWellFormed χ)
    {a : X → K} (ha : a ∈ χ.A) (e : { s // s ∈ χ.E.carrier }) :
    (a '' e.val).Finite :=
  (hWF a ha e).1

/-- The level-sets-in-algebra component of `EUWellFormed` for a specific act
    and event. -/
theorem EUWellFormed.levelSets {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K} (hWF : EUWellFormed χ)
    {a : X → K} (ha : a ∈ χ.A) (e : { s // s ∈ χ.E.carrier }) :
    ∀ k, a ⁻¹' {k} ∩ e.val ∈ χ.E.carrier :=
  (hWF a ha e).2

/-! ## EU representation implies WARP -/

/-- **Bridging theorem (witness version).** If `χ` is EU-well-formed and
    `χ.C` agrees with EU-maximization (with respect to a specific
    probability `p` and utility `u`) on a non-null event `e`, and if `χ.M`
    has the menu-closure structure required for revealed-preference
    theorems, then WARP holds on `e`.

    The witness version operates on explicit `p, u`; the existential
    corollary `warpAt_of_hasEURepresentation` follows. -/
theorem warpAt_of_eu_witnesses {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hWF : EUWellFormed χ)
    (p : Fap χ.E) (u : K → ℝ)
    (hRep :
      ∀ (e : { s // s ∈ χ.E.carrier }),
        (he : p.p e ≠ 0) →
        ∀ m ∈ χ.M,
          ∀ a ∈ m,
            (hfin : (a '' e.val).Finite) →
            (ha : ∀ k, a ⁻¹' {k} ∩ e.val ∈ χ.E.carrier) →
            (a ∈ χ.C e.val m ↔
              ∀ a' ∈ m,
                (hfin' : (a' '' e.val).Finite) →
                (ha' : ∀ k, a' ⁻¹' {k} ∩ e.val ∈ χ.E.carrier) →
                expected_utility p u e he a' hfin' ha' ≤
                  expected_utility p u e he a hfin ha))
    (e : { s // s ∈ χ.E.carrier }) (hpe : p.p e ≠ 0) :
    WARPAt χ e.val := by
  intro m m' hm hm' a a' ha_m ha_m' ha'_m ha'_m' ha_C ha'_C'
  -- a, a' lie in χ.A via MenuClosure.menu_subset_alt.
  have ha_A  : a  ∈ χ.A := hM.menu_subset_alt m hm ha_m
  have ha'_A : a' ∈ χ.A := hM.menu_subset_alt m hm ha'_m
  -- Their finite-support and level-set witnesses.
  have hfa  : (a  '' e.val).Finite := hWF.finite ha_A  e
  have hla  : ∀ k, a  ⁻¹' {k} ∩ e.val ∈ χ.E.carrier := hWF.levelSets ha_A  e
  have hfa' : (a' '' e.val).Finite := hWF.finite ha'_A e
  have hla' : ∀ k, a' ⁻¹' {k} ∩ e.val ∈ χ.E.carrier := hWF.levelSets ha'_A e
  -- Unpack the EU representation at (m, a) and (m', a').
  have hRep_m  := (hRep e hpe m  hm  a  ha_m  hfa hla).mp ha_C
  have hRep_m' := (hRep e hpe m' hm' a' ha'_m' hfa' hla').mp ha'_C'
  -- EU(a') ≤ EU(a) and EU(a) ≤ EU(a'), hence equal.
  have h1 : expected_utility p u e hpe a' hfa' hla'
              ≤ expected_utility p u e hpe a  hfa  hla :=
    hRep_m  a' ha'_m  hfa' hla'
  have h2 : expected_utility p u e hpe a  hfa  hla
              ≤ expected_utility p u e hpe a' hfa' hla' :=
    hRep_m' a  ha_m'  hfa  hla
  -- Conclude a ∈ C e.val m' via the EU representation at (m', a).
  refine (hRep e hpe m' hm' a ha_m' hfa hla).mpr ?_
  intro b hb hfb hlb
  -- For each b ∈ m', EU(b) ≤ EU(a') ≤ EU(a) (using h2 reversed: EU a ≤ EU a',
  -- so we want EU b ≤ EU a; route via EU(a') first.)
  -- Actually we need EU b ≤ EU a. We have EU b ≤ EU a' (from hRep_m')
  -- and EU a' ≤ EU a (from h1). Chain.
  have hb_le_a' : expected_utility p u e hpe b hfb hlb
                    ≤ expected_utility p u e hpe a' hfa' hla' :=
    hRep_m' b hb hfb hlb
  exact le_trans hb_le_a' h1

/-- **Bridging theorem (existential corollary).** Under `MenuClosure` and
    `EUWellFormed`, if `χ` admits an EU representation and `e` is a
    non-null event for the (existentially quantified) probability, then
    WARP holds on `e`.

    Because `HasEURepresentation` is existential in `(p, u)`, the
    non-null hypothesis must refer to *some* witnessing probability;
    we therefore phrase the conclusion as a Skolem-style implication on
    the witnesses. -/
theorem warpAt_of_hasEURepresentation {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hWF : EUWellFormed χ)
    (hEU : HasEURepresentation χ) :
    ∃ (p : Fap χ.E) (_u : K → ℝ),
      ∀ (e : { s // s ∈ χ.E.carrier }), p.p e ≠ 0 → WARPAt χ e.val := by
  obtain ⟨p, u, hRep⟩ := hEU
  exact ⟨p, u, fun e hpe => warpAt_of_eu_witnesses hM hWF p u hRep e hpe⟩

/-- **Representability follows from EU representation.** Under `MenuClosure`
    and `EUWellFormed`, an EU representation entails that `χ.C` is
    `Representable` (in the sense of `RevealedPreference.lean`) on every
    non-null event of the witnessing probability. -/
theorem representable_of_hasEURepresentation {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hWF : EUWellFormed χ)
    (hEU : HasEURepresentation χ) :
    ∃ (p : Fap χ.E) (_u : K → ℝ),
      ∀ (e : { s // s ∈ χ.E.carrier }), p.p e ≠ 0 →
        e.val ∈ χ.E → Representable χ e.val := by
  obtain ⟨p, u, hWARP⟩ := warpAt_of_hasEURepresentation hM hWF hEU
  exact ⟨p, u, fun e hpe he => representable_of_warp hM he (hWARP e hpe)⟩

/-- **Weak ordering of `R_e` follows from EU representation.** Under
    `MenuClosure` and `EUWellFormed`, EU-representability yields that the
    revealed-preference relation `R_e` is a weak order on `χ.A` for every
    non-null event. -/
theorem weakOrderingAt_of_hasEURepresentation {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hWF : EUWellFormed χ)
    (hEU : HasEURepresentation χ) :
    ∃ (p : Fap χ.E) (_u : K → ℝ),
      ∀ (e : { s // s ∈ χ.E.carrier }), p.p e ≠ 0 →
        e.val ∈ χ.E → WeakOrderingAt χ e.val := by
  obtain ⟨p, u, hWARP⟩ := warpAt_of_hasEURepresentation hM hWF hEU
  exact ⟨p, u, fun e hpe he =>
    revealedPref_weakOrder_at hM he (hWARP e hpe)⟩

/-- **Consequence-level weak ordering follows from EU representation.**
    Combining the bridging theorem with the constant-acts module:
    EU-representability yields that `R_e^K` is a weak order on `K` for
    every non-null event. -/
theorem weakOrderingKAt_of_hasEURepresentation {X : Type u} {K : Type v}
    {χ : ConditionalJudgment X K}
    (hM : MenuClosure χ) (hC : HasConstantActs χ) (hWF : EUWellFormed χ)
    (hEU : HasEURepresentation χ) :
    ∃ (p : Fap χ.E) (_u : K → ℝ),
      ∀ (e : { s // s ∈ χ.E.carrier }), p.p e ≠ 0 →
        e.val ∈ χ.E → WeakOrderingKAt χ e.val := by
  obtain ⟨p, u, hWARP⟩ := warpAt_of_hasEURepresentation hM hWF hEU
  exact ⟨p, u, fun e hpe he =>
    revealedPrefK_weakOrder_at hM hC he (hWARP e hpe)⟩

end ConditionalChoice
