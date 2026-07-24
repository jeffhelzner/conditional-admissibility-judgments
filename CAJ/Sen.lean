import CAJ.Judgment

/-!
# Sen postulates and WARP, per supposition

Choice-consistency postulates for an `AdmissibilityJudgment`, stated *per
supposition* (`…At e`) with event-uniform versions quantifying over all
suppositions. Formulations follow the legacy development (tag `legacy-v1`,
`src/RevealedPreference.lean`), adapted to the subtype encoding of events
and menus; membership hypotheses derivable from `choice_subset` are dropped.

The basic facts `WARP → α` and `WARP → β` are proved here as sanity checks
on the definitions. The headline result about joins — α is preserved, β/WARP
destroyed — is Phase 4 (β-corollary).
-/

namespace CAJ

namespace AdmissibilityJudgment

variable {ctx : DecisionContext} (J : AdmissibilityJudgment ctx)

/-- Sen's α (contraction consistency) at supposition `e`: an act admissible
from a menu is admissible from any submenu containing it. -/
def SenAlphaAt (e : ctx.Event) : Prop :=
  ∀ m m' : ctx.Menu, m'.val ⊆ m.val →
    ∀ a ∈ m'.val, a ∈ J.C e m → a ∈ J.C e m'

/-- Event-uniform Sen's α. -/
def SenAlpha : Prop := ∀ e, J.SenAlphaAt e

/-- Sen's β (expansion of bests) at supposition `e`: acts jointly admissible
from a submenu agree on admissibility from the larger menu. -/
def SenBetaAt (e : ctx.Event) : Prop :=
  ∀ m m' : ctx.Menu, m'.val ⊆ m.val →
    ∀ a a', a ∈ J.C e m' → a' ∈ J.C e m' →
      (a ∈ J.C e m ↔ a' ∈ J.C e m)

/-- Event-uniform Sen's β. -/
def SenBeta : Prop := ∀ e, J.SenBetaAt e

/-- Sen's γ (binary expansion consistency) at supposition `e`: an act
admissible from each of two menus is admissible from their union, whenever
the union is available as a menu. -/
def SenGammaAt (e : ctx.Event) : Prop :=
  ∀ m₁ m₂ mu : ctx.Menu, mu.val = m₁.val ∪ m₂.val →
    ∀ a, a ∈ J.C e m₁ → a ∈ J.C e m₂ → a ∈ J.C e mu

/-- Event-uniform Sen's γ. -/
def SenGamma : Prop := ∀ e, J.SenGammaAt e

/-- The Weak Axiom of Revealed Preference at supposition `e`: if `a` and `a'`
both belong to menus `m` and `m'`, `a` is admissible from `m`, and `a'` is
admissible from `m'`, then `a` is admissible from `m'`. -/
def WARPAt (e : ctx.Event) : Prop :=
  ∀ m m' : ctx.Menu, ∀ a a',
    a ∈ m.val → a ∈ m'.val → a' ∈ m.val → a' ∈ m'.val →
      a ∈ J.C e m → a' ∈ J.C e m' → a ∈ J.C e m'

/-- Event-uniform WARP. -/
def WARP : Prop := ∀ e, J.WARPAt e

/-! ## Basic implications -/

/-- WARP implies Sen's α at every supposition. Uses the live/dead dichotomy:
at a dead supposition α is vacuous; at a live one the smaller menu supplies
a witness. -/
theorem WARPAt.senAlphaAt {e : ctx.Event} (h : J.WARPAt e) :
    J.SenAlphaAt e := by
  intro m m' hsub a ham' haC
  have hlive : J.Live e := J.live_of_nonempty ⟨a, haC⟩
  obtain ⟨a', ha'⟩ := hlive m'
  exact h m m' a a' (J.choice_subset e m haC) ham'
    (hsub (J.choice_subset e m' ha')) (J.choice_subset e m' ha') haC ha'

/-- WARP implies Sen's β at every supposition. -/
theorem WARPAt.senBetaAt {e : ctx.Event} (h : J.WARPAt e) :
    J.SenBetaAt e := by
  intro m m' hsub a a' ha ha'
  have key : ∀ x y, x ∈ J.C e m' → y ∈ J.C e m' → x ∈ J.C e m → y ∈ J.C e m :=
    fun x y hx hy hxm =>
      h m' m y x (J.choice_subset e m' hy) (hsub (J.choice_subset e m' hy))
        (J.choice_subset e m' hx) (hsub (J.choice_subset e m' hx)) hy hxm
  exact ⟨key a a' ha ha', key a' a ha' ha⟩

/-- WARP implies Sen's α (uniform version). -/
theorem WARP.senAlpha (h : J.WARP) : J.SenAlpha := fun e =>
  WARPAt.senAlphaAt J (h e)

/-- WARP implies Sen's β (uniform version). -/
theorem WARP.senBeta (h : J.WARP) : J.SenBeta := fun e =>
  WARPAt.senBetaAt J (h e)

/-! ## The top judgment satisfies everything -/

theorem top_warp : (⊤ : AdmissibilityJudgment ctx).WARP := by
  intro e m m' a a' _ ham' _ _ _ _
  simpa using ham'

theorem top_senGamma : (⊤ : AdmissibilityJudgment ctx).SenGamma := by
  intro e m₁ m₂ mu hu a ha _
  simp only [top_C] at ha ⊢
  rw [hu]
  exact Or.inl ha

end AdmissibilityJudgment

end CAJ
