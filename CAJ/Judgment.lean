import CAJ.DecisionContext
import Mathlib.Order.BoundedOrder.Basic

/-!
# Admissibility judgments

An `AdmissibilityJudgment` over a fixed `DecisionContext` is a conditional
choice function `C : Event → Menu → Set Act` with `C e m ⊆ m`.

## Null-supposition policy (design decision, Phase 1)

The choice set is *not* required to be nonempty at every supposition: a
supposition the judgment treats as null (e.g. `p e = 0` for an SEU judgment
with prior `p`, or `e = ∅`) yields the *empty* choice set — it must NOT
default to the full menu, which would break the join identity M1. Nullity is
uniform across menus: at each supposition a judgment is either *live*
(nonempty choice from every menu) or *dead* (empty choice from every menu).
This dichotomy is stored as a field rather than a separate domain datum, so
the pointwise order and pointwise joins (Phase 2) need no side conditions.
The unsupposed judgment (supposition `univ`) is required to be live.
-/

namespace CAJ

open DecisionContext

variable {ctx : DecisionContext}

/-- A conditional admissibility judgment over the fixed context `ctx`:
for each supposition `e` and menu `m`, the subset `C e m ⊆ m` of acts judged
admissible under `e`. At each supposition the judgment is either live
(all choice sets nonempty) or dead (all empty); it is live at `univ`. -/
structure AdmissibilityJudgment (ctx : DecisionContext) where
  /-- The conditional choice function. -/
  C : ctx.Event → ctx.Menu → Set ctx.Act
  /-- Choices come from the menu. -/
  choice_subset : ∀ e m, C e m ⊆ m.val
  /-- Null-supposition dichotomy: at each supposition, either every menu
  yields a nonempty choice set, or every menu yields the empty set. -/
  live_or_dead : ∀ e, (∀ m, (C e m).Nonempty) ∨ (∀ m, C e m = ∅)
  /-- The vacuous supposition `univ` is never null. -/
  live_univ : ∀ m, (C ctx.topEvent m).Nonempty

namespace AdmissibilityJudgment

variable (J K : AdmissibilityJudgment ctx)

/-- `J` is live at `e`: every menu yields a nonempty choice set. -/
def Live (e : ctx.Event) : Prop := ∀ m, (J.C e m).Nonempty

/-- `J` is dead at `e` (treats `e` as null): every choice set is empty. -/
def Dead (e : ctx.Event) : Prop := ∀ m, J.C e m = ∅

theorem live_topEvent : J.Live ctx.topEvent := J.live_univ

theorem not_dead_of_live {e : ctx.Event} (h : J.Live e) : ¬ J.Dead e := by
  intro hd
  obtain ⟨m⟩ := (inferInstance : Nonempty ctx.Menu)
  obtain ⟨a, ha⟩ := h m
  rw [hd m] at ha
  exact ha

/-- A single nonempty choice set witnesses liveness. -/
theorem live_of_nonempty {e : ctx.Event} {m : ctx.Menu}
    (h : (J.C e m).Nonempty) : J.Live e := by
  rcases J.live_or_dead e with hl | hd
  · exact hl
  · obtain ⟨a, ha⟩ := h
    rw [hd m] at ha
    exact absurd ha (Set.notMem_empty a)

theorem dead_of_not_live {e : ctx.Event} (h : ¬ J.Live e) : J.Dead e := by
  rcases J.live_or_dead e with hl | hd
  · exact absurd hl h
  · exact hd

theorem live_iff_not_dead {e : ctx.Event} : J.Live e ↔ ¬ J.Dead e := by
  constructor
  · exact J.not_dead_of_live
  · intro h
    rcases J.live_or_dead e with hl | hd
    · exact hl
    · exact absurd hd h

/-! ## The pointwise order -/

/-- Extensionality: judgments with the same choice function are equal. -/
@[ext]
theorem ext {J K : AdmissibilityJudgment ctx}
    (h : ∀ e m, J.C e m = K.C e m) : J = K := by
  have hC : J.C = K.C := funext fun e => funext fun m => h e m
  cases J; cases K; cases hC; rfl

/-- Judgments are ordered pointwise: `J ≤ K` iff `J.C e m ⊆ K.C e m` for all
`e`, `m`. Descent along `≤` is contraction (`𝓛`), ascent is expansion (`𝓡`). -/
instance : PartialOrder (AdmissibilityJudgment ctx) where
  le J K := ∀ e m, J.C e m ⊆ K.C e m
  le_refl _ _ _ := subset_rfl
  le_trans _ _ _ h h' e m := (h e m).trans (h' e m)
  le_antisymm _ _ h h' := ext fun e m => (h e m).antisymm (h' e m)

theorem le_def {J K : AdmissibilityJudgment ctx} :
    J ≤ K ↔ ∀ e m, J.C e m ⊆ K.C e m :=
  Iff.rfl

/-- Liveness is monotone along the pointwise order. -/
theorem Live.mono {J K : AdmissibilityJudgment ctx} (h : J ≤ K)
    {e : ctx.Event} (hl : J.Live e) : K.Live e := fun m =>
  let ⟨a, ha⟩ := hl m
  ⟨a, h e m ha⟩

/-- Deadness is antitone along the pointwise order. -/
theorem Dead.anti {J K : AdmissibilityJudgment ctx} (h : J ≤ K)
    {e : ctx.Event} (hd : K.Dead e) : J.Dead e := fun m =>
  Set.eq_empty_of_subset_empty (hd m ▸ h e m)

/-! ## The top judgment -/

/-- The judgment that deems every act in every menu admissible under every
supposition. This is the greatest element of the pointwise order. -/
def top (ctx : DecisionContext) : AdmissibilityJudgment ctx where
  C _ m := m.val
  choice_subset _ _ := subset_rfl
  live_or_dead _ := Or.inl fun m => ctx.menu_nonempty m
  live_univ m := ctx.menu_nonempty m

instance : OrderTop (AdmissibilityJudgment ctx) where
  top := top ctx
  le_top J e m := J.choice_subset e m

@[simp]
theorem top_C (e : ctx.Event) (m : ctx.Menu) :
    (⊤ : AdmissibilityJudgment ctx).C e m = m.val :=
  rfl

end AdmissibilityJudgment

end CAJ
