import CAJTest.Smoke
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# The two-prior witness context

The designed witness context for the M5 negatives (Phase 4), built early
(Phase 3) and reused: two states (`Bool`), three acts (`Fin 3`), the
powerset algebra, and all nonempty menus.

* act `0` — the *safe* act, utility `1` in every state;
* act `1` — bets on state `false`: utility `2` there, `0` otherwise;
* act `2` — bets on state `true`: utility `2` there, `0` otherwise;
* `prior0` puts weight `7/10` on `false` (favors the bet `1`);
* `prior1` puts weight `7/10` on `true` (favors the bet `2`).

Expected-utility table at the vacuous supposition (verified below):

| act | `prior0` | `prior1` |
|-----|----------|----------|
| `0` | `1`      | `1`      |
| `1` | `7/5`    | `3/5`    |
| `2` | `3/5`    | `7/5`    |

The canonical Levi/SSK pattern follows on the full menu: each SEU judgment
chooses its favored bet, and the E-admissibility judgment of the two-prior
credal set chooses `{1, 2}` — the safe act is *excluded* despite being
nobody's worst option.
-/

namespace CAJTest

open CAJ

/-! ## Finitely additive probability from weights on a finite type -/

/-- The `Fap` on the powerset algebra of a finite type induced by a
nonnegative weight function summing to 1. -/
noncomputable def finFap {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) :
    Fap (powersetAlgebra X) where
  p s := ∑ x ∈ s.val.toFinite.toFinset, w x
  nonneg _ := Finset.sum_nonneg fun x _ => hw x
  p_univ := by
    rw [← hsum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp
  additive s t hd := by
    classical
    have hdisj : Disjoint s.val.toFinite.toFinset t.val.toFinite.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Set.Finite.mem_toFinset] at hx hx'
      exact Set.disjoint_left.mp hd hx hx'
    rw [← Finset.sum_union hdisj]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp

/-- Compute a `finFap` against any concrete `Finset` enumerating the
member set. -/
theorem finFap_p {X : Type*} [Fintype X] (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) (s : {s : Set X // s ∈ powersetAlgebra X})
    (t : Finset X) (h : s.val = ↑t) :
    (finFap w hw hsum).p s = ∑ x ∈ t, w x := by
  unfold finFap
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  rw [Set.Finite.mem_toFinset, h, Finset.mem_coe]

/-! ## The context -/

/-- The two-prior witness context: states `Bool`, acts `Fin 3`, powerset
algebra, and every nonempty menu available. -/
@[reducible]
def twoPriorCtx : DecisionContext where
  State := Bool
  Act := Fin 3
  alg := powersetAlgebra Bool
  Menus := {m | m.Nonempty}
  menus_nonempty _ h := h
  menus_inhabited := ⟨Set.univ, ⟨0, Set.mem_univ 0⟩⟩

/-- State-dependent payoffs: act `0` is safe; act `1` bets on `false`;
act `2` bets on `true`. -/
noncomputable def payoff (a : Fin 3) (b : Bool) : ℝ :=
  if a = 0 then 1
  else if a = 1 then (if b then 0 else 2)
  else (if b then 2 else 0)

@[simp] theorem payoff_zero (b : Bool) : payoff 0 b = 1 := rfl
@[simp] theorem payoff_one (b : Bool) : payoff 1 b = if b then 0 else 2 := rfl
@[simp] theorem payoff_two (b : Bool) : payoff 2 b = if b then 2 else 0 := rfl

/-- The credal evaluation data on the witness context. -/
noncomputable def twoPriorCC : CredalContext twoPriorCtx where
  U := payoff
  finite_range a e := e.val.toFinite.image (payoff a)
  level_mem _ _ _ := trivial
  menus_finite m := m.val.toFinite

@[simp] theorem twoPriorCC_U : twoPriorCC.U = payoff := rfl

@[simp] theorem topEvent_val : twoPriorCtx.topEvent.val = Set.univ := rfl

/-- The full menu `{0, 1, 2}`. -/
def fullMenu : twoPriorCtx.Menu := ⟨Set.univ, ⟨0, Set.mem_univ 0⟩⟩

@[simp] theorem fullMenu_val : fullMenu.val = Set.univ := rfl

/-! ## The two priors -/

/-- Weights favoring state `false`. -/
noncomputable def w0 : Bool → ℝ := fun b => if b then 3 / 10 else 7 / 10

/-- Weights favoring state `true`. -/
noncomputable def w1 : Bool → ℝ := fun b => if b then 7 / 10 else 3 / 10

theorem w0_nonneg : ∀ b, 0 ≤ w0 b := by intro b; cases b <;> norm_num [w0]
theorem w1_nonneg : ∀ b, 0 ≤ w1 b := by intro b; cases b <;> norm_num [w1]

theorem w0_sum : ∑ b, w0 b = 1 := by rw [Fintype.sum_bool]; norm_num [w0]
theorem w1_sum : ∑ b, w1 b = 1 := by rw [Fintype.sum_bool]; norm_num [w1]

/-- The prior favoring state `false` (weight `7/10`). -/
noncomputable def prior0 : Fap twoPriorCtx.alg := finFap w0 w0_nonneg w0_sum

/-- The prior favoring state `true` (weight `7/10`). -/
noncomputable def prior1 : Fap twoPriorCtx.alg := finFap w1 w1_nonneg w1_sum

/-! ## Utility ranges and level sets -/

theorem image_payoff_zero : payoff 0 '' Set.univ = ↑({1} : Finset ℝ) := by
  ext r
  simp

theorem image_payoff_one : payoff 1 '' Set.univ = ↑({0, 2} : Finset ℝ) := by
  ext r
  simp only [Set.image_univ, Set.mem_range, payoff_one, Finset.coe_insert,
    Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    Bool.exists_bool, Bool.false_eq_true, if_false, if_true]
  constructor
  · rintro (rfl | rfl)
    · right; rfl
    · left; rfl
  · rintro (rfl | rfl)
    · right; rfl
    · left; rfl

theorem image_payoff_two : payoff 2 '' Set.univ = ↑({0, 2} : Finset ℝ) := by
  ext r
  simp only [Set.image_univ, Set.mem_range, payoff_two, Finset.coe_insert,
    Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    Bool.exists_bool, Bool.false_eq_true, if_false, if_true]
  constructor
  · rintro (rfl | rfl)
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · left; rfl
    · right; rfl

theorem level_payoff_zero :
    twoPriorCC.U 0 ⁻¹' {1} ∩ twoPriorCtx.topEvent.val =
      ↑(Finset.univ : Finset Bool) := by
  ext b
  simp

theorem level_payoff_one :
    twoPriorCC.U 1 ⁻¹' {2} ∩ twoPriorCtx.topEvent.val =
      ↑({false} : Finset Bool) := by
  ext b
  cases b <;> norm_num
  all_goals decide

theorem level_payoff_two :
    twoPriorCC.U 2 ⁻¹' {2} ∩ twoPriorCtx.topEvent.val =
      ↑({true} : Finset Bool) := by
  ext b
  cases b <;> norm_num
  all_goals decide

/-! ## The expected-utility table -/

theorem wEU_prior0_act0 :
    twoPriorCC.wEU prior0 twoPriorCtx.topEvent 0 = 1 := by
  rw [twoPriorCC.wEU_eq_sum ({1} : Finset ℝ)
      (by rw [twoPriorCC_U, topEvent_val]; exact image_payoff_zero),
    Finset.sum_singleton]
  simp only [prior0]
  rw [finFap_p w0 w0_nonneg w0_sum _ Finset.univ level_payoff_zero,
    Fintype.sum_bool]
  norm_num [w0]

theorem wEU_prior0_act1 :
    twoPriorCC.wEU prior0 twoPriorCtx.topEvent 1 = 7 / 5 := by
  rw [twoPriorCC.wEU_eq_sum ({0, 2} : Finset ℝ)
      (by rw [twoPriorCC_U, topEvent_val]; exact image_payoff_one),
    Finset.sum_insert (by norm_num), Finset.sum_singleton, zero_mul, zero_add]
  simp only [prior0]
  rw [finFap_p w0 w0_nonneg w0_sum _ ({false} : Finset Bool) level_payoff_one,
    Finset.sum_singleton]
  norm_num [w0]

theorem wEU_prior0_act2 :
    twoPriorCC.wEU prior0 twoPriorCtx.topEvent 2 = 3 / 5 := by
  rw [twoPriorCC.wEU_eq_sum ({0, 2} : Finset ℝ)
      (by rw [twoPriorCC_U, topEvent_val]; exact image_payoff_two),
    Finset.sum_insert (by norm_num), Finset.sum_singleton, zero_mul, zero_add]
  simp only [prior0]
  rw [finFap_p w0 w0_nonneg w0_sum _ ({true} : Finset Bool) level_payoff_two,
    Finset.sum_singleton]
  norm_num [w0]

theorem wEU_prior1_act0 :
    twoPriorCC.wEU prior1 twoPriorCtx.topEvent 0 = 1 := by
  rw [twoPriorCC.wEU_eq_sum ({1} : Finset ℝ)
      (by rw [twoPriorCC_U, topEvent_val]; exact image_payoff_zero),
    Finset.sum_singleton]
  simp only [prior1]
  rw [finFap_p w1 w1_nonneg w1_sum _ Finset.univ level_payoff_zero,
    Fintype.sum_bool]
  norm_num [w1]

theorem wEU_prior1_act1 :
    twoPriorCC.wEU prior1 twoPriorCtx.topEvent 1 = 3 / 5 := by
  rw [twoPriorCC.wEU_eq_sum ({0, 2} : Finset ℝ)
      (by rw [twoPriorCC_U, topEvent_val]; exact image_payoff_one),
    Finset.sum_insert (by norm_num), Finset.sum_singleton, zero_mul, zero_add]
  simp only [prior1]
  rw [finFap_p w1 w1_nonneg w1_sum _ ({false} : Finset Bool) level_payoff_one,
    Finset.sum_singleton]
  norm_num [w1]

theorem wEU_prior1_act2 :
    twoPriorCC.wEU prior1 twoPriorCtx.topEvent 2 = 7 / 5 := by
  rw [twoPriorCC.wEU_eq_sum ({0, 2} : Finset ℝ)
      (by rw [twoPriorCC_U, topEvent_val]; exact image_payoff_two),
    Finset.sum_insert (by norm_num), Finset.sum_singleton, zero_mul, zero_add]
  simp only [prior1]
  rw [finFap_p w1 w1_nonneg w1_sum _ ({true} : Finset Bool) level_payoff_two,
    Finset.sum_singleton]
  norm_num [w1]

/-! ## Choice sets on the full menu -/

theorem fin3_eq (b : twoPriorCtx.Act) : b = 0 ∨ b = 1 ∨ b = 2 := by
  revert b; decide

/-- Under `prior0`, the unique SEU-admissible act from the full menu is
the bet on `false`. -/
theorem seu_prior0_full :
    (twoPriorCC.seu prior0).C twoPriorCtx.topEvent fullMenu = {1} := by
  ext a
  rw [CredalContext.mem_seu_C]
  constructor
  · rintro ⟨-, -, h⟩
    rcases fin3_eq a with rfl | rfl | rfl
    · have := h 1 (Set.mem_univ 1)
      rw [wEU_prior0_act1, wEU_prior0_act0] at this
      norm_num at this
    · rfl
    · have := h 1 (Set.mem_univ 1)
      rw [wEU_prior0_act1, wEU_prior0_act2] at this
      norm_num at this
  · rintro rfl
    refine ⟨Set.mem_univ 1, by rw [Fap.p_topEvent]; exact one_ne_zero, ?_⟩
    intro b _
    rw [wEU_prior0_act1]
    rcases fin3_eq b with rfl | rfl | rfl
    · rw [wEU_prior0_act0]; norm_num
    · rw [wEU_prior0_act1]
    · rw [wEU_prior0_act2]; norm_num

/-- Under `prior1`, the unique SEU-admissible act from the full menu is
the bet on `true`. -/
theorem seu_prior1_full :
    (twoPriorCC.seu prior1).C twoPriorCtx.topEvent fullMenu = {2} := by
  ext a
  rw [CredalContext.mem_seu_C]
  constructor
  · rintro ⟨-, -, h⟩
    rcases fin3_eq a with rfl | rfl | rfl
    · have := h 2 (Set.mem_univ 2)
      rw [wEU_prior1_act2, wEU_prior1_act0] at this
      norm_num at this
    · have := h 2 (Set.mem_univ 2)
      rw [wEU_prior1_act2, wEU_prior1_act1] at this
      norm_num at this
    · rfl
  · rintro rfl
    refine ⟨Set.mem_univ 2, by rw [Fap.p_topEvent]; exact one_ne_zero, ?_⟩
    intro b _
    rw [wEU_prior1_act2]
    rcases fin3_eq b with rfl | rfl | rfl
    · rw [wEU_prior1_act0]; norm_num
    · rw [wEU_prior1_act1]; norm_num
    · rw [wEU_prior1_act2]

/-- The two-prior credal set. -/
noncomputable def credalPair : Set (Fap twoPriorCtx.alg) := {prior0, prior1}

theorem credalPair_nonempty : credalPair.Nonempty :=
  ⟨prior0, Set.mem_insert _ _⟩

/-- The Levi/SSK pattern: E-admissibility under the two-prior credal set
chooses exactly the two bets from the full menu — the safe act is
excluded. -/
theorem eAdm_pair_full :
    (twoPriorCC.eAdm credalPair credalPair_nonempty).C twoPriorCtx.topEvent
      fullMenu = {1, 2} := by
  rw [CredalContext.eAdm_C]
  simp only [credalPair]
  rw [Set.biUnion_pair, seu_prior0_full, seu_prior1_full, Set.singleton_union]

/-- The safe act is E-inadmissible from the full menu. -/
theorem safe_excluded :
    (0 : twoPriorCtx.Act) ∉ (twoPriorCC.eAdm credalPair credalPair_nonempty).C
      twoPriorCtx.topEvent fullMenu := by
  rw [eAdm_pair_full]
  rintro (h | h)
  · exact absurd h (by decide : ¬((0 : twoPriorCtx.Act) = 1))
  · exact absurd h (by decide : ¬((0 : twoPriorCtx.Act) = 2))

/-! ## Sanity checks: monotonicity, liveness, mixtures -/

/-- Monotonicity of E-admissibility in the credal set. -/
example :
    twoPriorCC.eAdm {prior0} (Set.singleton_nonempty _) ≤
      twoPriorCC.eAdm credalPair credalPair_nonempty :=
  twoPriorCC.eAdm_mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

/-- The E-admissibility judgment is live at the vacuous supposition. -/
example :
    (twoPriorCC.eAdm credalPair credalPair_nonempty).Live
      twoPriorCtx.topEvent :=
  twoPriorCC.eAdm_live_iff.mpr
    ⟨prior0, Set.mem_insert _ _, by rw [prior0.p_topEvent]; exact one_ne_zero⟩

/-- The even mixture of the two priors lies in the convex hull of the
credal pair. -/
example :
    Fap.mix (1 / 2) (by norm_num) (by norm_num) prior0 prior1 ∈
      Fap.convexHull credalPair := by
  apply Fap.mixtureClosed_convexHull
  · exact Fap.subset_convexHull _ (Set.mem_insert _ _)
  · exact Fap.subset_convexHull _ (Set.mem_insert_of_mem _ rfl)

end CAJTest
