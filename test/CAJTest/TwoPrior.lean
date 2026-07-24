import CAJTest.Smoke
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# The two-prior witness context

The designed witness context for the M5 negatives: two states (`Bool`),
three acts (`Fin 3`), the powerset algebra, and all nonempty menus.

* act `0` — the *safe* act, utility `6/5` in every state;
* act `1` — bets on state `false`: utility `2` there, `0` otherwise;
* act `2` — bets on state `true`: utility `2` there, `0` otherwise;
* `prior0` puts weight `7/10` on `false` (favors the bet `1`);
* `prior1` puts weight `7/10` on `true` (favors the bet `2`).

The safe payoff `6/5` is chosen strictly inside `(1, 7/5)`: above the
bets' expected utility `1` under the uniform prior (so the safe act is
uniquely optimal there — the convexity wedge M5(b) needs this), and below
the favored bet's `7/5` under each extreme prior (so each extreme prior
rejects it). With safe payoff `1` the uniform prior would *tie* all three
acts and an SEU judgment would suspend the issue, killing M5(a).

Expected-utility table at the vacuous supposition (verified below):

| act | `prior0` | `prior1` |
|-----|----------|----------|
| `0` | `6/5`    | `6/5`    |
| `1` | `7/5`    | `3/5`    |
| `2` | `3/5`    | `7/5`    |

Contents:

* the Levi/SSK pattern on the full menu: each SEU judgment chooses its
  favored bet, E-admissibility chooses `{1, 2}` — the safe act is
  excluded despite being nobody's worst option;
* **M5(a)**: no SEU judgment gives the two extreme SEU judgments even a
  fair hearing (`no_seu_fairHearing`), so the change between them is not
  commensurable within the SEU class (`not_commensurable_KSEU`) — but it
  *is* within the E-admissibility class (`commensurable_KEadm`): Levi's
  argument in miniature;
* **M5(b)**: the credal pair is not choice-equivalent to its convex hull
  (`not_convexEquivalent`) — the convexity wedge;
* **M5(c)**: the pair's E-admissibility judgment satisfies α but violates
  Sen's β, hence WARP (`eAdm_pair_not_senBetaAt`) — the β-corollary
  instantiated;
* a commutation sanity check for suppositional conditioning.
-/

namespace CAJTest

open CAJ
open AdmissibilityJudgment

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
  if a = 0 then 6 / 5
  else if a = 1 then (if b then 0 else 2)
  else (if b then 2 else 0)

@[simp] theorem payoff_zero (b : Bool) : payoff 0 b = 6 / 5 := rfl
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

/-- The submenu `{safe, bet-on-false}`. -/
def menu01 : twoPriorCtx.Menu := ⟨{0, 1}, ⟨0, Set.mem_insert 0 {1}⟩⟩

@[simp] theorem menu01_val : menu01.val = {0, 1} := rfl

/-- The submenu `{safe, bet-on-true}`. -/
def menu02 : twoPriorCtx.Menu := ⟨{0, 2}, ⟨0, Set.mem_insert 0 {2}⟩⟩

@[simp] theorem menu02_val : menu02.val = {0, 2} := rfl

/-- The event “the state is `false`”. -/
def eFalse : twoPriorCtx.Event := ⟨{false}, trivial⟩

@[simp] theorem eFalse_val : eFalse.val = {false} := rfl

/-- The event “the state is `true`”. -/
def eTrue : twoPriorCtx.Event := ⟨{true}, trivial⟩

@[simp] theorem eTrue_val : eTrue.val = {true} := rfl

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

theorem image_payoff_zero :
    payoff 0 '' Set.univ = ↑({6 / 5} : Finset ℝ) := by
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
    twoPriorCC.U 0 ⁻¹' {6 / 5} ∩ twoPriorCtx.topEvent.val = Set.univ := by
  ext b
  simp

theorem level_payoff_one :
    twoPriorCC.U 1 ⁻¹' {2} ∩ twoPriorCtx.topEvent.val =
      ({false} : Set Bool) := by
  ext b
  cases b <;> norm_num
  all_goals decide

theorem level_payoff_two :
    twoPriorCC.U 2 ⁻¹' {2} ∩ twoPriorCtx.topEvent.val =
      ({true} : Set Bool) := by
  ext b
  cases b <;> norm_num
  all_goals decide

/-! ## The expected-utility table -/

/-- Expected utility of the safe act under *any* prior. -/
theorem wEU_top_act0 (q : Fap twoPriorCtx.alg) :
    twoPriorCC.wEU q twoPriorCtx.topEvent 0 = 6 / 5 := by
  rw [twoPriorCC.wEU_eq_sum ({6 / 5} : Finset ℝ)
      (by rw [twoPriorCC_U, topEvent_val]; exact image_payoff_zero),
    Finset.sum_singleton,
    q.p_congr (t := twoPriorCtx.topEvent) level_payoff_zero,
    q.p_topEvent, mul_one]

/-- Expected utility of the bet on `false` under *any* prior. -/
theorem wEU_top_act1 (q : Fap twoPriorCtx.alg) :
    twoPriorCC.wEU q twoPriorCtx.topEvent 1 = 2 * q.p eFalse := by
  rw [twoPriorCC.wEU_eq_sum ({0, 2} : Finset ℝ)
      (by rw [twoPriorCC_U, topEvent_val]; exact image_payoff_one),
    Finset.sum_insert (by norm_num), Finset.sum_singleton, zero_mul,
    zero_add, q.p_congr (t := eFalse) level_payoff_one]

/-- Expected utility of the bet on `true` under *any* prior. -/
theorem wEU_top_act2 (q : Fap twoPriorCtx.alg) :
    twoPriorCC.wEU q twoPriorCtx.topEvent 2 = 2 * q.p eTrue := by
  rw [twoPriorCC.wEU_eq_sum ({0, 2} : Finset ℝ)
      (by rw [twoPriorCC_U, topEvent_val]; exact image_payoff_two),
    Finset.sum_insert (by norm_num), Finset.sum_singleton, zero_mul,
    zero_add, q.p_congr (t := eTrue) level_payoff_two]

/-- Any prior splits its mass between the two atoms. -/
theorem q_split (q : Fap twoPriorCtx.alg) : q.p eFalse + q.p eTrue = 1 := by
  have hd : Disjoint eFalse.val eTrue.val :=
    Set.disjoint_singleton_left.mpr (by simp)
  have huniv : eFalse.val ∪ eTrue.val = twoPriorCtx.topEvent.val := by
    ext b
    cases b <;> simp
  rw [← q.additive eFalse eTrue hd,
    q.p_congr (t := twoPriorCtx.topEvent) huniv, q.p_topEvent]

theorem prior0_eFalse : prior0.p eFalse = 7 / 10 := by
  simp only [prior0]
  rw [finFap_p w0 w0_nonneg w0_sum _ ({false} : Finset Bool)
      (Finset.coe_singleton false).symm,
    Finset.sum_singleton]
  norm_num [w0]

theorem prior0_eTrue : prior0.p eTrue = 3 / 10 := by
  simp only [prior0]
  rw [finFap_p w0 w0_nonneg w0_sum _ ({true} : Finset Bool)
      (Finset.coe_singleton true).symm,
    Finset.sum_singleton]
  norm_num [w0]

theorem prior1_eFalse : prior1.p eFalse = 3 / 10 := by
  simp only [prior1]
  rw [finFap_p w1 w1_nonneg w1_sum _ ({false} : Finset Bool)
      (Finset.coe_singleton false).symm,
    Finset.sum_singleton]
  norm_num [w1]

theorem prior1_eTrue : prior1.p eTrue = 7 / 10 := by
  simp only [prior1]
  rw [finFap_p w1 w1_nonneg w1_sum _ ({true} : Finset Bool)
      (Finset.coe_singleton true).symm,
    Finset.sum_singleton]
  norm_num [w1]

theorem wEU_prior0_act0 :
    twoPriorCC.wEU prior0 twoPriorCtx.topEvent 0 = 6 / 5 :=
  wEU_top_act0 prior0

theorem wEU_prior0_act1 :
    twoPriorCC.wEU prior0 twoPriorCtx.topEvent 1 = 7 / 5 := by
  rw [wEU_top_act1, prior0_eFalse]
  norm_num

theorem wEU_prior0_act2 :
    twoPriorCC.wEU prior0 twoPriorCtx.topEvent 2 = 3 / 5 := by
  rw [wEU_top_act2, prior0_eTrue]
  norm_num

theorem wEU_prior1_act0 :
    twoPriorCC.wEU prior1 twoPriorCtx.topEvent 0 = 6 / 5 :=
  wEU_top_act0 prior1

theorem wEU_prior1_act1 :
    twoPriorCC.wEU prior1 twoPriorCtx.topEvent 1 = 3 / 5 := by
  rw [wEU_top_act1, prior1_eFalse]
  norm_num

theorem wEU_prior1_act2 :
    twoPriorCC.wEU prior1 twoPriorCtx.topEvent 2 = 7 / 5 := by
  rw [wEU_top_act2, prior1_eTrue]
  norm_num

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

/-! ## Choice sets on the submenus -/

/-- Under `prior0`, the bet on `false` beats the safe act. -/
theorem seu_prior0_menu01 :
    (twoPriorCC.seu prior0).C twoPriorCtx.topEvent menu01 = {1} := by
  ext a
  rw [CredalContext.mem_seu_C]
  constructor
  · rintro ⟨ham, -, h⟩
    simp only [menu01_val, Set.mem_insert_iff, Set.mem_singleton_iff] at ham
    rcases ham with rfl | rfl
    · have := h 1 (Set.mem_insert_of_mem 0 rfl)
      rw [wEU_prior0_act1, wEU_prior0_act0] at this
      norm_num at this
    · rfl
  · rintro rfl
    refine ⟨Set.mem_insert_of_mem 0 rfl,
      by rw [Fap.p_topEvent]; exact one_ne_zero, ?_⟩
    intro b hb
    simp only [menu01_val, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · rw [wEU_prior0_act0, wEU_prior0_act1]
      norm_num
    · exact le_refl _

/-- Under `prior1`, the safe act beats the bet on `false`. -/
theorem seu_prior1_menu01 :
    (twoPriorCC.seu prior1).C twoPriorCtx.topEvent menu01 = {0} := by
  ext a
  rw [CredalContext.mem_seu_C]
  constructor
  · rintro ⟨ham, -, h⟩
    simp only [menu01_val, Set.mem_insert_iff, Set.mem_singleton_iff] at ham
    rcases ham with rfl | rfl
    · rfl
    · have := h 0 (Set.mem_insert 0 {1})
      rw [wEU_prior1_act0, wEU_prior1_act1] at this
      norm_num at this
  · rintro rfl
    refine ⟨Set.mem_insert 0 {1},
      by rw [Fap.p_topEvent]; exact one_ne_zero, ?_⟩
    intro b hb
    simp only [menu01_val, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact le_refl _
    · rw [wEU_prior1_act1, wEU_prior1_act0]
      norm_num

/-- Under `prior0`, the safe act beats the bet on `true`. -/
theorem seu_prior0_menu02 :
    (twoPriorCC.seu prior0).C twoPriorCtx.topEvent menu02 = {0} := by
  ext a
  rw [CredalContext.mem_seu_C]
  constructor
  · rintro ⟨ham, -, h⟩
    simp only [menu02_val, Set.mem_insert_iff, Set.mem_singleton_iff] at ham
    rcases ham with rfl | rfl
    · rfl
    · have := h 0 (Set.mem_insert 0 {2})
      rw [wEU_prior0_act0, wEU_prior0_act2] at this
      norm_num at this
  · rintro rfl
    refine ⟨Set.mem_insert 0 {2},
      by rw [Fap.p_topEvent]; exact one_ne_zero, ?_⟩
    intro b hb
    simp only [menu02_val, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact le_refl _
    · rw [wEU_prior0_act2, wEU_prior0_act0]
      norm_num

/-- Under `prior1`, the bet on `true` beats the safe act. -/
theorem seu_prior1_menu02 :
    (twoPriorCC.seu prior1).C twoPriorCtx.topEvent menu02 = {2} := by
  ext a
  rw [CredalContext.mem_seu_C]
  constructor
  · rintro ⟨ham, -, h⟩
    simp only [menu02_val, Set.mem_insert_iff, Set.mem_singleton_iff] at ham
    rcases ham with rfl | rfl
    · have := h 2 (Set.mem_insert_of_mem 0 rfl)
      rw [wEU_prior1_act2, wEU_prior1_act0] at this
      norm_num at this
    · rfl
  · rintro rfl
    refine ⟨Set.mem_insert_of_mem 0 rfl,
      by rw [Fap.p_topEvent]; exact one_ne_zero, ?_⟩
    intro b hb
    simp only [menu02_val, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · rw [wEU_prior1_act0, wEU_prior1_act2]
      norm_num
    · exact le_refl _

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

/-- On the submenu `{0, 1}` the E-admissibility judgment keeps *both* acts:
the β-violation witness pattern, upper half. -/
theorem eAdm_pair_menu01 :
    (twoPriorCC.eAdm credalPair credalPair_nonempty).C twoPriorCtx.topEvent
      menu01 = {0, 1} := by
  rw [CredalContext.eAdm_C]
  simp only [credalPair]
  rw [Set.biUnion_pair, seu_prior0_menu01, seu_prior1_menu01,
    Set.union_comm, Set.singleton_union]

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

/-! ## M5(a): incommensurability within the SEU class

No single prior can give both extreme SEU judgments even a fair hearing:
agreeing with `prior0` on `{0, 1}` pins `q(false) = 3/5`, agreeing with
`prior1` on `{0, 2}` pins `q(true) = 3/5`, and `3/5 + 3/5 ≠ 1`. -/

theorem no_seu_fairHearing :
    ¬ ∃ q : Fap twoPriorCtx.alg,
      FairHearing (twoPriorCC.seu q) (twoPriorCC.seu prior0)
        (twoPriorCC.seu prior1) := by
  rintro ⟨q, h0, h1⟩
  obtain ⟨x, hxq, hx0⟩ := h0 twoPriorCtx.topEvent menu01
    (by rw [seu_prior0_menu01]; exact ⟨1, rfl⟩)
  rw [seu_prior0_menu01, Set.mem_singleton_iff] at hx0
  subst hx0
  obtain ⟨y, hyq, hy1⟩ := h1 twoPriorCtx.topEvent menu01
    (by rw [seu_prior1_menu01]; exact ⟨0, rfl⟩)
  rw [seu_prior1_menu01, Set.mem_singleton_iff] at hy1
  subst hy1
  obtain ⟨z, hzq, hz0⟩ := h0 twoPriorCtx.topEvent menu02
    (by rw [seu_prior0_menu02]; exact ⟨0, rfl⟩)
  rw [seu_prior0_menu02, Set.mem_singleton_iff] at hz0
  subst hz0
  obtain ⟨w, hwq, hw1⟩ := h1 twoPriorCtx.topEvent menu02
    (by rw [seu_prior1_menu02]; exact ⟨2, rfl⟩)
  rw [seu_prior1_menu02, Set.mem_singleton_iff] at hw1
  subst hw1
  rw [CredalContext.mem_seu_C] at hxq hyq hzq hwq
  have h01 := hxq.2.2 0 (Set.mem_insert 0 {1})
  have h10 := hyq.2.2 1 (Set.mem_insert_of_mem 0 rfl)
  have h02 := hwq.2.2 0 (Set.mem_insert 0 {2})
  have h20 := hzq.2.2 2 (Set.mem_insert_of_mem 0 rfl)
  rw [wEU_top_act0, wEU_top_act1] at h01
  rw [wEU_top_act1, wEU_top_act0] at h10
  rw [wEU_top_act0, wEU_top_act2] at h02
  rw [wEU_top_act2, wEU_top_act0] at h20
  have hsplit := q_split q
  linarith

theorem no_seu_suspends :
    ¬ ∃ q : Fap twoPriorCtx.alg,
      Suspends (twoPriorCC.seu q) (twoPriorCC.seu prior0)
        (twoPriorCC.seu prior1) :=
  fun ⟨q, h⟩ => no_seu_fairHearing ⟨q, h.fairHearing⟩

/-- M5(a): the change between the two extreme SEU judgments is not even
weakly commensurable within the SEU class. -/
theorem not_weaklyCommensurable_KSEU :
    ¬ WeaklyCommensurable twoPriorCC.KSEU (twoPriorCC.seu prior0)
      (twoPriorCC.seu prior1) := by
  rintro ⟨D, ⟨q, rfl⟩, hfh⟩
  exact no_seu_fairHearing ⟨q, hfh⟩

theorem not_commensurable_KSEU :
    ¬ Commensurable twoPriorCC.KSEU (twoPriorCC.seu prior0)
      (twoPriorCC.seu prior1) :=
  fun h => not_weaklyCommensurable_KSEU h.weaklyCommensurable

/-- Levi's move in miniature: within the E-admissibility class the same
change *is* commensurable — the union credal set suspends it. -/
theorem commensurable_KEadm :
    Commensurable twoPriorCC.KEadm (twoPriorCC.seu prior0)
      (twoPriorCC.seu prior1) :=
  twoPriorCC.joinClosed_KEadm.commensurable
    (twoPriorCC.KSEU_subset_KEadm (twoPriorCC.seu_mem_KSEU prior0))
    (twoPriorCC.KSEU_subset_KEadm (twoPriorCC.seu_mem_KSEU prior1))

/-! ## M5(c): the β-corollary instantiated -/

/-- M5(c): the pair's E-admissibility judgment violates Sen's β at the
vacuous supposition — from `{0, 1}` both the safe act and the bet are
admissible, but only the bet survives to the full menu. -/
theorem eAdm_pair_not_senBetaAt :
    ¬ (twoPriorCC.eAdm credalPair credalPair_nonempty).SenBetaAt
      twoPriorCtx.topEvent :=
  AdmissibilityJudgment.not_senBetaAt_of_witness
    (m := fullMenu) (m' := menu01) (Set.subset_univ _)
    (by rw [eAdm_pair_menu01]; exact Set.mem_insert 0 {1})
    (by rw [eAdm_pair_menu01]; exact Set.mem_insert_of_mem 0 rfl)
    safe_excluded
    (by rw [eAdm_pair_full]; exact Set.mem_insert 1 {2})

/-- Hence it violates WARP — while satisfying α (next example). -/
theorem eAdm_pair_not_warpAt :
    ¬ (twoPriorCC.eAdm credalPair credalPair_nonempty).WARPAt
      twoPriorCtx.topEvent :=
  AdmissibilityJudgment.not_warpAt_of_not_senBetaAt eAdm_pair_not_senBetaAt

/-- α survives the join even where β dies. -/
example :
    (twoPriorCC.eAdm credalPair credalPair_nonempty).SenAlphaAt
      twoPriorCtx.topEvent :=
  twoPriorCC.eAdm_senAlphaAt credalPair credalPair_nonempty
    twoPriorCtx.topEvent

/-- The abstract β-corollary instantiated: the E-admissibility class
contains a β-violating judgment. -/
example :
    ∃ D ∈ twoPriorCC.KEadm, ¬ D.SenBetaAt twoPriorCtx.topEvent :=
  ⟨_, twoPriorCC.eAdm_mem_KEadm credalPair credalPair_nonempty,
    eAdm_pair_not_senBetaAt⟩

/-! ## M5(b): the convexity wedge -/

/-- The even mixture of the two priors. -/
noncomputable def uniformP : Fap twoPriorCtx.alg :=
  Fap.mix (1 / 2) (by norm_num) (by norm_num) prior0 prior1

theorem uniformP_eFalse : uniformP.p eFalse = 1 / 2 := by
  simp only [uniformP, Fap.mix_p]
  rw [prior0_eFalse, prior1_eFalse]
  norm_num

theorem uniformP_eTrue : uniformP.p eTrue = 1 / 2 := by
  simp only [uniformP, Fap.mix_p]
  rw [prior0_eTrue, prior1_eTrue]
  norm_num

theorem uniformP_mem_hull : uniformP ∈ Fap.convexHull credalPair := by
  apply Fap.mixtureClosed_convexHull
  · exact Fap.subset_convexHull _ (Set.mem_insert _ _)
  · exact Fap.subset_convexHull _ (Set.mem_insert_of_mem _ rfl)

/-- Under the even mixture the safe act is admissible from the full menu
(indeed uniquely optimal: `6/5 > 1`). -/
theorem safe_in_seu_uniform :
    (0 : twoPriorCtx.Act) ∈
      (twoPriorCC.seu uniformP).C twoPriorCtx.topEvent fullMenu := by
  rw [CredalContext.mem_seu_C]
  refine ⟨Set.mem_univ 0, by rw [Fap.p_topEvent]; exact one_ne_zero, ?_⟩
  intro b _
  rcases fin3_eq b with rfl | rfl | rfl
  · exact le_refl _
  · rw [wEU_top_act1, wEU_top_act0, uniformP_eFalse]
    norm_num
  · rw [wEU_top_act2, wEU_top_act0, uniformP_eTrue]
    norm_num

/-- M5(b), the convexity wedge: the two-prior credal set is *not*
choice-equivalent to its convex hull — the even mixture admits the safe
act that the pair excludes. Commensuration closure never forces convex
closure. -/
theorem not_convexEquivalent :
    ¬ twoPriorCC.ConvexEquivalent credalPair credalPair_nonempty := by
  intro h
  apply safe_excluded
  rw [h]
  exact twoPriorCC.mem_eAdm_C.mpr
    ⟨uniformP, uniformP_mem_hull, safe_in_seu_uniform⟩

/-! ## Commutation sanity check -/

instance : Min twoPriorCtx.Event := DecisionContext.instMinEvent twoPriorCtx

theorem prior0_eFalse_ne_zero : prior0.p eFalse ≠ 0 := by
  rw [prior0_eFalse]
  norm_num

/-- Conditioning `prior0` on `eFalse` and judging at the vacuous
supposition agrees with judging `prior0` at supposition `eFalse ⊓ ⊤`. -/
example (m : twoPriorCtx.Menu) :
    (twoPriorCC.seu (prior0.condition eFalse prior0_eFalse_ne_zero)).C
        twoPriorCtx.topEvent m =
      (twoPriorCC.seu prior0).C (eFalse ⊓ twoPriorCtx.topEvent) m :=
  twoPriorCC.seu_condition_C prior0 prior0_eFalse_ne_zero
    twoPriorCtx.topEvent m

end CAJTest
