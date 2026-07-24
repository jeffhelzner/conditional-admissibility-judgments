import CAJ.Fap
import CAJ.Join
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Lattice.Image

/-!
# SEU judgments and E-admissibility

A `CredalContext` equips the fixed decision context with the evaluation
data needed for expected utility: a state-dependent utility `U` for acts,
finiteness of each act's utility range on each supposition, membership of
utility level sets in the algebra, and finiteness of menus (so maximizers
exist).

`wEU p e a` is the *unnormalized* conditional expected utility
`∑ r ∈ range(U a on e), r * p (U a ⁻¹' {r} ∩ e)`. Since normalizing by
`1 / p e` is a positive rescaling whenever `p e ≠ 0`, maximization — hence
admissibility — is unaffected, and no division is needed.

`seu p` is the SEU judgment of the single prior `p`: at a supposition `p`
treats as null (`p.p e = 0`) the judgment is dead (empty choice sets, per
the Phase 1 null policy); elsewhere it selects the `wEU`-maximizers.

`eAdm P hP` is the E-admissibility judgment of the credal set `P`,
*defined* as the pointwise join of the singleton SEU judgments — so the
join identity M1, `C_P = ⋁_{p ∈ P} C_{{p}}`, is definitional
(`eAdm_eq_sJoin`), and `eAdm_C` is its pointwise form
`C_P(e,m) = ⋃_{p ∈ P} C_{{p}}(e,m)`. Monotonicity in the credal set
follows from monotonicity of joins. The identification of the closure
instance `cc(K_SEU) = K_Eadm` is Phase 4.
-/

namespace CAJ

open DecisionContext

/-- The probability of the vacuous supposition is 1. -/
theorem Fap.p_topEvent {ctx : DecisionContext} (p : Fap ctx.alg) :
    p.p ctx.topEvent = 1 :=
  p.p_univ

/-- Expected-utility evaluation data over the fixed decision context:
state-dependent utilities for acts, with the finiteness and measurability
side conditions needed to compute expectations against a `Fap` and to
guarantee that maximizers exist on menus. -/
structure CredalContext (ctx : DecisionContext) where
  /-- State-dependent utility of acts. -/
  U : ctx.Act → ctx.State → ℝ
  /-- Each act takes finitely many utility values on each supposition. -/
  finite_range : ∀ (a : ctx.Act) (e : ctx.Event), (U a '' e.val).Finite
  /-- Utility level sets (within a supposition) belong to the algebra. -/
  level_mem : ∀ (a : ctx.Act) (r : ℝ) (e : ctx.Event),
    U a ⁻¹' {r} ∩ e.val ∈ ctx.alg
  /-- Menus are finite, so expected-utility maximizers exist. -/
  menus_finite : ∀ m : ctx.Menu, m.val.Finite

namespace CredalContext

variable {ctx : DecisionContext} (cc : CredalContext ctx)

/-- Unnormalized conditional expected utility of act `a` under supposition
`e`, relative to the prior `p`: the sum over the (finite) utility range of
`a` on `e` of each value weighted by the probability of its level set. -/
noncomputable def wEU (p : Fap ctx.alg) (e : ctx.Event) (a : ctx.Act) : ℝ :=
  (cc.finite_range a e).toFinset.sum fun r =>
    r * p.p ⟨cc.U a ⁻¹' {r} ∩ e.val, cc.level_mem a r e⟩

/-- Compute `wEU` against any concrete `Finset` enumerating the utility
range. -/
theorem wEU_eq_sum {p : Fap ctx.alg} {e : ctx.Event} {a : ctx.Act}
    (s : Finset ℝ) (hs : cc.U a '' e.val = ↑s) :
    cc.wEU p e a =
      ∑ r ∈ s, r * p.p ⟨cc.U a ⁻¹' {r} ∩ e.val, cc.level_mem a r e⟩ := by
  unfold wEU
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext r
  rw [Set.Finite.mem_toFinset, hs, Finset.mem_coe]

/-- The SEU judgment of a single prior `p`: at suppositions `p` treats as
null the judgment is dead; elsewhere it admits exactly the maximizers of
(unnormalized) conditional expected utility. -/
def seu (p : Fap ctx.alg) : AdmissibilityJudgment ctx where
  C e m := {a | a ∈ m.val ∧ p.p e ≠ 0 ∧
    ∀ b ∈ m.val, cc.wEU p e b ≤ cc.wEU p e a}
  choice_subset _ _ := fun _ ha => ha.1
  live_or_dead e := by
    by_cases h : p.p e = 0
    · exact Or.inr fun m =>
        Set.eq_empty_iff_forall_notMem.mpr fun a ha => ha.2.1 h
    · refine Or.inl fun m => ?_
      obtain ⟨a, ham, hmax⟩ := Set.exists_max_image m.val (cc.wEU p e)
        (cc.menus_finite m) (ctx.menu_nonempty m)
      exact ⟨a, ham, h, hmax⟩
  live_univ m := by
    obtain ⟨a, ham, hmax⟩ := Set.exists_max_image m.val (cc.wEU p ctx.topEvent)
      (cc.menus_finite m) (ctx.menu_nonempty m)
    refine ⟨a, ham, ?_, hmax⟩
    rw [p.p_topEvent]
    exact one_ne_zero

@[simp]
theorem mem_seu_C {p : Fap ctx.alg} {e : ctx.Event} {m : ctx.Menu}
    {a : ctx.Act} :
    a ∈ (cc.seu p).C e m ↔
      a ∈ m.val ∧ p.p e ≠ 0 ∧ ∀ b ∈ m.val, cc.wEU p e b ≤ cc.wEU p e a :=
  Iff.rfl

/-- An SEU judgment is live exactly at the suppositions its prior does not
treat as null. -/
theorem seu_live_iff {p : Fap ctx.alg} {e : ctx.Event} :
    (cc.seu p).Live e ↔ p.p e ≠ 0 := by
  constructor
  · intro h hp
    obtain ⟨m⟩ := (inferInstance : Nonempty ctx.Menu)
    obtain ⟨a, ha⟩ := h m
    exact ha.2.1 hp
  · intro hp m
    obtain ⟨a, ham, hmax⟩ := Set.exists_max_image m.val (cc.wEU p e)
      (cc.menus_finite m) (ctx.menu_nonempty m)
    exact ⟨a, ham, hp, hmax⟩

/-- An SEU judgment is dead exactly at the suppositions its prior treats
as null. -/
theorem seu_dead_iff {p : Fap ctx.alg} {e : ctx.Event} :
    (cc.seu p).Dead e ↔ p.p e = 0 := by
  constructor
  · intro hd
    by_contra hne
    exact ((cc.seu p).not_dead_of_live (cc.seu_live_iff.mpr hne)) hd
  · intro h0
    exact (cc.seu p).dead_of_not_live fun hl => cc.seu_live_iff.mp hl h0

/-! ## E-admissibility -/

/-- The E-admissibility judgment of a nonempty credal set `P`: the
pointwise join of the singleton SEU judgments of its members. -/
def eAdm (P : Set (Fap ctx.alg)) (hP : P.Nonempty) :
    AdmissibilityJudgment ctx :=
  AdmissibilityJudgment.sJoin (cc.seu '' P) (hP.image cc.seu)

/-- M1 (join identity), definitional form: `C_P = ⋁_{p ∈ P} C_{{p}}`. -/
theorem eAdm_eq_sJoin (P : Set (Fap ctx.alg)) (hP : P.Nonempty) :
    cc.eAdm P hP = AdmissibilityJudgment.sJoin (cc.seu '' P) (hP.image cc.seu) :=
  rfl

/-- M1 (join identity), pointwise form:
`C_P(e,m) = ⋃_{p ∈ P} C_{{p}}(e,m)`. -/
theorem eAdm_C (P : Set (Fap ctx.alg)) (hP : P.Nonempty) (e : ctx.Event)
    (m : ctx.Menu) :
    (cc.eAdm P hP).C e m = ⋃ p ∈ P, (cc.seu p).C e m := by
  unfold eAdm
  rw [AdmissibilityJudgment.sJoin_C, Set.biUnion_image]

/-- An act is E-admissible iff it is SEU-admissible under some prior in
the credal set. -/
theorem mem_eAdm_C {P : Set (Fap ctx.alg)} {hP : P.Nonempty} {e : ctx.Event}
    {m : ctx.Menu} {a : ctx.Act} :
    a ∈ (cc.eAdm P hP).C e m ↔ ∃ p ∈ P, a ∈ (cc.seu p).C e m := by
  rw [eAdm_C]
  simp only [Set.mem_iUnion, exists_prop]

/-- Singleton credal sets recover SEU: sanity check for the
representation. -/
theorem eAdm_singleton (p : Fap ctx.alg) :
    cc.eAdm {p} (Set.singleton_nonempty p) = cc.seu p :=
  AdmissibilityJudgment.ext fun e m => by rw [eAdm_C]; simp

/-- Each member prior's SEU judgment refines the E-admissibility judgment
of the credal set. -/
theorem seu_le_eAdm {P : Set (Fap ctx.alg)} {hP : P.Nonempty}
    {p : Fap ctx.alg} (hp : p ∈ P) : cc.seu p ≤ cc.eAdm P hP :=
  AdmissibilityJudgment.le_sJoin _ (Set.mem_image_of_mem _ hp)

/-- Monotonicity: E-admissibility is monotone in the credal set. -/
theorem eAdm_mono {P Q : Set (Fap ctx.alg)} (hP : P.Nonempty)
    (hQ : Q.Nonempty) (h : P ⊆ Q) : cc.eAdm P hP ≤ cc.eAdm Q hQ :=
  AdmissibilityJudgment.sJoin_mono _ _ (Set.image_mono h)

/-- An E-admissibility judgment is live exactly where some member prior is
non-null. -/
theorem eAdm_live_iff {P : Set (Fap ctx.alg)} {hP : P.Nonempty}
    {e : ctx.Event} :
    (cc.eAdm P hP).Live e ↔ ∃ p ∈ P, p.p e ≠ 0 := by
  unfold eAdm
  rw [AdmissibilityJudgment.sJoin_live_iff]
  constructor
  · rintro ⟨J, ⟨p, hp, rfl⟩, hlive⟩
    exact ⟨p, hp, cc.seu_live_iff.mp hlive⟩
  · rintro ⟨p, hp, hne⟩
    exact ⟨cc.seu p, Set.mem_image_of_mem _ hp, cc.seu_live_iff.mpr hne⟩

end CredalContext

end CAJ
