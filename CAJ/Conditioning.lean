import CAJ.EAdmissibility
import Mathlib.Algebra.BigOperators.Field

/-!
# Commutation: suppositional conditioning commutes with joins

Conditioning is *internal* — it lives in the supposition slot `e` — while
credal change is external. This file makes the interaction precise.

`Fap.condition p e h` is the conditional probability given a non-null
member `e` (ordinary Bayes conditioning on the algebra). The generalized
Bayes rule for credal sets is memberwise conditioning of the non-null
members, `Fap.conditionOn`.

The commutation theorem (`eAdm_conditionOn_C`) says the two routes agree:
conditioning the credal set memberwise and judging at supposition `f` is
the same as judging with the original credal set at the conjoined
supposition `e ⊓ f`. The engine is `seu_condition_C` — SEU maximization
against a conditioned prior coincides with maximization against the
original prior at the conjoined supposition (positive rescaling of
unnormalized conditional expected utility, `wEU_condition`) — plus the
Phase 1 null policy: members that treat `e` as null are dead at `e ⊓ f`
and contribute nothing to the join, exactly matching their exclusion from
the conditioned credal set. This is Levi's confirmational
conditionalization for E-admissibility: it conditions memberwise.

The statement is pointwise on choice sets because "the conditioning of a
judgment" is not itself an admissibility judgment: `live_univ` can fail at
the vacuous supposition (a prior null on `e` is dead at `e ⊓ ⊤`).
-/

namespace CAJ

universe u

namespace Fap

variable {X : Type u} {E : SetAlgebra X}

/-- Bayes conditioning of a finitely additive probability on a non-null
member of the algebra. -/
noncomputable def condition (p : Fap E) (e : {s : Set X // s ∈ E})
    (h : p.p e ≠ 0) : Fap E where
  p s := p.p ⟨s.val ∩ e.val, E.inter_mem s.2 e.2⟩ / p.p e
  nonneg s := div_nonneg (p.nonneg _) (p.nonneg e)
  p_univ := by
    rw [p.p_congr (t := e) (Set.univ_inter e.val), div_self h]
  additive s t hd := by
    rw [← add_div]
    congr 1
    rw [p.p_congr
      (t := ⟨(s.val ∩ e.val) ∪ (t.val ∩ e.val),
        E.union_mem (E.inter_mem s.2 e.2) (E.inter_mem t.2 e.2)⟩)
      (Set.union_inter_distrib_right _ _ _)]
    exact p.additive ⟨s.val ∩ e.val, E.inter_mem s.2 e.2⟩
      ⟨t.val ∩ e.val, E.inter_mem t.2 e.2⟩
      (hd.mono Set.inter_subset_left Set.inter_subset_left)

theorem condition_p (p : Fap E) (e : {s : Set X // s ∈ E}) (h : p.p e ≠ 0)
    (s : {s : Set X // s ∈ E}) :
    (p.condition e h).p s = p.p ⟨s.val ∩ e.val, E.inter_mem s.2 e.2⟩ / p.p e :=
  rfl

/-- Memberwise conditioning of a credal set (generalized Bayes): the
conditional probabilities of those members that do not treat `e` as
null. -/
def conditionOn (P : Set (Fap E)) (e : {s : Set X // s ∈ E}) :
    Set (Fap E) :=
  {q | ∃ p ∈ P, ∃ hpe : p.p e ≠ 0, q = p.condition e hpe}

end Fap

/-- The conditioned prior treats a supposition as non-null exactly when the
original prior does not treat the conjunction as null. -/
theorem Fap.condition_p_ne_zero_iff {ctx : DecisionContext}
    (p : Fap ctx.alg) {e : ctx.Event} (h : p.p e ≠ 0) (f : ctx.Event) :
    (p.condition e h).p f ≠ 0 ↔ p.p (e ⊓ f) ≠ 0 := by
  rw [Fap.condition_p, div_ne_zero_iff,
    p.p_congr (t := e ⊓ f) (Set.inter_comm f.val e.val)]
  exact and_iff_left h

namespace CredalContext

open DecisionContext

variable {ctx : DecisionContext} (cc : CredalContext ctx)

/-- Unnormalized conditional expected utility against a conditioned prior
is the original conditional expected utility at the conjoined supposition,
rescaled by the (positive) probability of the conditioning event. -/
theorem wEU_condition (p : Fap ctx.alg) {e : ctx.Event} (h : p.p e ≠ 0)
    (f : ctx.Event) (a : ctx.Act) :
    cc.wEU (p.condition e h) f a = cc.wEU p (e ⊓ f) a / p.p e := by
  unfold wEU
  have hterm : ∀ r ∈ (cc.finite_range a f).toFinset,
      r * (p.condition e h).p ⟨cc.U a ⁻¹' {r} ∩ f.val, cc.level_mem a r f⟩
        = r * p.p ⟨cc.U a ⁻¹' {r} ∩ (e ⊓ f).val, cc.level_mem a r (e ⊓ f)⟩
            / p.p e := by
    intro r _
    have hset : (cc.U a ⁻¹' {r} ∩ f.val) ∩ e.val
        = cc.U a ⁻¹' {r} ∩ (e ⊓ f).val := by
      rw [inf_event_val, Set.inter_assoc, Set.inter_comm f.val e.val]
    rw [Fap.condition_p, mul_div_assoc]
    congr 2
    exact p.p_congr hset
  rw [Finset.sum_congr rfl hterm, Finset.sum_div]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro r hr
    rw [Set.Finite.mem_toFinset] at hr ⊢
    exact Set.image_mono Set.inter_subset_right hr
  · intro r _ hr
    rw [Set.Finite.mem_toFinset] at hr
    have hempty : cc.U a ⁻¹' {r} ∩ (e ⊓ f).val = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hxef⟩
      exact hr ⟨x, hxef, hx⟩
    rw [p.p_congr (t := ⟨∅, ctx.alg.empty_mem⟩) hempty, p.p_empty, mul_zero,
      zero_div]

/-- Generalized Bayes for SEU: the SEU judgment of the conditioned prior at
supposition `f` has the same choice sets as the SEU judgment of the
original prior at the conjoined supposition `e ⊓ f`. -/
theorem seu_condition_C (p : Fap ctx.alg) {e : ctx.Event} (h : p.p e ≠ 0)
    (f : ctx.Event) (m : ctx.Menu) :
    (cc.seu (p.condition e h)).C f m = (cc.seu p).C (e ⊓ f) m := by
  ext a
  rw [mem_seu_C, mem_seu_C]
  have hpos : 0 < p.p e := lt_of_le_of_ne (p.nonneg e) (Ne.symm h)
  have hEU : ∀ b : ctx.Act,
      (cc.wEU (p.condition e h) f b ≤ cc.wEU (p.condition e h) f a
        ↔ cc.wEU p (e ⊓ f) b ≤ cc.wEU p (e ⊓ f) a) := fun b => by
    rw [cc.wEU_condition p h f b, cc.wEU_condition p h f a,
      div_le_div_iff_of_pos_right hpos]
  constructor
  · rintro ⟨ham, hne, hmax⟩
    exact ⟨ham, (p.condition_p_ne_zero_iff h f).mp hne,
      fun b hb => (hEU b).mp (hmax b hb)⟩
  · rintro ⟨ham, hne, hmax⟩
    exact ⟨ham, (p.condition_p_ne_zero_iff h f).mpr hne,
      fun b hb => (hEU b).mpr (hmax b hb)⟩

/-- A prior null on `e` chooses nothing at any conjoined supposition. -/
theorem seu_C_null (p : Fap ctx.alg) {e' : ctx.Event} (h : p.p e' = 0)
    (m : ctx.Menu) : (cc.seu p).C e' m = ∅ :=
  cc.seu_dead_iff.mpr h m

/-- Commutation (headline): suppositional conditioning commutes with the
credal join. Pointwise, the E-admissibility judgment of the
memberwise-conditioned credal set at supposition `f` coincides with the
original E-admissibility judgment at the conjoined supposition `e ⊓ f` —
E-admissibility conditions memberwise (generalized Bayes), and the null
members drop out on both sides. -/
theorem eAdm_conditionOn_C (P : Set (Fap ctx.alg)) (hP : P.Nonempty)
    {e : ctx.Event} (hne : (Fap.conditionOn P e).Nonempty)
    (f : ctx.Event) (m : ctx.Menu) :
    (cc.eAdm (Fap.conditionOn P e) hne).C f m =
      (cc.eAdm P hP).C (e ⊓ f) m := by
  rw [eAdm_C, eAdm_C]
  apply subset_antisymm
  · refine Set.iUnion₂_subset fun q hq => ?_
    obtain ⟨p, hp, hpe, rfl⟩ := hq
    rw [cc.seu_condition_C p hpe f m]
    exact Set.subset_biUnion_of_mem (u := fun p => (cc.seu p).C (e ⊓ f) m) hp
  · refine Set.iUnion₂_subset fun p hp => ?_
    by_cases hpe : p.p e = 0
    · have h0 : p.p (e ⊓ f) = 0 :=
        le_antisymm
          (hpe ▸ p.mono (s := e ⊓ f) (t := e) Set.inter_subset_left)
          (p.nonneg _)
      rw [cc.seu_C_null p h0 m]
      exact Set.empty_subset _
    · rw [← cc.seu_condition_C p hpe f m]
      exact Set.subset_biUnion_of_mem (u := fun q => (cc.seu q).C f m)
        ⟨p, hp, hpe, rfl⟩

end CredalContext

end CAJ
