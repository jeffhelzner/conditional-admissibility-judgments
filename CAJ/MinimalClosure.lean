import CAJ.EAdmissibility
import CAJ.Commensuration

/-!
# M2/M3 instance: E-admissibility as the minimal commensuration closure of SEU

The headline identification. `KSEU` is the class of judgments representable
by a single prior (`Set.range cc.seu`); `KEadm` the class representable by a
nonempty credal set. The main theorem `commensurationClosure_KSEU` computes
the commensuration closure of the SEU class:

  `commensurationClosure KSEU = KEadm`.

Consequences, all essentially free from the closure-operator framework:

* `joinClosed_KEadm` — the E-admissibility class is join-closed;
* `KEadm_minimal` — it is the **least** join-closed extension of `KSEU`
  (M3's minimality, from the universal property);
* `eAdm_union` / `suspends_eAdm_union` / `eAdm_union_le` — M3 concretely:
  the commensurating intermediary between two credal judgments is the
  E-admissibility judgment of the *union* credal set, and it is the least
  intermediary;
* `eAdm_commensurable` / `zigZagIn_KEadm_iff` — the cospan normal form
  instantiated: within `KEadm` every zig-zag between credal judgments
  reduces to the diameter-≤ 2 cospan through the join.

`eAdm_unique` is the comparative universal property: E-admissibility is the
**unique** extension of SEU maximization to credal sets that is determined
by its singletons via joins (the `sSupHom` reading of M2).

M4 is *stated* (`ConvexEquivalent`): a credal set may or may not be
choice-equivalent to its convex hull. `eAdm_le_eAdm_convexHull` is the easy
half; the two-prior witness (`test/CAJTest/TwoPrior.lean`) shows strictness
can occur — the convexity wedge: commensuration closure never forces convex
closure.
-/

namespace CAJ

namespace CredalContext

open AdmissibilityJudgment

variable {ctx : DecisionContext} (cc : CredalContext ctx)

/-- The SEU-representable class: judgments of single priors. -/
def KSEU : Set (AdmissibilityJudgment ctx) := Set.range cc.seu

/-- The E-admissibility-representable class: judgments of nonempty credal
sets. -/
def KEadm : Set (AdmissibilityJudgment ctx) :=
  {J | ∃ P, ∃ hP : P.Nonempty, J = cc.eAdm P hP}

theorem seu_mem_KSEU (p : Fap ctx.alg) : cc.seu p ∈ cc.KSEU :=
  ⟨p, rfl⟩

theorem eAdm_mem_KEadm (P : Set (Fap ctx.alg)) (hP : P.Nonempty) :
    cc.eAdm P hP ∈ cc.KEadm :=
  ⟨P, hP, rfl⟩

/-- Singleton credal sets embed SEU into the E-admissibility class. -/
theorem KSEU_subset_KEadm : cc.KSEU ⊆ cc.KEadm := by
  rintro J ⟨p, rfl⟩
  exact ⟨{p}, Set.singleton_nonempty p, (cc.eAdm_singleton p).symm⟩

/-- M2 (headline instance): the commensuration closure of the
SEU-representable class is exactly the E-admissibility class. -/
theorem commensurationClosure_KSEU :
    commensurationClosure cc.KSEU = cc.KEadm := by
  apply subset_antisymm
  · rintro J ⟨S, hS, hsub, rfl⟩
    have himg : cc.seu '' {p | cc.seu p ∈ S} = S := by
      apply subset_antisymm
      · rintro q ⟨p, hp, rfl⟩
        exact hp
      · intro q hq
        obtain ⟨p, rfl⟩ := hsub hq
        exact ⟨p, hq, rfl⟩
    have hPne : {p | cc.seu p ∈ S}.Nonempty := by
      obtain ⟨q, hq⟩ := hS
      obtain ⟨p, rfl⟩ := hsub hq
      exact ⟨p, hq⟩
    refine ⟨{p | cc.seu p ∈ S}, hPne, ?_⟩
    rw [cc.eAdm_eq_sJoin]
    exact sJoin_congr himg.symm hS
  · rintro J ⟨P, hP, rfl⟩
    exact ⟨cc.seu '' P, hP.image cc.seu, Set.image_subset_range cc.seu P, rfl⟩

/-- The E-admissibility class is join-closed. -/
theorem joinClosed_KEadm : JoinClosed cc.KEadm := by
  rw [← cc.commensurationClosure_KSEU]
  exact joinClosed_commensurationClosure _

/-- Minimality (M2/M3, free from the universal property): the
E-admissibility class is contained in every join-closed extension of the
SEU class. -/
theorem KEadm_minimal {L : Set (AdmissibilityJudgment ctx)}
    (hL : cc.KSEU ⊆ L) (hLj : JoinClosed L) : cc.KEadm ⊆ L := by
  rw [← cc.commensurationClosure_KSEU]
  exact commensurationClosure_le hL hLj

/-! ## M3: the commensurating intermediary between credal judgments -/

/-- E-admissibility turns unions of credal sets into joins of judgments. -/
theorem eAdm_union (P Q : Set (Fap ctx.alg)) (hP : P.Nonempty)
    (hQ : Q.Nonempty) :
    cc.eAdm (P ∪ Q) hP.inl = cc.eAdm P hP ⊔ cc.eAdm Q hQ :=
  AdmissibilityJudgment.ext fun e m => by
    rw [eAdm_C, sup_C, eAdm_C, eAdm_C, Set.biUnion_union]

/-- M3: the E-admissibility judgment of the union credal set suspends the
issue between the judgments of the parts. -/
theorem suspends_eAdm_union (P Q : Set (Fap ctx.alg)) (hP : P.Nonempty)
    (hQ : Q.Nonempty) :
    Suspends (cc.eAdm (P ∪ Q) hP.inl) (cc.eAdm P hP) (cc.eAdm Q hQ) := by
  rw [cc.eAdm_union P Q hP hQ]
  exact ⟨le_sup_left, le_sup_right⟩

/-- M3 minimality (free): the union judgment is the least judgment
suspending between the two credal judgments. -/
theorem eAdm_union_le {P Q : Set (Fap ctx.alg)} {hP : P.Nonempty}
    {hQ : Q.Nonempty} {D : AdmissibilityJudgment ctx}
    (hPD : cc.eAdm P hP ≤ D) (hQD : cc.eAdm Q hQ ≤ D) :
    cc.eAdm (P ∪ Q) hP.inl ≤ D := by
  rw [cc.eAdm_union P Q hP hQ]
  exact sup_le hPD hQD

/-- Any two E-admissibility judgments are commensurable within the
E-admissibility class. -/
theorem eAdm_commensurable (P Q : Set (Fap ctx.alg)) (hP : P.Nonempty)
    (hQ : Q.Nonempty) :
    Commensurable cc.KEadm (cc.eAdm P hP) (cc.eAdm Q hQ) :=
  cc.joinClosed_KEadm.commensurable (cc.eAdm_mem_KEadm P hP)
    (cc.eAdm_mem_KEadm Q hQ)

/-- Cospan normal form, instantiated to the credal class: zig-zag
connectedness within `KEadm` coincides with commensurability, i.e. every
zig-zag between credal judgments reduces to a diameter-≤ 2 cospan through
the join. -/
theorem zigZagIn_KEadm_iff {J J' : AdmissibilityJudgment ctx}
    (hJ : J ∈ cc.KEadm) (hJ' : J' ∈ cc.KEadm) :
    ZigZagIn cc.KEadm J J' ↔ Commensurable cc.KEadm J J' :=
  zigZagIn_iff_commensurable cc.joinClosed_KEadm hJ hJ'

/-! ## Uniqueness: the universal property of E-admissibility -/

/-- E-admissibility is determined by its singleton values via joins. -/
theorem eAdm_eq_sJoin_singletons (P : Set (Fap ctx.alg)) (hP : P.Nonempty) :
    cc.eAdm P hP =
      sJoin ((fun p => cc.eAdm {p} (Set.singleton_nonempty p)) '' P)
        (hP.image _) := by
  rw [cc.eAdm_eq_sJoin]
  exact sJoin_congr
    (Set.image_congr' fun p => (cc.eAdm_singleton p).symm) (hP.image _)

/-- M2, comparative universal property (the `sSupHom` reading):
E-admissibility is the **unique** assignment of judgments to nonempty
credal sets that agrees with SEU on singletons and is determined by its
singleton values via joins. -/
theorem eAdm_unique
    (F : (P : Set (Fap ctx.alg)) → P.Nonempty → AdmissibilityJudgment ctx)
    (hsingle : ∀ p, F {p} (Set.singleton_nonempty p) = cc.seu p)
    (hjoin : ∀ P (hP : P.Nonempty),
      F P hP = sJoin ((fun p => F {p} (Set.singleton_nonempty p)) '' P)
        (hP.image _)) :
    ∀ P (hP : P.Nonempty), F P hP = cc.eAdm P hP := by
  intro P hP
  rw [hjoin P hP, cc.eAdm_eq_sJoin]
  exact sJoin_congr (Set.image_congr' hsingle) (hP.image _)

/-! ## M4: statement and the easy half -/

/-- Convexification only coarsens choice: E-admissibility over the convex
hull refines pointwise-upward. -/
theorem eAdm_le_eAdm_convexHull (P : Set (Fap ctx.alg)) (hP : P.Nonempty) :
    cc.eAdm P hP ≤
      cc.eAdm (Fap.convexHull P) (hP.mono (Fap.subset_convexHull P)) :=
  cc.eAdm_mono _ _ (Fap.subset_convexHull P)

/-- M4 (statement): a credal set is *convex-equivalent* when its
E-admissibility judgment coincides with that of its convex hull. The
convexity wedge (M5(b), witnessed in `test/CAJTest/TwoPrior.lean`) is that
this can fail: commensuration closure never forces convex closure. -/
def ConvexEquivalent (P : Set (Fap ctx.alg)) (hP : P.Nonempty) : Prop :=
  cc.eAdm P hP =
    cc.eAdm (Fap.convexHull P) (hP.mono (Fap.subset_convexHull P))

end CredalContext

end CAJ
