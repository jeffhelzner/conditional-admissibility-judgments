import CAJ.Judgment
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Bounds.Basic

/-!
# M0: pointwise joins of admissibility judgments

The poset of admissibility judgments over a fixed context has all *nonempty*
joins, computed pointwise: `(⋁ S).C e m = ⋃ J ∈ S, J.C e m`. The
null-supposition dichotomy is preserved — a join is live at `e` iff some
member is — which is exactly why nullity is encoded as emptiness rather than
by defaulting to the menu.

There is no bottom and no empty join: the empty union would be dead at
`univ`, violating `live_univ`. Binary joins give a `SemilatticeSup`
instance; general nonempty joins are provided by `sJoin`.
-/

namespace CAJ

namespace AdmissibilityJudgment

variable {ctx : DecisionContext}

/-- Binary join: pointwise union of choice sets. -/
protected def sup (J K : AdmissibilityJudgment ctx) : AdmissibilityJudgment ctx where
  C e m := J.C e m ∪ K.C e m
  choice_subset e m :=
    Set.union_subset (J.choice_subset e m) (K.choice_subset e m)
  live_or_dead e := by
    rcases J.live_or_dead e with hl | hd
    · exact Or.inl fun m => (hl m).mono Set.subset_union_left
    · rcases K.live_or_dead e with hl' | hd'
      · exact Or.inl fun m => (hl' m).mono Set.subset_union_right
      · exact Or.inr fun m => by rw [hd m, hd' m, Set.union_empty]
  live_univ m := (J.live_univ m).mono Set.subset_union_left

instance : SemilatticeSup (AdmissibilityJudgment ctx) :=
  { (inferInstance : PartialOrder (AdmissibilityJudgment ctx)) with
    sup := AdmissibilityJudgment.sup
    le_sup_left := fun _ _ _ _ => Set.subset_union_left
    le_sup_right := fun _ _ _ _ => Set.subset_union_right
    sup_le := fun _ _ _ h h' e m => Set.union_subset (h e m) (h' e m) }

@[simp]
theorem sup_C (J K : AdmissibilityJudgment ctx) (e : ctx.Event) (m : ctx.Menu) :
    (J ⊔ K).C e m = J.C e m ∪ K.C e m :=
  rfl

/-- The join of a nonempty set of judgments, computed pointwise. -/
def sJoin (S : Set (AdmissibilityJudgment ctx)) (hS : S.Nonempty) :
    AdmissibilityJudgment ctx where
  C e m := ⋃ J ∈ S, J.C e m
  choice_subset e m := Set.iUnion₂_subset fun J _ => J.choice_subset e m
  live_or_dead e := by
    by_cases h : ∃ J ∈ S, J.Live e
    · obtain ⟨J, hJ, hlive⟩ := h
      exact Or.inl fun m => (hlive m).mono (Set.subset_biUnion_of_mem hJ)
    · push Not at h
      refine Or.inr fun m => Set.eq_empty_iff_forall_notMem.mpr fun a ha => ?_
      simp only [Set.mem_iUnion] at ha
      obtain ⟨J, hJ, ha⟩ := ha
      rw [J.dead_of_not_live (h J hJ) m] at ha
      exact ha
  live_univ m :=
    (hS.choose.live_univ m).mono (Set.subset_biUnion_of_mem hS.choose_spec)

@[simp]
theorem sJoin_C (S : Set (AdmissibilityJudgment ctx)) (hS : S.Nonempty)
    (e : ctx.Event) (m : ctx.Menu) :
    (sJoin S hS).C e m = ⋃ J ∈ S, J.C e m :=
  rfl

theorem le_sJoin {S : Set (AdmissibilityJudgment ctx)} (hS : S.Nonempty)
    {J : AdmissibilityJudgment ctx} (hJ : J ∈ S) : J ≤ sJoin S hS :=
  fun e m => Set.subset_biUnion_of_mem (u := fun J => J.C e m) hJ

theorem sJoin_le {S : Set (AdmissibilityJudgment ctx)} {hS : S.Nonempty}
    {K : AdmissibilityJudgment ctx} (h : ∀ J ∈ S, J ≤ K) : sJoin S hS ≤ K :=
  fun e m => Set.iUnion₂_subset fun J hJ => h J hJ e m

/-- M0: `sJoin S hS` is the least upper bound of `S`. -/
theorem isLUB_sJoin (S : Set (AdmissibilityJudgment ctx)) (hS : S.Nonempty) :
    IsLUB S (sJoin S hS) :=
  ⟨fun _ hJ => le_sJoin hS hJ, fun _ hK => sJoin_le fun _ hJ => hK hJ⟩

theorem sJoin_mono {S T : Set (AdmissibilityJudgment ctx)} (hS : S.Nonempty)
    (hT : T.Nonempty) (h : S ⊆ T) : sJoin S hS ≤ sJoin T hT :=
  sJoin_le fun _ hJ => le_sJoin hT (h hJ)

/-- `sJoin` respects equality of the index class (the nonemptiness proof is
irrelevant). -/
theorem sJoin_congr {S T : Set (AdmissibilityJudgment ctx)} (h : S = T)
    (hS : S.Nonempty) : sJoin S hS = sJoin T (h ▸ hS) := by
  subst h; rfl

/-- Joins split across unions of index classes. -/
theorem sJoin_union (S T : Set (AdmissibilityJudgment ctx)) (hS : S.Nonempty)
    (hT : T.Nonempty) :
    sJoin (S ∪ T) hS.inl = sJoin S hS ⊔ sJoin T hT :=
  ext fun e m => by
    rw [sJoin_C, sup_C, sJoin_C, sJoin_C, Set.biUnion_union]

@[simp]
theorem sJoin_singleton (J : AdmissibilityJudgment ctx)
    (h : ({J} : Set (AdmissibilityJudgment ctx)).Nonempty := Set.singleton_nonempty J) :
    sJoin {J} h = J :=
  ext fun e m => by simp

theorem sJoin_pair (J K : AdmissibilityJudgment ctx)
    (h : ({J, K} : Set (AdmissibilityJudgment ctx)).Nonempty :=
      ⟨J, Set.mem_insert J {K}⟩) :
    sJoin {J, K} h = J ⊔ K :=
  ext fun e m => by simp

/-- A join is live exactly where some member is live. -/
theorem sJoin_live_iff {S : Set (AdmissibilityJudgment ctx)} (hS : S.Nonempty)
    {e : ctx.Event} : (sJoin S hS).Live e ↔ ∃ J ∈ S, J.Live e := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨m⟩ := (inferInstance : Nonempty ctx.Menu)
    obtain ⟨a, ha⟩ := h m
    simp only [sJoin_C, Set.mem_iUnion] at ha
    obtain ⟨J, hJ, ha⟩ := ha
    rw [J.dead_of_not_live (hn J hJ) m] at ha
    exact ha
  · rintro ⟨J, hJ, hlive⟩
    exact hlive.mono (le_sJoin hS hJ)

end AdmissibilityJudgment

end CAJ
