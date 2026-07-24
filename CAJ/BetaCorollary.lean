import CAJ.Sen
import CAJ.EAdmissibility
import CAJ.Commensuration

/-!
# β-corollary: joins preserve α, destroy β

The static side of the headline package. Joins of admissibility judgments
preserve Sen's α (`sup_senAlphaAt`, `sJoin_senAlphaAt`), and SEU judgments
satisfy WARP per supposition (`seu_warpAt`), so every E-admissibility
judgment satisfies α (`eAdm_senAlphaAt`). But joins destroy β: a single
witness pattern — two acts jointly admissible from a submenu, exactly one
surviving to the larger menu — refutes β (`not_senBetaAt_of_witness`), and
the abstract β-corollary (`JoinClosed.exists_suspends_not_senBetaAt`) shows
that any join-closed class whose suspension of two members exhibits the
pattern contains a commensurating intermediary that violates β, hence WARP.
Dynamic rationality (commensurability) entails static WARP-violation. The
witness instantiation is `test/CAJTest/TwoPrior.lean`.
-/

namespace CAJ

namespace AdmissibilityJudgment

variable {ctx : DecisionContext}

/-! ## Joins preserve α -/

theorem sup_senAlphaAt {J K : AdmissibilityJudgment ctx} {e : ctx.Event}
    (hJ : J.SenAlphaAt e) (hK : K.SenAlphaAt e) : (J ⊔ K).SenAlphaAt e := by
  intro m m' hsub a ham' ha
  rw [sup_C] at ha ⊢
  rcases ha with ha | ha
  · exact Set.mem_union_left _ (hJ m m' hsub a ham' ha)
  · exact Set.mem_union_right _ (hK m m' hsub a ham' ha)

theorem sJoin_senAlphaAt {S : Set (AdmissibilityJudgment ctx)}
    (hS : S.Nonempty) {e : ctx.Event} (h : ∀ J ∈ S, J.SenAlphaAt e) :
    (sJoin S hS).SenAlphaAt e := by
  intro m m' hsub a ham' ha
  rw [sJoin_C, Set.mem_iUnion₂] at ha ⊢
  obtain ⟨J, hJ, haJ⟩ := ha
  exact ⟨J, hJ, h J hJ m m' hsub a ham' haJ⟩

/-! ## Joins destroy β -/

/-- A concrete β-violation witness: two acts jointly admissible from a
submenu of which exactly one survives to the larger menu. -/
theorem not_senBetaAt_of_witness {D : AdmissibilityJudgment ctx}
    {e : ctx.Event} {m m' : ctx.Menu} (hsub : m'.val ⊆ m.val)
    {a a' : ctx.Act} (ha : a ∈ D.C e m') (ha' : a' ∈ D.C e m')
    (ham : a ∉ D.C e m) (ha'm : a' ∈ D.C e m) : ¬ D.SenBetaAt e :=
  fun h => ham ((h m m' hsub a a' ha ha').mpr ha'm)

theorem not_warpAt_of_not_senBetaAt {D : AdmissibilityJudgment ctx}
    {e : ctx.Event} (h : ¬ D.SenBetaAt e) : ¬ D.WARPAt e :=
  fun hw => h hw.senBetaAt

/-- β-corollary (headline, abstract form): if the suspension of two members
of a join-closed class exhibits the β-violation witness pattern, the class
contains a commensurating intermediary between them that violates Sen's β —
commensurability within the class forces WARP-violation. -/
theorem JoinClosed.exists_suspends_not_senBetaAt
    {K : Set (AdmissibilityJudgment ctx)} (hK : JoinClosed K)
    {J J' : AdmissibilityJudgment ctx} (hJ : J ∈ K) (hJ' : J' ∈ K)
    {e : ctx.Event} {m m' : ctx.Menu} (hsub : m'.val ⊆ m.val)
    {a a' : ctx.Act}
    (ha : a ∈ (J ⊔ J').C e m') (ha' : a' ∈ (J ⊔ J').C e m')
    (ham : a ∉ (J ⊔ J').C e m) (ha'm : a' ∈ (J ⊔ J').C e m) :
    ∃ D ∈ K, Suspends D J J' ∧ ¬ D.SenBetaAt e :=
  ⟨J ⊔ J', hK.sup_mem hJ hJ', ⟨le_sup_left, le_sup_right⟩,
    not_senBetaAt_of_witness hsub ha ha' ham ha'm⟩

end AdmissibilityJudgment

namespace CredalContext

open AdmissibilityJudgment

variable {ctx : DecisionContext} (cc : CredalContext ctx)

/-- SEU judgments satisfy WARP at every supposition. -/
theorem seu_warpAt (p : Fap ctx.alg) (e : ctx.Event) :
    (cc.seu p).WARPAt e := by
  intro m m' a a' _ ham' ha'm _ haC ha'C
  rw [mem_seu_C] at haC ha'C ⊢
  exact ⟨ham', haC.2.1,
    fun b hb => le_trans (ha'C.2.2 b hb) (haC.2.2 a' ha'm)⟩

/-- SEU judgments satisfy WARP (uniform version). -/
theorem seu_warp (p : Fap ctx.alg) : (cc.seu p).WARP :=
  fun e => cc.seu_warpAt p e

/-- E-admissibility judgments satisfy Sen's α at every supposition: α is
preserved by the join. -/
theorem eAdm_senAlphaAt (P : Set (Fap ctx.alg)) (hP : P.Nonempty)
    (e : ctx.Event) : (cc.eAdm P hP).SenAlphaAt e := by
  refine sJoin_senAlphaAt _ fun J hJ => ?_
  obtain ⟨p, _, rfl⟩ := hJ
  exact (cc.seu_warpAt p e).senAlphaAt

/-- E-admissibility judgments satisfy Sen's α (uniform version). -/
theorem eAdm_senAlpha (P : Set (Fap ctx.alg)) (hP : P.Nonempty) :
    (cc.eAdm P hP).SenAlpha :=
  fun e => cc.eAdm_senAlphaAt P hP e

end CredalContext

end CAJ
