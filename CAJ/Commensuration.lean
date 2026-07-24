import CAJ.Join
import Mathlib.Order.Closure
import Mathlib.Logic.Relation

/-!
# Commensuration: suspension, closure, and the zig-zag interface

Levi vocabulary, relativized to a class `K` of admissibility judgments over
the fixed context:

* `Suspends D C C'` — the strong condition: `D` suspends the issue between
  `C` and `C'`, i.e. `C ≤ D` and `C' ≤ D` pointwise.
* `FairHearing D C C'` — the weak condition: at every supposition and menu
  where `C` (resp. `C'`) chooses anything, `D`'s choice set meets it.
* `Commensurable K C C'` — the change `C ⤳ C'` is commensurable *within `K`*:
  some `D ∈ K` suspends between them (factorizability through a
  commensurating intermediary drawn from `K`).
* `suspension C C'` — the canonical commensurating intermediary, the join.

## M2: commensuration closure

`commensurationClosure` maps a class `K` to the class of joins of nonempty
subsets of `K`. It is proved to be a `ClosureOperator` on `Set J`,
*parametric* in the base class; its closed classes are exactly the
`JoinClosed` ones, and it is the **least** join-closed extension
(`commensurationClosure_le` — minimality is free from the universal
property, which is M3's minimality). The instance `cc(K_SEU) = K_Eadm` is
Phase 4.

## The zig-zag interface (𝓛/𝓡)

Change of judgment is external. A *contraction* step (`𝓛`) moves pointwise
`⊆`-up toward a weaker judgment; an *expansion* step (`𝓡`) is the reverse.
`ZigZagIn K` is the reflexive-transitive closure of single 𝓛/𝓡 steps
through members of `K` (the thin zig-zag category on `K`). Within a
join-closed class, every zig-zag reduces to a diameter-≤ 2 cospan through
the join (`zigZagIn_iff_commensurable`) — the generic skeleton of the
cospan normal form; Phase 4 instantiates it to the credal class.
-/

namespace CAJ

namespace AdmissibilityJudgment

variable {ctx : DecisionContext}

/-! ## Suspension and fair hearing -/

/-- `D` suspends the issue between `C` and `C'` (strong condition):
`D` deems admissible everything either judgment does. -/
def Suspends (D C C' : AdmissibilityJudgment ctx) : Prop :=
  C ≤ D ∧ C' ≤ D

/-- `D` gives a fair hearing to `C` and `C'` (weak condition): wherever
either judgment chooses anything, `D`'s choice set meets its choice set. -/
def FairHearing (D C C' : AdmissibilityJudgment ctx) : Prop :=
  (∀ e m, (C.C e m).Nonempty → (D.C e m ∩ C.C e m).Nonempty) ∧
  (∀ e m, (C'.C e m).Nonempty → (D.C e m ∩ C'.C e m).Nonempty)

/-- Suspension is stronger than fair hearing. -/
theorem Suspends.fairHearing {D C C' : AdmissibilityJudgment ctx}
    (h : Suspends D C C') : FairHearing D C C' :=
  ⟨fun e m ⟨a, ha⟩ => ⟨a, h.1 e m ha, ha⟩,
   fun e m ⟨a, ha⟩ => ⟨a, h.2 e m ha, ha⟩⟩

/-- The change `C ⤳ C'` is commensurable within the class `K`: some
member of `K` suspends the issue between `C` and `C'`. -/
def Commensurable (K : Set (AdmissibilityJudgment ctx))
    (C C' : AdmissibilityJudgment ctx) : Prop :=
  ∃ D ∈ K, Suspends D C C'

/-- The weak variant: some member of `K` gives both judgments a fair
hearing. -/
def WeaklyCommensurable (K : Set (AdmissibilityJudgment ctx))
    (C C' : AdmissibilityJudgment ctx) : Prop :=
  ∃ D ∈ K, FairHearing D C C'

theorem Commensurable.weaklyCommensurable
    {K : Set (AdmissibilityJudgment ctx)} {C C' : AdmissibilityJudgment ctx}
    (h : Commensurable K C C') : WeaklyCommensurable K C C' :=
  let ⟨D, hD, hs⟩ := h
  ⟨D, hD, hs.fairHearing⟩

/-- The canonical commensurating intermediary: the join. -/
def suspension (C C' : AdmissibilityJudgment ctx) : AdmissibilityJudgment ctx :=
  C ⊔ C'

theorem suspends_suspension (C C' : AdmissibilityJudgment ctx) :
    Suspends (suspension C C') C C' :=
  ⟨le_sup_left, le_sup_right⟩

/-! ## M2: commensuration closure -/

/-- A class of judgments is join-closed: it contains the join of each of
its nonempty subsets. -/
def JoinClosed (K : Set (AdmissibilityJudgment ctx)) : Prop :=
  ∀ S (hS : S.Nonempty), S ⊆ K → sJoin S hS ∈ K

theorem JoinClosed.sup_mem {K : Set (AdmissibilityJudgment ctx)}
    (hK : JoinClosed K) {C D : AdmissibilityJudgment ctx}
    (hC : C ∈ K) (hD : D ∈ K) : C ⊔ D ∈ K := by
  have h := hK {C, D} ⟨C, Set.mem_insert C {D}⟩ (by
    rintro J (rfl | rfl) <;> assumption)
  rwa [sJoin_pair] at h

/-- Any two members of a join-closed class are commensurable within it:
the suspension (join) is the commensurating intermediary. Minimality of the
intermediary is free from the universal property of the join (M3). -/
theorem JoinClosed.commensurable {K : Set (AdmissibilityJudgment ctx)}
    (hK : JoinClosed K) {C C' : AdmissibilityJudgment ctx}
    (hC : C ∈ K) (hC' : C' ∈ K) : Commensurable K C C' :=
  ⟨suspension C C', hK.sup_mem hC hC', suspends_suspension C C'⟩

/-- M2 (headline, parametric form): the commensuration closure of a class
`K` — the class of joins of nonempty subsets of `K` — as a closure operator
on classes of judgments. -/
def commensurationClosure :
    ClosureOperator (Set (AdmissibilityJudgment ctx)) where
  toFun K := {J | ∃ S, ∃ hS : S.Nonempty, S ⊆ K ∧ J = sJoin S hS}
  monotone' _ _ h _ hJ := by
    obtain ⟨S, hS, hSK, hJeq⟩ := hJ
    exact ⟨S, hS, hSK.trans h, hJeq⟩
  le_closure' K J hJ :=
    ⟨{J}, Set.singleton_nonempty J, Set.singleton_subset_iff.mpr hJ,
      (sJoin_singleton J).symm⟩
  idempotent' K := by
    apply subset_antisymm
    · rintro J ⟨S', hS', hsub, rfl⟩
      have h' : ∀ J' ∈ S', ∃ S, ∃ hS : S.Nonempty, S ⊆ K ∧ J' = sJoin S hS :=
        fun J' hJ' => hsub hJ'
      choose! f hf hfsub hfeq using h'
      refine ⟨⋃ J' ∈ S', f J', ?_, ?_, ?_⟩
      · obtain ⟨J₀, hJ₀⟩ := hS'
        obtain ⟨J₁, hJ₁⟩ := hf J₀ hJ₀
        exact ⟨J₁, Set.mem_biUnion hJ₀ hJ₁⟩
      · exact Set.iUnion₂_subset fun J' hJ' => hfsub J' hJ'
      · refine le_antisymm (sJoin_le fun J' hJ' => ?_)
          (sJoin_le fun J hJ => ?_)
        · rw [hfeq J' hJ']
          exact sJoin_mono _ _ (Set.subset_biUnion_of_mem hJ')
        · simp only [Set.mem_iUnion] at hJ
          obtain ⟨J', hJ', hJmem⟩ := hJ
          calc J ≤ sJoin (f J') (hf J' hJ') := le_sJoin _ hJmem
            _ = J' := (hfeq J' hJ').symm
            _ ≤ _ := le_sJoin hS' hJ'
    · exact fun J hJ =>
        ⟨{J}, Set.singleton_nonempty J, Set.singleton_subset_iff.mpr hJ,
          (sJoin_singleton J).symm⟩

theorem mem_commensurationClosure {K : Set (AdmissibilityJudgment ctx)}
    {J : AdmissibilityJudgment ctx} :
    J ∈ commensurationClosure K ↔
      ∃ S, ∃ hS : S.Nonempty, S ⊆ K ∧ J = sJoin S hS :=
  Iff.rfl

/-- The commensuration closure of any class is join-closed. -/
theorem joinClosed_commensurationClosure
    (K : Set (AdmissibilityJudgment ctx)) :
    JoinClosed (commensurationClosure K) := by
  intro S hS hsub
  rw [← commensurationClosure.idempotent K]
  exact ⟨S, hS, hsub, rfl⟩

/-- Minimality (M3, free from the universal property): the commensuration
closure is contained in every join-closed extension of the base class. -/
theorem commensurationClosure_le {K L : Set (AdmissibilityJudgment ctx)}
    (hKL : K ⊆ L) (hL : JoinClosed L) : commensurationClosure K ⊆ L := by
  rintro J ⟨S, hS, hsub, rfl⟩
  exact hL S hS (hsub.trans hKL)

/-- The closed classes of the commensuration closure are exactly the
join-closed ones. -/
theorem isClosed_commensurationClosure_iff
    {K : Set (AdmissibilityJudgment ctx)} :
    commensurationClosure.IsClosed K ↔ JoinClosed K := by
  rw [commensurationClosure.isClosed_iff]
  constructor
  · intro h
    rw [← h]
    exact joinClosed_commensurationClosure K
  · intro h
    exact subset_antisymm (commensurationClosure_le subset_rfl h)
      (commensurationClosure.le_closure' K)

/-! ## The zig-zag interface (𝓛/𝓡) -/

/-- A contraction step (`𝓛`): moving pointwise up, toward the weaker
judgment. -/
def Contraction (C D : AdmissibilityJudgment ctx) : Prop := C ≤ D

/-- An expansion step (`𝓡`): moving pointwise down, toward the stronger
judgment. -/
def Expansion (C D : AdmissibilityJudgment ctx) : Prop := D ≤ C

/-- A single zig-zag step within the class `K`: a contraction or an
expansion between members of `K`. -/
def StepIn (K : Set (AdmissibilityJudgment ctx))
    (C D : AdmissibilityJudgment ctx) : Prop :=
  C ∈ K ∧ D ∈ K ∧ (Contraction C D ∨ Expansion C D)

/-- The zig-zag relation on `K`: the reflexive-transitive closure of
single 𝓛/𝓡 steps through members of `K`. This is the hom-existence
relation of the thin zig-zag category generated by contractions and
expansions on `K`. -/
def ZigZagIn (K : Set (AdmissibilityJudgment ctx)) :
    AdmissibilityJudgment ctx → AdmissibilityJudgment ctx → Prop :=
  Relation.ReflTransGen (StepIn K)

/-- Commensurability within `K` yields a two-step zig-zag through the
intermediary: a contraction up to `D`, then an expansion down to `C'`. -/
theorem Commensurable.zigZagIn {K : Set (AdmissibilityJudgment ctx)}
    {C C' : AdmissibilityJudgment ctx} (hC : C ∈ K) (hC' : C' ∈ K)
    (h : Commensurable K C C') : ZigZagIn K C C' := by
  obtain ⟨D, hD, hCD, hC'D⟩ := h
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single ⟨hC, hD, Or.inl hCD⟩)
    ⟨hD, hC', Or.inr hC'D⟩

/-- Cospan normal form (generic skeleton): within a join-closed class,
zig-zag connectedness coincides with commensurability, i.e. every zig-zag
reduces to a diameter-≤ 2 cospan through a join. -/
theorem zigZagIn_iff_commensurable {K : Set (AdmissibilityJudgment ctx)}
    (hK : JoinClosed K) {C C' : AdmissibilityJudgment ctx}
    (hC : C ∈ K) (hC' : C' ∈ K) :
    ZigZagIn K C C' ↔ Commensurable K C C' :=
  ⟨fun _ => hK.commensurable hC hC',
   fun h => h.zigZagIn hC hC'⟩

end AdmissibilityJudgment

end CAJ
