import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function

/-!
# Set algebras (finitely additive setting)

A `SetAlgebra X` is a Boolean algebra of subsets of a type `X`, bundled as a
carrier collection closed under complement and finite union (intersection is
derived). The state space `X` encodes the agent's serious possibilities given
the background corpus `K` (which is therefore implicit in v1); each member of
the algebra represents a proposition the agent can *suppose* in Levi's sense.
Conditioning on a member is suppositional reasoning within a fixed synchronic
state; genuine revision is an external change of judgment, not conditioning.

Only finite operations are required — this is the algebra underlying finitely
additive probability (`Fap`, Phase 3); no countable closure is assumed.
-/

namespace CAJ

universe u

/-- A Boolean algebra of subsets of `X`: contains `Set.univ` and is closed
under binary union and complement. Closure under intersection and the
membership of `∅` are derived. -/
structure SetAlgebra (X : Type u) where
  /-- The collection of member sets. -/
  carrier : Set (Set X)
  /-- The universe is a member. -/
  univ_mem : Set.univ ∈ carrier
  /-- Members are closed under binary union. -/
  union_mem : ∀ {s t}, s ∈ carrier → t ∈ carrier → s ∪ t ∈ carrier
  /-- Members are closed under complement. -/
  compl_mem : ∀ {s}, s ∈ carrier → sᶜ ∈ carrier

namespace SetAlgebra

variable {X : Type u}

instance : Membership (Set X) (SetAlgebra X) where
  mem E s := s ∈ E.carrier

@[simp]
theorem mem_def {s : Set X} {E : SetAlgebra X} : s ∈ E ↔ s ∈ E.carrier :=
  Iff.rfl

/-- The empty set belongs to any set algebra. -/
theorem empty_mem (E : SetAlgebra X) : (∅ : Set X) ∈ E := by
  have h := E.compl_mem E.univ_mem
  rwa [Set.compl_univ] at h

/-- Members are closed under binary intersection (via De Morgan). -/
theorem inter_mem (E : SetAlgebra X) {s t : Set X} (hs : s ∈ E) (ht : t ∈ E) :
    s ∩ t ∈ E := by
  have h := E.compl_mem (E.union_mem (E.compl_mem hs) (E.compl_mem ht))
  rwa [Set.compl_union, compl_compl, compl_compl] at h

end SetAlgebra

end CAJ
