import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function

namespace ConditionalChoice

universe u

/-- A Boolean algebra of subsets of a type. The state space X encodes the
    agent's serious possibilities; each member of the algebra represents
    something the agent could learn. Closure under union, intersection,
    complement, and containing the universe ensures that the collection
    is closed under standard logical operations. -/
structure SetAlgebra (X : Type u) where
  carrier : Set (Set X)
  univ_mem : Set.univ ∈ carrier
  union_mem : ∀ {s t}, s ∈ carrier → t ∈ carrier → s ∪ t ∈ carrier
  inter_mem : ∀ {s t}, s ∈ carrier → t ∈ carrier → s ∩ t ∈ carrier
  compl_mem : ∀ {s}, s ∈ carrier → Set.compl s ∈ carrier

instance {X : Type u} : Membership (Set X) (SetAlgebra X) where
  mem E s := s ∈ E.carrier

@[simp]
theorem SetAlgebra.mem_def {X : Type u} {s : Set X} {E : SetAlgebra X} :
    s ∈ E ↔ s ∈ E.carrier :=
  Iff.rfl

/-- The empty set belongs to any set algebra (derived from `univ_mem` and `compl_mem`). -/
theorem SetAlgebra.empty_mem {X : Type u} (E : SetAlgebra X) : ∅ ∈ E := by
  have h : Set.compl Set.univ = (∅ : Set X) := Set.compl_univ
  rw [SetAlgebra.mem_def, ← h]
  exact E.compl_mem E.univ_mem

/-- The carrier of any set algebra is nonempty (it contains `Set.univ`). -/
theorem SetAlgebra.nonempty {X : Type u} (E : SetAlgebra X) : E.carrier.Nonempty :=
  ⟨Set.univ, E.univ_mem⟩

end ConditionalChoice
