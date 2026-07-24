import CAJ.SetAlgebra

/-!
# Decision contexts

v1 fixes a single decision context: a state space `State` (the serious
possibilities consistent with the background corpus `K`, which is thereby
implicit), an act type `Act`, a set algebra `alg` of suppositions, and a
collection `Menus` of nonempty menus of acts. Only the admissibility
judgment (choice function) varies across the theory; heterogeneous contexts
are deferred to v2.
-/

namespace CAJ

universe u v

/-- A fixed decision context `(X, K, E, A, M)`. `State` plays the role of the
possibility space determined by the corpus `K`; `alg` is the algebra `E` of
suppositions; `Act` is the act space `A`; `Menus` is the menu collection `M`.
Every menu is nonempty and at least one menu exists. -/
structure DecisionContext where
  /-- The state space `X` (serious possibilities given the corpus `K`). -/
  State : Type u
  /-- The act space `A`. -/
  Act : Type v
  /-- The algebra `E` of suppositions. -/
  alg : SetAlgebra State
  /-- The collection `M` of available menus. -/
  Menus : Set (Set Act)
  /-- Every menu is nonempty. -/
  menus_nonempty : ∀ ⦃m⦄, m ∈ Menus → m.Nonempty
  /-- At least one menu is available. -/
  menus_inhabited : Menus.Nonempty

namespace DecisionContext

variable (ctx : DecisionContext.{u, v})

/-- A supposition: a member of the algebra `E`. -/
abbrev Event : Type u := {e : Set ctx.State // e ∈ ctx.alg}

/-- A menu: a member of the collection `M`. -/
abbrev Menu : Type v := {m : Set ctx.Act // m ∈ ctx.Menus}

theorem menu_nonempty (m : ctx.Menu) : m.val.Nonempty :=
  ctx.menus_nonempty m.2

/-- The vacuous supposition `univ` (supposing nothing beyond the corpus). -/
def topEvent : ctx.Event := ⟨Set.univ, ctx.alg.univ_mem⟩

instance : Nonempty ctx.Event :=
  ⟨ctx.topEvent⟩

instance : Nonempty ctx.Menu :=
  ⟨⟨ctx.menus_inhabited.choose, ctx.menus_inhabited.choose_spec⟩⟩

end DecisionContext

end CAJ
