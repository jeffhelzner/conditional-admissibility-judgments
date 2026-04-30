/-
# Revealed Preference Examples

Examples accompanying `src/RevealedPreference.lean`. The theorems in the
core module are independent of these examples; the file's purpose is to
document particular `χ` for which the various predicates (`MenuClosure`,
`AxiomAlpha…`, `WARPAt`, `Representable`, …) hold or fail, and so to
illustrate the *findings* recorded in the module header.

Section labels below mirror §8 of `prompts/PLAN_FOR_REVEALED_PREFERENCE_ON_A.md`.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import RevealedPreference
import Examples

namespace ConditionalChoice

/-! ## §8.1 The `bool_example` revisited

`bool_example` from `test/Examples.lean` has

* `A = {const_true, const_false}`
* `M = {{const_false}, {const_true, const_false}}`

Note that `{const_true}` is *not* in `M`, so `MenuClosure` fails. This is
an instance of the design tension noted in §14 of the plan: in
`ConditionalJudgment`, `M` is simultaneously the set of menus the analyst
takes as observed *and* the domain on which `C` is defined. Sen-style
revealed-preference theorems require closure of `M` under singletons,
pairs, and triples drawn from `A`; `bool_example` does not provide this. -/

theorem bool_example_not_menuClosure : ¬ MenuClosure bool_example := by
  intro hM
  -- `singleton_mem` would require `{const_true} ∈ bool_example.M`.
  have htrue_in_A : (fun (_ : Bool) => true) ∈ bool_example.A :=
    Set.mem_insert _ _
  have hsing : ({fun (_ : Bool) => true} : Set (Bool → Bool)) ∈ bool_example.M :=
    hM.singleton_mem _ htrue_in_A
  -- But `bool_example.M = {{const_false}, {const_true, const_false}}`,
  -- and `{const_true}` is neither.
  rcases hsing with h1 | h2
  · -- `{const_true} = {const_false}` → contradiction by evaluating at any input.
    have : (fun (_ : Bool) => true) = (fun (_ : Bool) => false) := by
      have := Set.eq_of_mem_singleton (h1 ▸ Set.mem_singleton (fun (_ : Bool) => true))
      exact this
    have := congrArg (fun f => f true) this
    simp at this
  · -- `{const_true} = {const_true, const_false}` is also impossible.
    rw [Set.mem_singleton_iff] at h2
    have hfalse_mem : (fun (_ : Bool) => false) ∈
        ({fun (_ : Bool) => true} : Set (Bool → Bool)) := by
      rw [h2]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [Set.mem_singleton_iff] at hfalse_mem
    have := congrArg (fun f => f true) hfalse_mem
    simp at this

/-! ## §8.3 / §8.4 Notes on Fin 3 examples

Two further examples are described in the plan:

* §8.3, the Condorcet cycle counterexample: a `χ` on three alternatives
  with `C({a, b}) = {a}`, `C({b, c}) = {b}`, `C({a, c}) = {c}`. With the
  *triple* menu chosen to keep `α` intact (`C({a, b, c}) = {a, b, c}`),
  the relation `R_e` is in fact fully transitive (the triple menu
  witnesses every pair), so this is not a counterexample to "α + γ →
  Trans `R_e`". The relation is non-transitive only when the triple
  menu is *omitted* from `χ.M`, but then `MenuClosure` itself fails.
  This subtlety is recorded here as a correction to the original plan.

* §8.4, the "representable-but-`R_e`-not-a-weak-order" example, which
  serves jointly as a counterexample to both unprovable implications
  recorded in `RevealedPreference.lean`. Take `A = {a, a', b}` and
  `χ.C` defined on all nonempty submenus by

  * `C({a, a'}) = {a, a'}`,
  * `C({a, b}) = {a}`,
  * `C({a', b}) = {b}`,
  * `C({a, a', b}) = {a}`.

  A direct calculation shows: α and γ both hold, `χ.C e m =
  maxSet χ e m` for every `m` (i.e., `Representable` holds), yet β
  fails for `(m, m') = ({a, a', b}, {a, a'})` — both `a, a' ∈ C(m')`
  yet `a ∈ C(m)` while `a' ∉ C(m)` — and consequently WARP fails.
  In particular `R_e` is not transitive: `a' R_e a` (witness `{a, a'}`)
  and `a R_e b` (witness `{a, b}`) hold but `a' R_e b` fails (no
  menu contains both with `a'` admissible).

  Under the new equivalence

  ```
  warpAt_iff_representable_and_transitive :
    WARPAt χ e ↔ Representable χ e ∧ TransitiveOnAlt χ e
  ```

  this single example demonstrates that `Representable` and
  `TransitiveOnAlt` are independent components of WARP: dropping
  transitivity of `R_e` while retaining representability is
  consistent (and exactly what this example does).

A full Lean realization of this example would require constructing a
concrete `ConditionalJudgment` over `Unit` × `Fin 3` (or similar) and
checking each property by exhaustive case analysis. Given the new
equivalence theorem, such a verification reduces to: build `χ`, prove
`MenuClosure χ`, prove `Representable χ e`, prove a single direct
WARP violation (or `¬ TransitiveOnAlt χ e`), and conclude the other
via the equivalence. This is left as a follow-up module. -/

end ConditionalChoice
