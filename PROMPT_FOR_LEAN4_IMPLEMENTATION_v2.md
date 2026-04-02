# Formalizing Conditional Judgments of Admissibility in Lean4

## 1. Goal

Produce a type-checked Lean4 formalization of **conditional judgments of admissibility** and their transformations, backed by Mathlib4. Deliver:

1. Core structures: `SetAlgebra`, `ConditionalJudgment`, `CJTransformation`
2. Probability and utility infrastructure: `Fap`, `expected_utility`, `HasEURepresentation`
3. Categorical structure: composition and identity for `CJTransformation`
4. A concrete `Bool` example with explicit verification lemmas
5. A representation theorem for the `Bool` example

### Representation target

Find conditions on a conditional choice function `C` equivalent to the existence of a finitely-additive probability `p` on `E` and a cardinal utility `u : K → ℝ` such that for all `e ∈ E` and `m ∈ M`:

```
C e m = { a ∈ m | expected utility of a given e is maximal among elements of m }
```

Encode this as the named predicate `HasEURepresentation`. The full proof for arbitrary spaces is deferred; the first deliverable proves it for one concrete finite example.

## 2. Interpretive Context

This formalization is motivated by philosophical questions about rational choice under uncertainty, not by purely mathematical considerations. The central object `C e m` is to be read as: "the alternatives in menu `m` that a decision maker would regard as *admissible* if they knew only that the true state of the world lies in `e`." The framework is designed to support normative investigation — what *should* a rational agent choose given their epistemic situation? — in the tradition of Anscombe–Aumann and related work in the foundations of decision theory. While the abstract formalism admits other interpretations, documentation and naming choices should reflect this intended reading. In particular: "epistemic state" (not "event" or "conditioning set"), "admissible" (not "optimal" or "selected"), and "judgment" (not "choice rule" or "selection function") are deliberate terminological choices that reflect the philosophical framing.

## 3. Terminology

- **State space** `X`: the set of possible states of the world.
- **Consequence space** `K`: the set of possible outcomes/consequences.
- **Epistemic state** `e ∈ E`: a subset of `X` representing what the decision maker considers possible. `C e m` gives the alternatives judged admissible given that the true state lies in `e`. These are informational/epistemic conditions, not probabilistic events.
- **Alternative** `a : X → K`: a function mapping states to consequences (an "act").
- **Menu** `m ∈ M`: a set of alternatives available for choice.
- **Conditional choice function** `C`: maps an epistemic state and a menu to the set of admissible alternatives.
- **Set algebra** `E`: a Boolean algebra of subsets of `X` representing the decision maker's possible epistemic conditions. Closure under Boolean operations reflects that these conditions are closed under standard logical operations.

## 4. Toolchain & Dependencies

- **Lean4**: use the Lean toolchain version matching the targeted Mathlib4 revision. Include a `lean-toolchain` file. Check the Mathlib4 repository's `lean-toolchain` for the compatible version.
- **Mathlib4**: required dependency. Expected imports include (but are not limited to):
  - `Mathlib.Data.Set.Basic`
  - `Mathlib.Data.Set.Function`
  - `Mathlib.Data.Finset.Basic`
  - `Mathlib.Tactic`
- **Build system**: `lake`. Include `lakefile.lean` and `lean-toolchain` in the repository root.

## 5. Project Layout

```
lakefile.lean
lean-toolchain
src/
  SetAlgebra.lean            -- SetAlgebra structure and Membership instance
  ConditionalJudgment.lean   -- ConditionalJudgment, Fap, expected_utility, HasEURepresentation
  Transformation.lean        -- CJTransformation and derived lemmas
  Category.lean              -- composition and identity for CJTransformation
test/
  Examples.lean              -- Bool example, transformation example, representation check
README.md                    -- build instructions, project overview
```

## 6. Specification

All definitions live in the `ConditionalChoice` namespace. Use one canonical encoding only — do not present alternatives.

### 6.1 SetAlgebra (`src/SetAlgebra.lean`)

A Boolean algebra of subsets of `X`, bundled with its closure properties.

```lean
universe u

/-- A Boolean algebra of subsets of a type, representing the possible
    epistemic states available to a decision maker. -/
structure SetAlgebra (X : Type u) where
  carrier : Set (Set X)
  univ_mem : Set.univ ∈ carrier
  union_mem : ∀ {s t}, s ∈ carrier → t ∈ carrier → s ∪ t ∈ carrier
  inter_mem : ∀ {s t}, s ∈ carrier → t ∈ carrier → s ∩ t ∈ carrier
  compl_mem : ∀ {s}, s ∈ carrier → Set.compl s ∈ carrier
```

Required derived definitions and lemmas:

- `Membership` instance: `instance : Membership (Set X) (SetAlgebra X)` so that `s ∈ E` desugars to `s ∈ E.carrier`.
- `SetAlgebra.empty_mem`: `∅ ∈ E` (derived from `univ_mem` and `compl_mem`).
- `SetAlgebra.nonempty`: `E.carrier.Nonempty` (derived from `univ_mem`).

### 6.2 ConditionalJudgment (`src/ConditionalJudgment.lean`)

-- Using Option A: Finite X

```lean
universe u v

/-- A conditional judgment of admissibility over state space X
    and consequence space K. -/
structure ConditionalJudgment (X : Type u) (K : Type v) where
  /-- Nonemptiness of the state space. -/
  X_nonempty : Nonempty X
  /-- Nonemptiness of the consequence space. -/
  K_nonempty : Nonempty K
  /-- The Boolean algebra of epistemic states (subsets of X the decision
      maker may regard as the set of possible states of the world). -/
  E : SetAlgebra X
  /-- The set of available alternatives (acts mapping states to consequences). -/
  A : Set (X → K)
  /-- The set of available menus (sets of alternatives). -/
  M : Set (Set (X → K))
  /-- The conditional choice function: C e m is the set of alternatives in m
      that the decision maker judges admissible given epistemic state e. -/
  C : Set X → Set (X → K) → Set (X → K)
  /-- The set of alternatives is nonempty. -/
  A_nonempty : A.Nonempty
  /-- The set of menus is nonempty. -/
  M_nonempty : M.Nonempty
  /-- Every menu is nonempty. -/
  M_elements_nonempty : ∀ m ∈ M, Set.Nonempty m
  /-- The choice from any valid epistemic state and menu is itself a valid menu. -/
  C_in_M : ∀ e m, e ∈ E → m ∈ M → C e m ∈ M
  /-- The choice from any valid epistemic state and menu is a subset of that menu. -/
  C_subset_menu : ∀ e m, e ∈ E → m ∈ M → C e m ⊆ m
```

Note: `C` is intentionally raw — it accepts any `Set X` and `Set (X → K)`. Well-formedness is enforced by `C_in_M` and `C_subset_menu`, which only apply when their hypotheses (`e ∈ E`, `m ∈ M`) hold. This avoids subtype gymnastics.

Note: `A_nonempty` requires the set of alternatives to be nonempty. It does *not* require each individual alternative to have nonempty image. If element-wise nonemptiness is needed later, state it explicitly.

**Finite-state restriction**: for the first pass, require `Fintype X` (Option A). Use `Fintype` (not `Finite`) because `expected_utility` needs a computable enumeration to sum over elements. `Fintype X` is a typeclass parameter on `expected_utility` and `HasEURepresentation`, not a field of `ConditionalJudgment` — the structure itself remains general. Place this comment at the top of `src/ConditionalJudgment.lean`:

```lean
-- Using Option A (Fintype X): expected utility is a finite sum over X.
```

### 6.3 Finitely-Additive Probability (`src/ConditionalJudgment.lean`)

```lean
/-- A finitely-additive probability measure on a set algebra. -/
structure Fap {X : Type u} (E : SetAlgebra X) where
  p : { s // s ∈ E.carrier } → ℝ
  nonneg : ∀ s, 0 ≤ p s
  p_univ : p ⟨Set.univ, E.univ_mem⟩ = 1
  additive : ∀ (s t : { s // s ∈ E.carrier }),
    Disjoint s.val t.val →
    p ⟨s.val ∪ t.val, E.union_mem s.prop t.prop⟩ = p s + p t
```

Note: `Fap` takes a bundled `SetAlgebra`, so the proof obligation in `additive` (`s.val ∪ t.val ∈ E.carrier`) is discharged by `E.union_mem s.prop t.prop` directly.

### 6.4 Expected Utility (`src/ConditionalJudgment.lean`)

```lean
/-- Expected utility of alternative a given epistemic state e with p(e) ≠ 0.
    Under Option A (Finite X), computed as a finite sum over the range of a:
    EU(p,u,e,a) = (1 / p(e)) * Σ_{k ∈ range(a)} u(k) * p(a⁻¹'{k} ∩ e). -/
noncomputable def expected_utility {X : Type u} {K : Type v} [Fintype X]
    {E : SetAlgebra X} (p : Fap E) (u : K → ℝ)
    (e : { s // s ∈ E.carrier }) (he : p.p e ≠ 0)
    (a : X → K)
    -- Proof that each level set intersected with e is in E:
    (hlevel : ∀ k, a ⁻¹' {k} ∩ e.val ∈ E.carrier) : ℝ := sorry
```

The implementer should choose the most natural finite summation form. The level-set approach (summing over `k ∈ (Set.range a).toFinset`) is preferred because it directly mirrors the mathematical definition and only requires level-set membership in E (not singleton membership).

For the `Bool` example with `E` = full powerset, `hlevel` is trivially satisfied (every subset is in E).

Provide at least one basic lemma:

- `expected_utility_const`: the expected utility of a constant alternative `fun _ => k` equals `u k` (when `p.p e ≠ 0`).

### 6.5 HasEURepresentation (`src/ConditionalJudgment.lean`)

```lean
/-- A conditional judgment has an expected-utility representation if there exist
    a finitely-additive probability and a utility function such that the choice
    function selects exactly the EU-maximizing alternatives from each menu,
    conditional on each non-null epistemic state. -/
def HasEURepresentation {X : Type u} {K : Type v} [Fintype X]
    (χ : ConditionalJudgment X K) : Prop :=
  ∃ (p : Fap χ.E) (u : K → ℝ),
    ∀ (e : { s // s ∈ χ.E.carrier }),
      p.p e ≠ 0 →
      ∀ m ∈ χ.M,
        ∀ a ∈ χ.A,
          (∀ k, a ⁻¹' {k} ∩ e.val ∈ χ.E.carrier) →
          (a ∈ χ.C e.val m ↔
            a ∈ m ∧ ∀ a' ∈ m, (∀ k, a' ⁻¹' {k} ∩ e.val ∈ χ.E.carrier) →
              expected_utility p u e ‹_› a' ‹_› ≤ expected_utility p u e ‹_› a ‹_›)
```

The exact Lean syntax will require adjustment by the implementer — the intent is:

> There exist `p` and `u` such that for every non-null epistemic state `e` and every menu `m`, an alternative is chosen iff it is in the menu and has maximal expected utility among menu elements.

The implementer should find the cleanest formulation that captures this intent and type-checks. The above is a guide, not a literal transcription.

### 6.6 CJTransformation (`src/Transformation.lean`)

```lean
universe u v u' v'

/-- A transformation (morphism) between two conditional judgments.
    Viewed categorically, each ConditionalJudgment is an object and
    CJTransformation is a morphism. The map f : X → X' pulls back epistemic
    states (coarse-to-fine); the map g : K' → K pushes forward consequences. -/
structure CJTransformation
    {X : Type u} {K : Type v} {X' : Type u'} {K' : Type v'}
    (χ : ConditionalJudgment X K) (χ' : ConditionalJudgment X' K') where
  /-- Map on state spaces. -/
  f : X → X'
  /-- Map on consequence spaces (contravariant direction). -/
  g : K' → K
  /-- Every epistemic state of χ arises as the preimage of some
      epistemic state of χ'. Weaker than global surjectivity of f. -/
  f_preimage_surjective_on_E :
    ∀ e, e ∈ χ.E → ∃ e', e' ∈ χ'.E ∧ f ⁻¹' e' = e
  /-- Preimages of χ'-epistemic states lie in χ's set algebra. -/
  preimage_preserves_E :
    ∀ e', e' ∈ χ'.E → f ⁻¹' e' ∈ χ.E
  /-- Composing with g and f maps χ'-alternatives into χ-alternatives. -/
  alternatives_closed :
    ∀ a' ∈ χ'.A, (g ∘ a' ∘ f) ∈ χ.A
  /-- Transforming a χ'-menu produces a χ-menu. -/
  menus_closed :
    ∀ m' ∈ χ'.M, Set.image (fun b' => g ∘ b' ∘ f) m' ∈ χ.M
  /-- Chosen alternatives transform to chosen alternatives. -/
  choice_preserved :
    ∀ e', e' ∈ χ'.E →
    ∀ m' ∈ χ'.M →
    ∀ a', a' ∈ χ'.C e' m' →
      (g ∘ a' ∘ f) ∈ χ.C (f ⁻¹' e') (Set.image (fun b' => g ∘ b' ∘ f) m')
```

Use `Set.image` for transformed menus. The lambda variable in `Set.image` should use a distinct name from the quantified `a'` for readability.

### 6.7 Helper Definitions (`src/ConditionalJudgment.lean`)

```lean
@[simp] def preimageSet (f : X → X') (s : Set X') : Set X := f ⁻¹' s

@[simp] def composeAlternative (g : K' → K) (a' : X' → K') (f : X → X') : X → K :=
  g ∘ a' ∘ f

@[simp] def transformMenu (g : K' → K) (f : X → X') (m' : Set (X' → K')) : Set (X → K) :=
  Set.image (fun b' => g ∘ b' ∘ f) m'
```

### 6.8 Required Derived Lemmas

From `ConditionalJudgment`:

- `ConditionalJudgment.choice_subset_menu` — wrapper restating `C_subset_menu`
- `ConditionalJudgment.choice_mem_menu` — wrapper restating `C_in_M`

From `CJTransformation`:

- `CJTransformation.transform_alternative_mem` — derived from `alternatives_closed`
- `CJTransformation.transform_menu_mem` — derived from `menus_closed`
- `CJTransformation.transform_choice_mem` — derived from `choice_preserved`

### 6.9 Composition and Identity (`src/Category.lean`)

**Required, but implement last** — after all other files type-check.

- `CJTransformation.id (χ : ConditionalJudgment X K) : CJTransformation χ χ`

  Identity: `f := id`, `g := id`. All fields follow from `Set.preimage_id`, `Function.comp_id`, `Function.id_comp`, etc.

- `CJTransformation.comp : CJTransformation χ χ' → CJTransformation χ' χ'' → CJTransformation χ χ''`

  Composition: `f := f' ∘ f`, `g := g ∘ g'` (note the contravariant direction of `g`). Fields compose by chaining the corresponding fields of the two inputs. The `menus_closed` and `choice_preserved` proofs use `Set.image_image` for the composed image.

If these proofs reveal that any field's statement does not compose cleanly, **report the issue** rather than silently modifying structures. (Composition has been verified to work on paper for this design.)

## 7. Required Examples (`test/Examples.lean`)

All checks must be explicit `example` or `theorem` lemmas. Do not rely on file-level type-checking alone.

### 7.1 Bool Example

Construct `bool_example : ConditionalJudgment Bool Bool`:

- `E`: the full powerset of `Bool` (as a `SetAlgebra Bool` — all 4 subsets).
- `A`: at least `{fun _ => true, fun _ => false}`.
- `M`: at least `{{fun _ => false}, {fun _ => true, fun _ => false}}`.
- `C e m := {fun _ => false}` for all `e`, `m` (constant rule).

Note: the `Bool` example will require `DecidableEq (Bool → Bool)` for set membership/equality proofs. This is derivable (e.g., `inferInstance` or via `Fintype` + classical reasoning) but may need an explicit instance or `classical` tactic.

Required checks:

```lean
example : bool_example.C_in_M := ...
example : bool_example.C_subset_menu := ...
```

### 7.2 Transformation Example

Construct `bool_transformation : CJTransformation bool_example bool_example` using either:

- Identity: `f := id`, `g := id` (simplest, acceptable).
- Nontrivial: `f := Bool.not`, `g := id` (preferred if the example satisfies all fields).

Required check:

```lean
example : bool_transformation.choice_preserved := ...
```

### 7.3 Representation Example

Construct witnesses `p : Fap bool_E` and `u : Bool → ℝ` and prove:

```lean
theorem bool_representation : HasEURepresentation bool_example := ...
```

Suggested witnesses:

- `p({true}) = 1/2`, `p({false}) = 1/2` (uniform).
- `u false = 0`, `u true = 1`.

Verify that the constant rule `C e m = {fun _ => false}` matches the EU-maximization criterion for these witnesses. (Under uniform probability: `EU(const_false) = 0`, `EU(const_true) = 1`, so `const_true` has higher EU. This means the example `C` does *not* select EU-maximizers under these witnesses — the implementer should choose witnesses and/or a `C` rule that make the representation hold. For example, reverse the utility: `u false = 1`, `u true = 0`.)

## 8. Implementation Order

Work in this order. Do not let later steps block earlier ones. If type-class or coercion issues arise, prioritize getting each file compiling before adding polish.

1. `src/SetAlgebra.lean` — structure, `Membership` instance, `empty_mem`, `nonempty`.
2. `src/ConditionalJudgment.lean` — structure, `Fap`, `expected_utility`, `HasEURepresentation`, helpers, derived lemmas.
3. `src/Transformation.lean` — `CJTransformation` structure and derived lemmas.
4. `test/Examples.lean` — `bool_example`, `bool_transformation`, `bool_representation`, all explicit checks.
5. `src/Category.lean` — `id` and `comp` for `CJTransformation`.
6. `README.md` and `lakefile.lean`.

## 9. Naming Conventions

| Name | Kind |
|------|------|
| `SetAlgebra` | structure |
| `ConditionalJudgment` | structure |
| `CJTransformation` | structure |
| `Fap` | structure |
| `HasEURepresentation` | def (Prop) |
| `expected_utility` | def |
| `composeAlternative` | def |
| `transformMenu` | def |
| `preimageSet` | def |

Namespace: `ConditionalChoice`.

Use these names unless there is a strong Lean-specific reason not to.

## 10. Design Rationale

*This section explains design choices. It is informational — the spec in §6 is authoritative.*

**`SetAlgebra` is a custom bundle** rather than Mathlib's `MeasurableSpace` because we want *finite* additivity, not σ-additivity. The Boolean algebra of epistemic states has no countable closure requirements.

**`C` is raw.** It accepts any `Set X` and `Set (X → K)`, not just members of `E` and `M`. Well-formedness is enforced by `C_in_M` and `C_subset_menu`, which apply only when their hypotheses hold.

**`f_preimage_surjective_on_E`** uses the weaker "every χ-state arises as a preimage" rather than global `Surjective f`. This suffices for transporting epistemic states in proofs. Global surjectivity is needed only for fibre witnesses in categorical/isomorphism results and can be added as a separate field when needed.

**`preimage_preserves_E` is on `CJTransformation`**, not on `SetAlgebra`. This keeps the set algebra as a self-contained Boolean algebra while allowing transformations to specify the necessary compatibility.

**`HasEURepresentation` is a named predicate** rather than an inline formula. This supports composable vocabulary: refinements like `HasUniqueEURepresentation` or statements like "transformations preserve representability" become clean one-line propositions.

**`Fap.additive` references `E.union_mem`** directly because `Fap` takes a bundled `SetAlgebra`, not a raw `Set (Set X)`. The proof obligation in the additive field is discharged by the bundle's closure property.

**Option A (`Fintype X`)** avoids measure-theoretic integration. Expected utility is a finite sum. `Fintype` (rather than `Finite`) is used because the sum requires a computable enumeration.

**Composition and identity** validate that the morphism design is sound before further development. They are structurally straightforward:
- Composition: `f ↦ f' ∘ f`, `g ↦ g ∘ g'` (contravariant), field proofs chain via `Set.preimage_comp`, `Set.image_image`, and associativity of function composition.
- Identity: `f := id`, `g := id`, fields follow from `Set.preimage_id`, `Function.comp_id`, `Function.id_comp`.

## 11. Future Directions

Once the core framework is in place:

- **Preference extraction**: define a derived weak preference `≥` on `K` via constant alternatives in menus (`k ≥ k'` iff the constant-`k` alternative is chosen over constant-`k'` under `Set.univ`).
- **Cardinal utility**: axioms on `C` ensuring the derived `≥` is a weak order; mixture-space closure on `K` to support vNM-style representation.
- **Full representation theorem**: connect to `Fap` and `u` for arbitrary (non-finite) spaces, along the lines of Anscombe–Aumann.
- **E-admissibility and credal sets**: the single-prior `HasEURepresentation` is the degenerate case of a richer target. Define a credal set `P : Set (Fap χ.E)` (a convex set of finitely-additive probabilities) and a corresponding predicate `HasEAdmissibilityRepresentation`: an alternative `a` is admissible in menu `m` given epistemic state `e` iff it is Bayes-optimal (EU-maximizing) with respect to *some* `p ∈ P` and `u`. This generalizes the framework to imprecise probabilities and connects directly to Levi's E-admissibility and the Seidenfeld–Schervish–Kadane theory of coherent choice. The current design — set-valued `C`, admissibility as primitive, no built-in completeness assumption — is specifically intended to support this generalization.
- **Categorical development**: functoriality, natural transformations, the subcategory of representable judgments (under both single-prior and credal-set representations).

## 12. Appendix: Optional Extensions

Not required in the first deliverable.

- `A_pointwise_update_closed`: pointwise modification of alternatives remains in `A`.
- `M_contains_finite_menus`: `M` contains all finite subsets of `A` (use `Finset.toSet`).
- Mixtures on `K`: `mix : K → K → ℚ → K` with symmetry and closure.
- `choice_preserved_bijective`: bijective correspondence of choices when `f`, `g` are bijections.
- `choice_preserved_surjective_on_choices`: every χ-choice arises as a transform of some χ'-choice.
- Linearity of `expected_utility` over mixtures.
- `expected_utility_const` (if not included in the main deliverable).

## 13. Acceptance Criteria

The implementation is complete when:

- [ ] All `.lean` files type-check without errors (`lake build` succeeds).
- [ ] Structures match §6 (field names, types, signatures).
- [ ] `test/Examples.lean` contains all `example`/`theorem` lemmas from §7.
- [ ] `src/Category.lean` contains `CJTransformation.id` and `CJTransformation.comp`.
- [ ] `README.md` documents project layout, dependencies, and build commands (`lake update`, `lake build`).
- [ ] `lakefile.lean` declares the Mathlib4 dependency with a `lean-toolchain` file.
- [ ] Brief docstrings above each structure and nontrivial lemma.
