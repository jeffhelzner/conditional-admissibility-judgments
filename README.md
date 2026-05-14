# Conditional Admissibility Judgments

> **🚧 Work in Progress:** This project is in early stages of development. APIs, definitions, and proofs are subject to change without notice.

A Lean4 formalization of **conditional judgments of admissibility** and their transformations, backed by Mathlib4.

## Overview

This project formalizes a framework for reasoning about rational choice under uncertainty. The central object is a *conditional choice function* `C e m` — the set of alternatives in menu `m` that a decision maker judges *admissible* given epistemic state `e`. The formalization includes:

- **SetAlgebra**: A Boolean algebra of subsets representing possible epistemic states
- **ConditionalJudgment**: The core structure encoding conditional choice functions with well-formedness properties
- **RevealedPreference**: Sen-style revealed preference on alternatives, including WARP, α/β/γ, finite-subset closure, pairwise revealed preference, weak-order representability, primitive congruence axioms, quasi-transitivity, acyclicity, and path independence
- **ConstantActs** and **ConstActInvariance**: Consequence-level pullbacks of the alternative-level revealed-preference theory
- **EUImpliesWARP**: A bridge from expected-utility representation to WARP
- **MultiRepresentable**: Multi-relation rationalizability and cautious preference, including the path-independence reduction used for Levi-style admissibility
- **CJTransformation**: Morphisms between conditional judgments (with categorical composition and identity)
- **Conditionalization**: Bayesian conditioning represented as a transformation between conditional judgments

## Project Layout

```
lakefile.lean                 -- Lake build configuration with Mathlib4 dependency
lean-toolchain                -- Lean toolchain version
.github/workflows/
  publish-reports.yml         -- GitHub Pages deployment for rendered Quarto reports
src/
  SetAlgebra.lean             -- SetAlgebra structure and Membership instance
  ConditionalJudgment.lean    -- ConditionalJudgment core structure
  RevealedPreference.lean     -- Revealed preference, WARP, representability, pairwise preference, path independence
  ConstantActs.lean           -- Consequence-level pullback of revealed preference via constant acts
  ConstActInvariance.lean     -- Constant-act invariance and consequence-level event independence
  EUImpliesWARP.lean          -- Expected-utility representation implies WARP
  MultiRepresentable.lean     -- Multi-relation rationalizability and cautious preference
  StrictIndiffIncomp.lean     -- Strict preference, indifference, and incomparability partition
  EAdmissible.lean            -- E-admissibility layer
  CredalEU.lean               -- Credal expected-utility layer
  Conditionalization.lean     -- Conditionalization as a transformation
  Transformation.lean         -- CJTransformation and derived lemmas
  Category.lean               -- Composition and identity for CJTransformation
  Transformations/Examples.lean -- Concrete transformation examples
test/
  Examples.lean               -- Bool example, transformation example, representation theorem
  RevealedPreferenceExamples.lean -- Revealed-preference examples and closure checks
  Fin3RepNotWARP.lean         -- Finite representable-but-not-WARP example
  Levi2PriorExample.lean      -- Levi-style two-prior example
reports/
  _quarto.yml                 -- Quarto project configuration
  index.qmd                   -- Public landing page for the report series
  01-foundations-overview.qmd  -- Overview of the formalization foundations
  references.bib              -- Bibliography
```

## Dependencies

- **Lean4**: version specified in `lean-toolchain`
- **Mathlib4**: declared as a dependency in `lakefile.lean`

## Building

```bash
# Fetch dependencies (including Mathlib4)
lake update

# Build all files
lake build
```

The first build will take some time as it downloads and compiles Mathlib4.

## Namespace

All definitions live in the `ConditionalChoice` namespace.

## Current Revealed-Preference Status

The abstract revealed-preference layer now distinguishes three rationalizability strengths:

- `Representable χ e`: rationalization by the canonical joint-witness relation `RevealedPref χ e`.
- `PairwiseRepresentable χ e`: rationalization by the pairwise relation `PairwisePref χ e`, where `a R'_e a'` means `a ∈ χ.C e {a, a'}`.
- `WeakOrderRepresentable χ e`: rationalization by some existentially quantified weak order on alternatives.

Under `FiniteSubsetMenuClosure`, the classical Arrow-Sen theorem is formalized as `WARPAt χ e ↔ WeakOrderRepresentable χ e`. Under the weaker `MenuClosure`, the sharp canonical result remains `WARPAt χ e ↔ Representable χ e ∧ TransitiveOnAlt χ e`.

The module also includes primitive congruence axioms (`WCAAt`, `SCAAt`, `SARPAt`), the primitive chain axiom `ChoiceChainAxiomAt`, the hierarchy `TransitiveOnAlt → QuasiTransitiveOnAlt → AcyclicOnAlt`, and `PathIndependentAt`. The full Plott equivalence `PathIndependentAt ↔ α ∧ γ` is intentionally deferred until a stronger menu-domain closure predicate is added; the implemented API records the sound α-derived inclusion and a multi-representability reduction via `MultiMaxPathIndependent`.

## AI Assistance

This repository has benefited from the use of AI-assisted development tools, including GitHub Copilot and related large-language-model assistants, for tasks such as drafting documentation, exploring proof strategies, and developing Lean formalizations. All substantive mathematical and implementation decisions remain the responsibility of the repository author(s).

## Reports

The `reports/` directory is a Quarto website that publishes the project reports through GitHub Pages.

### Local development

To render the HTML site locally:

```bash
quarto render reports --to html
```

To preview the site locally with live reload:

```bash
quarto preview reports
```

To render only the foundations report as HTML:

```bash
quarto render reports/01-foundations-overview.qmd --to html
```

Rendered output is written to `reports/_output/`.

### Deployment

The repository includes a GitHub Actions workflow at `.github/workflows/publish-reports.yml`. On each push to `main` that changes the workflow or files under `reports/`, GitHub Actions:

1. installs Quarto,
2. renders the `reports/` site to HTML, and
3. deploys `reports/_output/` to GitHub Pages.

### Expected public URLs

Once GitHub Pages is enabled for this repository, the stable public URLs are:

- Landing page: `https://jeffhelzner.github.io/conditional-admissibility-judgments/`
- Foundations report: `https://jeffhelzner.github.io/conditional-admissibility-judgments/01-foundations-overview.html`

### Required GitHub setting

If GitHub Pages has not already been configured for this repository, open **Settings > Pages** and set **Build and deployment** to **GitHub Actions**.

### Adding future reports

1. Add a new `.qmd` file under `reports/`.
2. Add a link to it from `reports/index.qmd`.
3. Preview locally with `quarto preview reports`.
4. Push to `main` to publish the updated site.

The `reports/` directory contains Quarto-based technical reports documenting the formalization. The current foundations report can also be rendered directly:

```bash
quarto render reports/01-foundations-overview.qmd
```

Requires [Quarto](https://quarto.org/) to be installed.
