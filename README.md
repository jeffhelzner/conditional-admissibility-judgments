# Conditional Admissibility Judgments

> **🚧 Work in Progress:** This project is in early stages of development. APIs, definitions, and proofs are subject to change without notice.

A Lean4 formalization of **conditional judgments of admissibility** and their transformations, backed by Mathlib4.

## Overview

This project formalizes a framework for reasoning about rational choice under uncertainty. The central object is a *conditional choice function* `C e m` — the set of alternatives in menu `m` that a decision maker judges *admissible* given epistemic state `e`. The formalization includes:

- **SetAlgebra**: A Boolean algebra of subsets representing possible epistemic states
- **ConditionalJudgment**: The core structure encoding conditional choice functions with well-formedness properties
- **Fap**: Finitely-additive probability measures on set algebras
- **expected\_utility**: Expected utility computation for finite state spaces
- **HasEURepresentation**: A predicate asserting the existence of a probability/utility pair rationalizing the choice function
- **CJTransformation**: Morphisms between conditional judgments (with categorical composition and identity)

## Project Layout

```
lakefile.lean                 -- Lake build configuration with Mathlib4 dependency
lean-toolchain                -- Lean toolchain version
.github/workflows/
  publish-reports.yml         -- GitHub Pages deployment for rendered Quarto reports
src/
  SetAlgebra.lean             -- SetAlgebra structure and Membership instance
  ConditionalJudgment.lean    -- ConditionalJudgment, Fap, expected_utility, HasEURepresentation
  Transformation.lean         -- CJTransformation and derived lemmas
  Category.lean               -- Composition and identity for CJTransformation
test/
  Examples.lean               -- Bool example, transformation example, representation theorem
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
