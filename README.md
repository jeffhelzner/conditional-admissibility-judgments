# Conditional Admissibility Judgments

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
src/
  SetAlgebra.lean             -- SetAlgebra structure and Membership instance
  ConditionalJudgment.lean    -- ConditionalJudgment, Fap, expected_utility, HasEURepresentation
  Transformation.lean         -- CJTransformation and derived lemmas
  Category.lean               -- Composition and identity for CJTransformation
test/
  Examples.lean               -- Bool example, transformation example, representation theorem
reports/
  _quarto.yml                 -- Quarto project configuration
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

## Reports

The `reports/` directory contains Quarto-based technical reports documenting the formalization. To render a report:

```bash
cd reports
quarto render 01-foundations-overview.qmd
```

Requires [Quarto](https://quarto.org/) to be installed.
