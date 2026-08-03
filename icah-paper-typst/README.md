# ICAH Typst Paper Project

Publication source for the Lean formalization of the Intermediate-Cardinality Arithmetic Hypothesis (ICAH): elementary substrata, real-closed subfields, elementary-chain direct limits, and cofinality at the continuum.

## Template choice

Baseline: [`unequivocal-ams`](https://typst.app/universe/package/unequivocal-ams/) because it is AMS-style, single-column, and aimed at mathematical papers.

Alternative templates to consider later:

- [`clean-math-paper`](https://typst.app/universe/package/clean-math-paper/) if you want a cleaner modern look with built-in math-paper metadata.
- [`theorion`](https://typst.app/universe/package/theorion/) if the paper becomes theorem-environment-heavy.
- `fine-lncs` only if targeting a Springer LNCS-style proceedings venue.

## Build

```bash
brew install typst # must provide Typst 0.14.2
make build
```

The Makefile pins and verifies Typst `0.14.2`, matching CI and release `v1.0.0`.

Output:

```text
build/icah-paper.pdf
```

## Structure

```text
main.typ
sections/
  01-introduction.typ
  02-background.typ
  03-formal-architecture.typ
  04-proved-results.typ
  05-axiom-inventory.typ
  06-related-work.typ
  07-neighboring-fields.typ
  08-conclusion.typ
src/
  macros.typ
notes/
  paper-positioning.md
  lean-to-paper-map.md
  agent-prompt.md
refs.bib
Makefile
```

## Writing strategy

Lead with the proved Lean content, not with the philosophical ambition.

Recommended headline result:

> `directLimit_card_eq_iSup`: the cardinality of a countable direct limit equals the supremum of its level cardinalities when that supremum is infinite, together with `directLimit_card_lt_continuum`, the König-based closure theorem below the continuum.

Recommended framing:

> A formalization study that separates general elementary-chain theorems, constant-chain witnesses in the top-level assembly results, a nonconstant cofinal family of real-closed subfields not yet proved elementary, explicit hypotheses, and Mathlib contribution targets.

## Release checks

1. Run `make build`, `make sorry-count`, and `make axiom-count` in the Lean repository.
2. Run `make build` here with Typst 0.14.2.
3. Confirm that the manuscript cites release tag `v1.0.0`.
4. Confirm that the top-level constant chains are never conflated with the nonconstant cofinal real-closed family.
