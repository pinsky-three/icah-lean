# ICAH Typst Paper Project

Starter paper project for the Lean formalization of the Intermediate-Cardinality Arithmetic Hypothesis (ICAH): stratified continuum, subfield strata, size-aware fields, elementary chains, and direct-limit cardinality.

## Template choice

Baseline: [`unequivocal-ams`](https://typst.app/universe/package/unequivocal-ams/) because it is AMS-style, single-column, and aimed at mathematical papers.

Alternative templates to consider later:

- [`clean-math-paper`](https://typst.app/universe/package/clean-math-paper/) if you want a cleaner modern look with built-in math-paper metadata.
- [`theorion`](https://typst.app/universe/package/theorion/) if the paper becomes theorem-environment-heavy.
- `fine-lncs` only if targeting a Springer LNCS-style proceedings venue.

## Build

```bash
brew install typst
make build
```

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

> `directLimit_card`: a complete cardinal-arithmetic proof that a countable direct limit has cardinality continuum when the level cardinalities are below continuum and their supremum is continuum.

Recommended framing:

> A formalization study that decomposes an intermediate-cardinality continuum hypothesis into proved Lean results, named axioms, and Mathlib contribution targets.

## Before public release

1. Re-run `lake build` in the Lean repo.
2. Paste the exact `#print axioms icahTheorem` output into an appendix.
3. Verify whether the current `README.md` and code comments still describe `directLimit_card` as a stub; update stale comments if the theorem is now fully proved.
4. Minimize every named Mathlib gap into a small standalone Lean example.
5. Decide whether the initial venue is a formalization venue, Lean/mathlib note, or arXiv preprint in logic/formalized mathematics.
