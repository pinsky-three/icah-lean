# ICAH Typst Paper Project

Publication source for *Elementary strata of the continuum under ¬CH: a Lean formalization study*: elementary substrata, named real-closed subfields, elementary-chain direct limits, and cofinal families of length `cf(𝔠)`.

## Template choice

Baseline: [`unequivocal-ams`](https://typst.app/universe/package/unequivocal-ams/) because it is AMS-style, single-column, and aimed at mathematical papers.

Alternative templates to consider later:

- [`clean-math-paper`](https://typst.app/universe/package/clean-math-paper/) if you want a cleaner modern look with built-in math-paper metadata.
- [`theorion`](https://typst.app/universe/package/theorion/) if the paper becomes theorem-environment-heavy.
- `fine-lncs` only if targeting a Springer LNCS-style proceedings venue.

## Build

The Makefile and CI require Typst **0.14.2** exactly. Homebrew's `typst`
formula is unpinned and will fail `make build` if it is not that version.
Install the matching GitHub release asset instead:

```bash
# Linux x86_64 (same archive CI uses)
curl -fL "https://github.com/typst/typst/releases/download/v0.14.2/typst-x86_64-unknown-linux-musl.tar.xz" \
  -o /tmp/typst.tar.xz
mkdir -p "$HOME/.local/bin"
tar -xJf /tmp/typst.tar.xz -C /tmp --strip-components=1
install -m 0755 /tmp/typst "$HOME/.local/bin/typst"
export PATH="$HOME/.local/bin:$PATH"

# macOS arm64: use typst-aarch64-apple-darwin.tar.xz from the same tag
# https://github.com/typst/typst/releases/tag/v0.14.2

make build
```

The version pin and SHA-256 live in this Makefile so CI cannot drift.

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

> Under `¬CH`, a strictly increasing ℕ-chain of elementary substrata of `ℝ` and a cofinal elementary family of length `cf(𝔠)`, plus the ambient-free chain theorem `ofLevelElem`.

Recommended framing:

> A formalization study that separates general elementary-chain theorems, a strictly increasing countable chain, a cofinal elementary family of optimal length, named real-closed subfields (conditional pillar), explicit hypotheses, and Mathlib contribution targets.

## Release checks

1. Run `make build`, `make sorry-count`, and `make axiom-count` in the Lean repository.
2. Run `make build` here with Typst 0.14.2.
3. Confirm that the manuscript does not advertise `v1.0.0` as the current artifact.
4. Confirm that the top-level chain witnesses are the strictly increasing `strictElemChain`, and that the elementary cofinal family is stated.
