#import "src/ams-article.typ": ams-article
#import "src/macros.typ": *

#show: ams-article.with(
  title: [Intermediate-Cardinality Strata and Direct Limits in Lean: A Formalization Study around the Continuum],
  running-head: [ICAH: Formalization Study around the Continuum],
  authors: (
    (
      name: "Bregy Malpartida",
      department: [Independent Researcher / Computational Artist],
      organization: [pinsky.studio],
      location: [Lima, Peru],
      url: "https://pinsky.studio",
    ),
  ),
  abstract: [
    This article presents a Lean 4 formalization study of an Intermediate-Cardinality Arithmetic Hypothesis (ICAH) under the negation of the Continuum Hypothesis. *Pillar A* constructs elementary substructures of $RR$ at every intermediate cardinality by Mathlib's downward Löwenheim–Skolem theorem. *Pillar B* constructs real-closed subfields of every infinite cardinality up to the continuum and is conditional, for its elementarity clause, on the $RR$-specialized consequence of real-closed-field model completeness that such subfield inclusions are elementary. The development proves Tarski–Vaught elementarity theorems for arbitrary countable elementary chains, a direct-limit cardinality identity, and closure below the continuum. The elementary-chain existence fields in both top-level theorems are witnessed by constant chains; they do not assert a strictly increasing hierarchy. Separately, under $not "CH"$ the development constructs a nonconstant monotone family of intermediate-size real-closed subfields covering $RR$. It proves that every covering family of subsets of $RR$ of size below the continuum has at least $"cof"(2^(aleph_0))$ members and that a real-closed-subfield covering family of exactly that length exists. Elementarity of this cofinal family is not proved. The project declares zero project axioms: `NotCH` and the Pillar B model-theory condition are explicit hypotheses, and guarded kernel audits exclude hidden assumptions such as `sorryAx`.
  ],
  bibliography: bibliography("refs.bib"),
)

#align(center)[Version 1.0.0 · August 2026]

#include "sections/01-introduction.typ"
#include "sections/02-background.typ"
#include "sections/03-formal-architecture.typ"
#include "sections/04-proved-results.typ"
#include "sections/05-axiom-inventory.typ"
#include "sections/06-related-work.typ"
#include "sections/07-neighboring-fields.typ"
#include "sections/08-conclusion.typ"
