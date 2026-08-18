#import "src/ams-article.typ": ams-article
#import "src/macros.typ": *

#show: ams-article.with(
  title: [Elementary strata of the continuum under $not "CH"$: a Lean formalization study],
  running-head: [Elementary strata of the continuum in Lean],
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
    We formalize, in Lean 4 and Mathlib, the elementary-substructure picture of the real continuum under $not "CH"$. Downward Löwenheim–Skolem yields elementary substrata of $RR$ at every intermediate cardinality. Nested elementary substructures of a common model form an elementary pair, so these strata assemble into a strictly increasing $NN$-chain and into a monotone covering family of length $"cof"(2^(aleph_0))$ whose inclusions are elementary. Named real-closed subfields of every infinite cardinality up to the continuum are constructed separately; elementarity of those algebraic inclusions remains conditional on a Mathlib gap (model completeness of RCF). The project declares no axioms: hypotheses appear in type signatures, and kernel audits are machine-checked in CI.
  ],
  bibliography: bibliography("refs.bib"),
)

#include "sections/01-introduction.typ"
#include "sections/02-background.typ"
#include "sections/03-formal-architecture.typ"
#include "sections/04-proved-results.typ"
#include "sections/05-axiom-inventory.typ"
#include "sections/06-related-work.typ"
#include "sections/07-neighboring-fields.typ"
#include "sections/08-conclusion.typ"
