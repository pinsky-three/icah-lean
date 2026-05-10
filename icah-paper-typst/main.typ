#import "@preview/unequivocal-ams:0.1.2": ams-article
#import "src/macros.typ": *

#show: ams-article.with(
  title: [Intermediate-Cardinality Strata and Direct Limits in Lean: A Formalization Study around the Continuum],
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
    This paper draft presents a Lean 4 formalization study of an Intermediate-Cardinality Arithmetic Hypothesis (ICAH): a stratified view of the real continuum under the negation of the Continuum Hypothesis. The development packages intermediate-size subsets of $RR$ as strata, refines strata that are closed under field operations as subfield strata, bundles cardinal data with ordered-field structure through size-aware fields, and studies elementary chains and their direct limits in the language of rings. The current formalization contains several fully proved components, including an intermediate-cardinal witness under $not "CH"$, a concrete synthetic stratum of cardinality $aleph_1$, a countability bound for the real algebraic numbers, definability lemmas for the graphs of addition and multiplication, and a cardinal-arithmetic theorem for direct limits. The remaining dependencies are deliberately exposed as named axioms, yielding both a mathematical statement and a roadmap for Mathlib contributions.
  ],
  bibliography: bibliography("refs.bib"),
)

#align(center)[#smallcaps([Working draft]) · version 0.2.0 · May 2026]

#include "sections/01-introduction.typ"
#include "sections/02-background.typ"
#include "sections/03-formal-architecture.typ"
#include "sections/04-proved-results.typ"
#include "sections/05-axiom-inventory.typ"
#include "sections/06-related-work.typ"
#include "sections/07-neighboring-fields.typ"
#include "sections/08-conclusion.typ"
