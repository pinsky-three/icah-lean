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
    This paper draft presents a Lean 4 formalization study of an Intermediate-Cardinality Arithmetic Hypothesis (ICAH): a stratified view of the real continuum under the negation of the Continuum Hypothesis. The development packages intermediate-size subsets of $RR$ as strata, bundles cardinal data with ordered-field structure through size-aware fields, and studies elementary chains and their direct limits in the language of ordered rings. The formalization proves, among other results: that $RR$ is a real-closed field; that for every cardinal $aleph_0 <= kappa <= 2^(aleph_0)$ there is a real-closed subfield of $RR$ of cardinality exactly $kappa$; a Łoś-style elementarity theorem for direct limits of elementary chains compatibly embedded in $RR$; a cardinal-arithmetic theorem for such direct limits; and, under $not "CH"$, a continuum-indexed cofinal family of intermediate-size real-closed subfields whose union is $RR$. The assembled main theorem depends on exactly two named axioms — the set-theoretic regime $not "CH"$ and the model completeness of real-closed fields (Tarski–Seidenberg), the latter being the single remaining Mathlib gap — and the axiom inventory is machine-checked in the build.
  ],
  bibliography: bibliography("refs.bib"),
)

#align(center)[#smallcaps([Working draft]) · version 0.3.0 · June 2026]

#include "sections/01-introduction.typ"
#include "sections/02-background.typ"
#include "sections/03-formal-architecture.typ"
#include "sections/04-proved-results.typ"
#include "sections/05-axiom-inventory.typ"
#include "sections/06-related-work.typ"
#include "sections/07-neighboring-fields.typ"
#include "sections/08-conclusion.typ"
