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
    This paper draft presents a Lean 4 formalization study of an Intermediate-Cardinality Arithmetic Hypothesis (ICAH): a stratified view of the real continuum under the negation of the Continuum Hypothesis. The development is organized as two pillars. *Pillar A* proves the main theorem under the single hypothesis $not "CH"$: strata are elementary substructures of $RR$ in the first-order ring language, produced at every intermediate cardinality by Mathlib's downward Löwenheim–Skolem theorem, so elementarity is free by construction. *Pillar B* gives a concrete algebraic realization — strata are relative algebraic closures of generated subfields, with native real-closed-field instances — conditional on one further hypothesis, the $RR$-specialized consequence that real-closed subfield inclusions into $RR$ are elementary (from real-closed-field model completeness / Tarski–Seidenberg), the single remaining Mathlib gap. The formalization proves, among other results: that $RR$ is a real-closed field; that for every cardinal $aleph_0 <= kappa <= 2^(aleph_0)$ there is a real-closed subfield of $RR$ of cardinality exactly $kappa$; Tarski–Vaught elementarity theorems for direct limits of elementary chains, both relativized to $RR$ and ambient-free (the canonical maps into the direct limit are elementary); the cardinality identity $\#F_omega = sup_n \#C_n$ for such direct limits, together with a closure theorem (countable chains of intermediate strata never exhaust $RR$) and a sharpness theorem (the least length of an exhausting family of intermediate strata is exactly $"cof"(2^(aleph_0))$). The project declares zero axioms: the two named hypotheses are threaded explicitly through the theorem statements, and every flagship result is machine-audited in the build to depend only on the Lean kernel axioms.
  ],
  bibliography: bibliography("refs.bib"),
)

#align(center)[#smallcaps([Working draft]) · version 0.4.0 · June 2026]

#include "sections/01-introduction.typ"
#include "sections/02-background.typ"
#include "sections/03-formal-architecture.typ"
#include "sections/04-proved-results.typ"
#include "sections/05-axiom-inventory.typ"
#include "sections/06-related-work.typ"
#include "sections/07-neighboring-fields.typ"
#include "sections/08-conclusion.typ"
