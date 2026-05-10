// Minimal paper helpers for the ICAH Typst draft.
// These are intentionally simple so the project does not depend on a theorem
// package API while the main layout uses the AMS-style template.

#let code(x) = raw(x)

#let statement(kind, body) = block(
  inset: 7pt,
  stroke: 0.6pt + gray,
  radius: 2pt,
  breakable: true,
)[
  *#kind.* #body
]

#let definition(body) = statement("Definition", body)
#let theorem(body) = statement("Theorem", body)
#let lemma(body) = statement("Lemma", body)
#let proposition(body) = statement("Proposition", body)
#let construction(body) = statement("Construction", body)
#let remark(body) = statement("Remark", body)
#let gap(body) = statement("Mathlib gap", body)
#let contribution(body) = statement("Contribution", body)

#let todo(body) = block(
  fill: rgb("#fff7d6"),
  inset: 6pt,
  radius: 2pt,
  breakable: true,
)[
  *TODO.* #body
]

#let Lean(name) = raw(name)
#let CH = $"CH"$
#let notCH = $not "CH"$
#let continuum = $2^aleph_0$
#let alephzero = $aleph_0$
#let alephone = $aleph_1$
#let R = $RR$
#let Q = $QQ$
#let Fomega = $F_omega$
#let LOR = $cal(L)_("or")$
