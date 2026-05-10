#import "../src/macros.typ": *

= Related work

== Continuum hypothesis and independence

The set-theoretic background is classical. The Continuum Hypothesis asks whether $2^aleph_0 = aleph_1$, equivalently whether there is no intermediate cardinal between $aleph_0$ and the continuum. Gödel proved relative consistency of CH with ZFC, and Cohen proved the independence direction using forcing @koellner_ch @cohen1966.

The present work does not contribute to the independence problem itself. It works in the $not "CH"$ regime and asks what kind of algebraic and model-theoretic structure can be layered over intermediate-cardinality subsets or subfields of $RR$.

== Real closed fields

The algebraic and model-theoretic backbone is the theory of real closed fields. Tarski's quantifier elimination for real closed fields makes them a natural setting for definability questions involving addition, multiplication, and order @vddries1988 @marker2002.

ICAH uses this tradition, but the novelty of the formalization is to combine real-closed-field ideas with explicit cardinal bookkeeping and Lean-level axiom accounting.

== Formalized mathematics in Lean

The project belongs to the growing ecosystem of Lean 4 and Mathlib formalizations. Mathlib is a community-driven library of formalized mathematics used for research-scale formal proofs @mathlib_usecase. ICAH is not only a Lean artifact but also a diagnostic of Mathlib boundaries: it identifies concrete places where model theory, real closed fields, cardinal arithmetic, and directed colimits need stronger APIs.

== Direct limits and elementary chains

Elementary-chain arguments are standard in model theory. The formal contribution here is more specific: it tests how far Mathlib's `Language.DirectLimit` API can be pushed toward a fully formal elementary-chain theorem. The direct-limit cardinality result is already proved locally; the elementarity theorem remains a named target.
