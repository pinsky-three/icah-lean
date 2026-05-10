#import "../src/macros.typ": *

= Neighboring fields and analogues

The ICAH architecture has natural analogues beyond real closed fields. The closest comparisons are not arbitrary fields but fields equipped with a closure principle and a first-order theory.

== P-adically closed fields

P-adically closed fields are the valued-field analogue most similar in spirit to real closed fields. On the real side, order and real closure control definability. On the p-adic side, valuation, henselianity, and p-adic closure play the corresponding role. Model theory of valued fields studies exactly this pattern: a field is enriched by extra structure, and the central questions concern definability, elementary equivalence, and preservation under extensions or chains @marker_valued_fields @macintyre1976.

A p-adic analogue of ICAH would replace:

+ subsets or subfields of $RR$ by valued subfields of a p-adic ambient field;
+ order/real-closure hypotheses by valuation/henselian or p-adically-closed hypotheses;
+ definability in an ordered-ring language by definability in a valued-field language;
+ real-closed-field elementary chains by valued-field elementary chains.

== Henselian valued fields

Henselian valued fields provide a broader comparison class. They are not merely fields with a topology; they are algebraic structures with a valuation satisfying a lifting principle. This makes them suitable for direct analogues of the ICAH pattern: carrier, extra structure, closure property, definability theory, elementary embeddings, and direct limits.

== Algebraically closed fields

Algebraically closed fields are less close to the order-theoretic content of ICAH, but they share an important formal pattern: a strong closure property plus a well-behaved first-order theory. A stripped-down version of the ICAH architecture could be tested in algebraically closed fields as a simpler control case.

== Paper positioning

#remark[
  The safest comparison is: ICAH is a real-field, cardinal-aware, Lean-formalized instance of a broader model-theoretic pattern. The neighboring fields are real closed fields, p-adically closed fields, henselian valued fields, pseudo real closed fields, pseudo p-adically closed fields, and algebraically closed fields.
]

For the first paper, these analogies should remain in a future-work section. The core contribution should stay focused on the formal Lean development around the real continuum.
