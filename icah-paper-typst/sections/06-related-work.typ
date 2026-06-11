#import "../src/macros.typ": *

= Related work

== Formalizations of the independence of CH

The set-theoretic background is classical: Gödel proved relative consistency of CH with ZFC, and Cohen proved the independence direction using forcing @koellner_ch @cohen1966. Crucially for the present paper, this metatheory has itself been formalized. The *Flypitch* project of Han and van Doorn gave a formal proof of the independence of the Continuum Hypothesis in Lean, with both consistency directions obtained by forcing with Boolean-valued models — Cohen forcing for $not "CH"$ and collapse forcing for CH @flypitch_itp @flypitch_cpp. Independently, Gunther, Pagano, Sánchez Terraf, and Steinberg formalized the independence of CH in Isabelle/ZF @isabelle_zf_ch.

The contrast sharpens the positioning of ICAH in one sentence: Flypitch and the Isabelle/ZF line formalize the *metatheory* (unprovability, via forcing models), while ICAH works *object-theoretically inside* the $not "CH"$ regime, building structure on intermediate cardinalities rather than building models of set theory. The present work contributes nothing to the independence problem itself; it presupposes its resolution and inhabits one of the two resulting worlds.

== Real closed fields and certified quantifier elimination

The algebraic and model-theoretic backbone is the theory of real closed fields. Tarski's quantifier elimination makes them the natural setting for definability questions involving addition, multiplication, and order @vddries1988 @marker2002; the standard real-algebraic reference is Bochnak–Coste–Roy @bochnak_coste_roy.

On the formalization side, the gap `RCFSubfieldRealElementary` (compatibility spelling `RCFModelComplete`) has substantial prior art in other proof assistants. Cohen and Mahboubi formalized, in Coq/SSReflect, a certified quantifier-elimination procedure for the first-order theory of real closed fields, yielding decidability with a correctness proof @cohen_mahboubi_lmcs (the `math-comp/real-closed` library). McLaughlin and Harrison implemented a proof-producing decision procedure for RCF in HOL Light @mclaughlin_harrison_cade. Neither development transfers directly to Mathlib's deep-embedded `FirstOrder` framework, but Cohen–Mahboubi is the closest blueprint for the remaining gap; Section 5 explains why the cheaper categoricity route used for Mathlib's ACF completeness is unavailable for RCF.

== Formalized mathematics in Lean and Mathlib

The project belongs to the growing ecosystem of Lean 4 and Mathlib formalizations @mathlib_cpp @mathlib_usecase. Two parts of Mathlib carry the present development: the model theory library (elementary substructures, Skolem functions and downward Löwenheim–Skolem, `Language.DirectLimit`, and the deep-embedded algebra of `Language.ring` up to the completeness of ACF) and the cardinal/ordinal library (König's theorem, cofinality, fundamental sequences). ICAH is not only a Lean artifact but also a diagnostic of Mathlib boundaries: it identifies concrete places where model theory, real closed fields, and directed colimits need stronger APIs — most pointedly, the absence of any elementarity result for `Language.DirectLimit` and of model completeness for RCF.

== Elementary chains and direct limits

Elementary-chain arguments are standard in model theory; the canonical reference is Chang–Keisler @chang_keisler, and the König/cofinality background is in Kunen @kunen and Jech @jech. The formal contribution here is more specific: it tests how far Mathlib's `Language.DirectLimit` API can be pushed toward a fully formal elementary-chain theorem. The relativized elementarity theorem (`tarskiVaughtDirectLimit`, via `DirectLimit.lift` and the Tarski--Vaught test), the *ambient-free* chain theorem (`ofLevelElem`: the direct limit of an elementary chain is an elementary extension of each level, by formula induction), and the cardinality identity (`directLimit_card_eq_iSup`) are all proved locally; they are natural candidates for upstreaming, since Mathlib's `DirectLimit` file currently has no elementarity results.
