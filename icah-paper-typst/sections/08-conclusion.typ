#import "../src/macros.typ": *

= Conclusion, reproducibility, and engagement plan

The current formalization is best presented as a rigorous formalization study rather than as a finished foundational theory. Its strongest components are already useful beyond the project name: the DLS-based existence of elementary substrata of $RR$ at every intermediate cardinality (`exists_elementary_substratum`), the nesting and directed-union lemmas (`elementaryInclusion`, `directed_iSup_isElementary`), a strictly increasing $NN$-chain (`strictElemChain`), a cofinal elementary family of length $"cof"(c)$ (`exists_cofinal_elem_family_cof_length`), the real-closedness of $RR$ (`Real.isRealClosed`), the existence of named real-closed subfields of every infinite cardinality up to the continuum (`exists_rc_subfield`), the Tarski–Vaught elementarity theorems for arbitrary countable direct limits — both relativized (`tarskiVaughtDirectLimit`) and ambient-free (`ofLevelElem`) — and the direct-limit cardinality identity and closure theorem (`directLimit_card_eq_iSup`, `directLimit_card_lt_continuum`).

Pillar A formalizes the informal picture under $not "CH"$ alone: elementary strata at every intermediate size, a strictly increasing countable chain, and a cofinal elementary family of optimal length. Pillar B remains the conditional, algebraically explicit companion: named real-closed subfields with native `IsRealClosed` instances, whose inclusions into $RR$ (and into each other) are elementary only given `RCFModelComplete`.

The most important editorial decision is to keep the paper honest about the distinction between proved Lean results and named hypotheses. This is not a weakness: the hypothesis inventory — `NotCH` for the regime, `RCFSubfieldRealElementary` / `RCFModelComplete` for Pillar B only, both visible in type signatures, with the kernel-level audit machine-checked by `#guard_msgs` — turns an ambitious mathematical program into precise, independently attackable formalization problems. Two defects of earlier drafts — a vacuous cardinality theorem and two false subfield axioms, with $QQ$ as counterexample — were detectable from the development's own documentation and are now repaired here.

== Reproducibility

The development is pinned and machine-checked:

- *Toolchain*: `leanprover/lean4:v4.31.0-rc2`.
- *Mathlib revision*: `a810615ff479602ad66b5403d179bfa805314a50` (June 2026), locked in `lake-manifest.json`.
- *Release*: repository tag `v1.1.0` at @pinsky_icah_lean; this tag is the artifact corresponding to the present paper. The earlier `v1.0.0` tag is the pre-chain-strengthening artifact and should not be cited for the results of Sections 1 and 4.
- *Paper compiler*: Typst 0.14.2, pinned and checked by the paper Makefile and CI.
- *Continuous integration*: `lake build` (including the guarded audits), zero-`sorry` and zero-project-`axiom` checks, followed by a pinned Typst build of the manuscript.
- *Statistics*: 11 Lean modules under `ICAH/`, circa 2,200 lines of Lean, 0 project axioms, 0 sorries; both main theorems audit to `[propext, Classical.choice, Quot.sound]`.

== Declaration-to-paper mapping

#table(
  columns: (auto, auto, auto),
  align: left,
  table.header([*Lean declaration*], [*Paper role*], [*Hypotheses*]),
  [`NotCH`], [the $not "CH"$ regime (Def., Section 5)], [—],
  [`RCFSubfieldRealElementary` / `RCFModelComplete`], [$RR$-specialized RCF subfield-inclusion elementarity (Gap, Section 5)], [—],
  [`exists_intermediate_cardinal`], [intermediate cardinal witness], [`NotCH`],
  [`Stratum`, `SizeAwareField`], [core objects (Section 3)], [—],
  [`syntheticStratum`], [concrete $aleph_1$-stratum], [`NotCH`],
  [`exists_elementary_substratum(_extending)`], [Pillar A strata via DLS], [ZFC-pure],
  [`elemSubstratumSubfield`], [substrata are subfields], [ZFC-pure],
  [`elemSubstratum_models_thReal`], [substrata model $op("Th")(RR)$], [ZFC-pure],
  [`elementaryInclusion`], [nested elementary pair], [ZFC-pure],
  [`directed_iSup_isElementary`], [directed unions stay elementary], [ZFC-pure],
  [`strictElemChain`], [strict $NN$-chain witness], [`NotCH`],
  [`exists_rc_subfield`], [Pillar B strata, every $aleph_0 <= kappa <= c$], [ZFC-pure],
  [`relAlgebraic_isRealClosed`], [relative algebraic closures are RC], [ZFC-pure],
  [`Real.isRealClosed`], [$RR$ is real closed], [ZFC-pure],
  [`fieldOnStratum`], [packaging lemma (Section 4)], [ZFC-pure],
  [`tarskiVaughtDirectLimit`], [chain theorem rel. $RR$], [ZFC-pure],
  [`ofLevelElem` / `realize_ofLevel_iff`], [ambient-free chain theorem], [ZFC-pure],
  [`directLimit_card_eq_iSup`], [limit cardinality identity], [ZFC-pure],
  [`directLimit_card_lt_continuum`], [closure under countable chains], [ZFC-pure],
  [`cofinal_family_length_lower_bound`], [covering subsets, $"cof"(c)$ lower bound], [ZFC-pure],
  [`exists_cofinal_elem_family`], [`𝔠.ord`-indexed elementary covering family], [`NotCH`],
  [`exists_cofinal_elem_family_cof_length`], [$"cof"(c)$-length elementary covering family], [`NotCH`],
  [`exists_cofinal_rc_family`], [`𝔠.ord`-indexed real-closed covering family], [`NotCH`],
  [`exists_cofinal_rc_family_cof_length`], [$"cof"(c)$-length real-closed covering family], [`NotCH`],
  [`exists_cofinal_rc_family_elementary`], [RC family with elementary inclusions], [`NotCH`, `RCFModelComplete`],
  [`cofinal_family_limit_size`], [M6 limit-size clause], [`NotCH`],
  [`ICAHElementary` / `icahElementary` / `elementaryStrata`], [*Theorem 1* (Pillar A)], [`NotCH`],
  [`ICAHStatement` / `icahTheorem` / `algebraicRealization`], [*Theorem 2* (Pillar B)], [`NotCH`, `RCFModelComplete`],
)

== Engagement plan

+ Post on the Lean Zulip model-theory stream with the repository and a minimized in-framework statement of `RCFSubfieldRealElementary`; this may surface in-progress RCF or real-closure work and prevents duplicated upstreaming. (A draft is maintained in `docs/UPSTREAMING.md`.) Do not claim this is the unique Mathlib gap until that check returns.
+ PR sequence: (1) DLS-based elementary substrata of $RR$ plus `directLimit_card_eq_iSup` — small, ZFC-pure, attractive; (2) the ambient-free Tarski–Vaught chain theorem for `Language.DirectLimit`, together with `elementaryInclusion` and `directed_iSup_isElementary`; (3) `Real.isRealClosed`, `isRealClosed_of_forall_root`, `relAlgebraic_isRealClosed` after the dedup check; (4) long-term, RCF model completeness modeled on the ACF files via Robinson's test.
+ Venue: this is a formalization paper — ITP or CPP, with an arXiv preprint cross-listed cs.LO primary and math.LO secondary. It should not be sent to a set-theory venue as-is, where the mathematics reads as exercises. JAR is appropriate only if the RCF-gap analysis is substantially expanded.
+ Keep p-adic and valued-field analogies as future work, not as the main thesis.
