#import "../src/macros.typ": *

#pagebreak(weak: true)
= Conclusion, reproducibility, and engagement plan

The current ICAH formalization is best presented as a rigorous formalization study rather than as a finished foundational theory. Its strongest components are already useful beyond ICAH itself: the DLS-based existence of elementary substrata of $RR$ at every intermediate cardinality (`exists_elementary_substratum`), the real-closedness of $RR$ (`Real.isRealClosed`), the existence of real-closed subfields of $RR$ of every infinite cardinality up to the continuum (`exists_rc_subfield`), the Tarski–Vaught elementarity theorems for direct limits — both relativized (`tarskiVaughtDirectLimit`) and ambient-free (`ofLevelElem`) — the direct-limit cardinality identity and closure theorem (`directLimit_card_eq_iSup`, `directLimit_card_lt_continuum`), and the $"cof"(c)$ sharpness pair for exhausting families.

The most important editorial decision is to keep the paper honest about the distinction between proved Lean results and named hypotheses. This is not a weakness: the hypothesis inventory — `NotCH` for the regime, `RCFSubfieldRealElementary` / `RCFModelComplete` for Pillar B only, both visible in type signatures, with the kernel-level audit machine-checked by `#guard_msgs` — turns an ambitious mathematical program into precise, independently attackable formalization problems. Two defects of earlier drafts — a vacuous cardinality theorem and a missed Löwenheim–Skolem shortcut — were detectable from the development's own documentation and are now repaired here.

== Reproducibility

The development is pinned and machine-checked:

- *Toolchain*: `leanprover/lean4:v4.31.0-rc2`.
- *Mathlib revision*: `a810615ff479602ad66b5403d179bfa805314a50` (June 2026), locked in `lake-manifest.json`.
- *Repository*: @pinsky_icah_lean, with CI running `lake build` (which enforces the `#guard_msgs` audits), a zero-`sorry` check, and a zero-`axiom` check.
- *Statistics*: 11 Lean modules under `ICAH/`, circa 1,800 lines of Lean, 0 axioms, 0 sorries; both main theorems audit to `[propext, Classical.choice, Quot.sound]`.

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
  [`exists_rc_subfield`], [Pillar B strata, every $aleph_0 <= kappa <= c$], [ZFC-pure],
  [`relAlgebraic_isRealClosed`], [relative algebraic closures are RC], [ZFC-pure],
  [`Real.isRealClosed`], [$RR$ is real closed], [ZFC-pure],
  [`fieldOnStratum`], [packaging lemma (Section 4)], [ZFC-pure],
  [`tarskiVaughtDirectLimit`], [chain theorem rel. $RR$], [ZFC-pure],
  [`ofLevelElem` / `realize_ofLevel_iff`], [ambient-free chain theorem], [ZFC-pure],
  [`directLimit_card_eq_iSup`], [limit cardinality identity], [ZFC-pure],
  [`directLimit_card_lt_continuum`], [closure under countable chains], [ZFC-pure],
  [`cofinal_family_length_lower_bound`], [sharpness, lower bound], [ZFC-pure],
  [`exists_cofinal_rc_family(_cof_length)`], [covering families, optimal length], [`NotCH`],
  [`cofinal_family_limit_size`], [M6 limit-size clause], [`NotCH`],
  [`ICAHElementary` / `icahElementary`], [*Theorem 1* (Pillar A)], [`NotCH`],
  [`ICAHStatement` / `icahTheorem`], [*Theorem 2* (Pillar B)], [`NotCH`, `RCFModelComplete`],
)

== Engagement plan

+ Post on the Lean Zulip model-theory stream with the repository and a minimized in-framework statement of `RCFSubfieldRealElementary`; this may surface in-progress RCF or real-closure work and prevents duplicated upstreaming. (A draft is maintained in `docs/UPSTREAMING.md`.)
+ PR sequence: (1) DLS-based elementary substrata of $RR$ plus `directLimit_card_eq_iSup` — small, ZFC-pure, attractive; (2) the ambient-free Tarski–Vaught chain theorem for `Language.DirectLimit`; (3) `Real.isRealClosed`, `isRealClosed_of_forall_root`, `relAlgebraic_isRealClosed` after the dedup check; (4) long-term, RCF model completeness modeled on the ACF files via Robinson's test.
+ Venue: this is a formalization paper — ITP, CPP, or the Journal of Automated Reasoning, with an arXiv preprint cross-listed math.LO/cs.LO. It should not be sent to a set-theory venue as-is, where the mathematics reads as exercises.
+ Keep p-adic and valued-field analogies as future work, not as the main thesis.
