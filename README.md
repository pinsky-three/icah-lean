# ICAH Lean

Lean 4 + Mathlib formalization of intermediate-cardinality strata of the real
continuum under `¬CH`, with elementary-substructure, real-closed-field,
direct-limit, and cofinality results.

The repository accompanies the paper *Intermediate-Cardinality Strata and
Direct Limits in Lean: A Formalization Study around the Continuum*.

## Publication release

The artifact for the paper is release **v1.0.0**. It pins:

- Lean `v4.31.0-rc2` in `lean-toolchain`;
- Mathlib revision `a810615ff479602ad66b5403d179bfa805314a50` in
  `lake-manifest.json`;
- Typst `0.14.2` in `icah-paper-typst/Makefile` (CI reads the same pin).

## What is proved

The development has two complementary pillars.

### Pillar A: elementary substrata

`ICAH.icahElementary (h : NotCH)` proves, from `¬CH` alone:

- an intermediate cardinal exists;
- for every intermediate cardinal `κ`, an elementary substructure of `ℝ` in
  the first-order ring language exists with cardinality exactly `κ`;
- elementary substrata of `ℝ` are carriers of subfields;
- a countable elementary-chain direct limit stays below the continuum when all
  levels do;
- every real belongs to some intermediate-size elementary substratum.

The elementary-chain existence field in this top-level theorem is witnessed by
the **constant chain** at one elementary substratum. It is not a strictly
increasing or cofinal hierarchy.

### Pillar B: real-closed subfields

`ICAH.icahTheorem (hCH : NotCH) (hMC : RCFModelComplete)` proves the algebraic
packaging from `¬CH` and one explicit model-theory hypothesis. Its ingredients
include:

- `Real.isRealClosed`: `ℝ` is real closed;
- `exists_rc_subfield`: for every `ℵ₀ ≤ κ ≤ 𝔠`, a real-closed subfield
  of `ℝ` of cardinality exactly `κ` exists;
- `fieldOnStratum`: every `Stratum` carries a transported
  `SizeAwareField` structure;
- general Tarski–Vaught theorems for arbitrary countable elementary chains;
- an exact cardinality identity for their direct limits.

The chain used inside `icahTheorem` is again a **constant chain**, this time at
one intermediate-size real-closed subfield. The hypothesis
`RCFSubfieldRealElementary` (compatibility name `RCFModelComplete`) supplies
elementarity of that subfield's inclusion into `ℝ`.

### Cofinal family and the `cf(𝔠)` threshold

Separately, `exists_cofinal_rc_family` constructs a nonconstant monotone family
of intermediate-size real-closed subfields whose union is all of `ℝ`.

The precise optimality statement is:

- any covering family of subsets of `ℝ`, each of cardinality `< 𝔠`, has at
  least `cf(𝔠)` members;
- under `¬CH`, a monotone covering family of intermediate-size real-closed
  subfields with exactly `cf(𝔠)` members exists.

The inclusions in this cofinal family are **not proved elementary**. The current
development therefore does not construct a nonconstant cofinal elementary
hierarchy.

## Explicit hypotheses and audit status

The project declares **zero project axioms** and contains **zero sorries**.
The two mathematical assumptions are ordinary propositions passed explicitly
to the theorems that need them:

| Hypothesis | Role |
|---|---|
| `ICAH.NotCH` | The `¬CH` regime, defined as `continuum ≠ aleph 1` |
| `ICAH.RCFSubfieldRealElementary` / `ICAH.RCFModelComplete` | The inclusion of every real-closed subfield of `ℝ` into `ℝ` is elementary in the ring language; used only by Pillar B |

The remaining RCF statement is a classical consequence of model completeness
or quantifier elimination for real-closed fields, but it is not yet available
in the required Mathlib `ModelTheory` form.

`ICAH/Main.lean` locks the dependency sets of the flagship declarations with
`#guard_msgs in #print axioms`. The expected kernel dependencies are:

```text
[propext, Classical.choice, Quot.sound]
```

Because `NotCH` and `RCFModelComplete` are theorem parameters rather than
environment axioms, they appear in type signatures rather than in this kernel
dependency list.

## Repository layout

```text
ICAH/Axioms.lean            NotCH and intermediate-cardinal lemmas
ICAH/SizeAwareField.lean    cardinal-aware field packaging
ICAH/Strata.lean            strata and cardinal bounds
ICAH/Definability.lean      ring-language definability kernel
ICAH/RealClosed.lean        real-closedness of ℝ and root criterion
ICAH/FieldOnStratum.lean    real-closed subfields and Pillar B hypothesis
ICAH/ElementaryChain.lean   elementary chains and direct limits
ICAH/ElementaryStrata.lean  DLS substrata and Pillar A
ICAH/CofinalFamily.lean     cofinal families and cf(𝔠) optimality
ICAH/Main.lean              Pillar B assembly and guarded audits
icah-paper-typst/           publication manuscript
```

## Reproduce the Lean artifact

Install [elan](https://github.com/leanprover/elan), then run:

```bash
make cache
make build
make sorry-count
make axiom-count
```

The expected final counts are both zero.

## Build the paper

Install exactly Typst `0.14.2` from the pinned GitHub release (see
`icah-paper-typst/README.md`; Homebrew is unpinned), then run:

```bash
make -C icah-paper-typst build
```

The output is `icah-paper-typst/build/icah-paper.pdf`. The paper Makefile
rejects a different Typst version and sets a fixed `SOURCE_DATE_EPOCH`, so
repeated release builds are byte-for-byte reproducible.

## Further work

- Formalize the real-closed-subfield elementarity theorem in Mathlib.
- Construct a nonconstant cofinal family of elementary substructures and relate
  it to the real-closed family.
- Generalize the local countable direct-limit elementarity theorems to the most
  reusable directed-system statement for upstreaming.

See `docs/UPSTREAMING.md` for the proposed Mathlib engagement sequence.

The repository includes `.zenodo.json` metadata so the tagged release can be
archived after the maintainer enables the Zenodo–GitHub integration. The
deposit records license `other-open` because the tree is dual-licensed (MIT
plus CC BY 4.0); after the first deposit, add both SPDX licenses in the
Zenodo UI if the integration flattened them. No DOI is claimed until Zenodo
creates the deposition; once minted, it should be added to this README,
`CITATION.cff`, and the paper bibliography.

## License and citation

Lean source code is licensed under the MIT License. The manuscript and
documentation are licensed under CC BY 4.0. See `LICENSE` and `CITATION.cff`.
