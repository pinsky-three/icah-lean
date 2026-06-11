
# ICAH Lean Project

**Intermediate‑Cardinality Arithmetic Hypothesis (ICAH)** — a Lean 4 + Mathlib workspace for formalising a stratified view of the continuum and building real‑closed field structures on intermediate‑size layers. This README serves as a technical design document *and* contributor guide.

---

## 0) Elevator pitch

ICAH proposes that the classical continuum can be approached via a transfinite ladder of **definability strata** $\{R[\!\le n]\}_{n<\omega_1}\subseteq\mathbb R$ with associated sizes $\kappa_n$ satisfying

$$
\aleph_0 \< \kappa_n < 2^{\aleph_0},
$$

and that each stratum supports a real‑closed field $F_n$ whose field operations are first‑order definable *within the same stratum*. The directed union $\bigcup_{n<\omega_1} F_n$ is conjectured to be **elementarily equivalent** to $(\mathbb R,+,\cdot,<)$; the limit field $F_\omega$ has cardinality $2^{\aleph_0}$. Optional: certain physical configuration spaces (quasicrystals, fracton phases) exhibit Hausdorff dimensions matching $\log_2\kappa_n$ (testable proxy).

This repository provides the **formal scaffolding**: cardinal bookkeeping, first‑order definability interfaces, and an elementary‑chain architecture in Lean 4.

---

## 0.5) Current status (June 2026)

The main assembly theorem `ICAH.icahTheorem` **compiles with zero sorries** and the project declares **zero axioms**. The two mathematical assumptions are explicit `Prop` hypotheses in theorem signatures, and the build locks the kernel axiom audit with `#guard_msgs`:

```
'ICAH.icahTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

| Hypothesis | Role |
|---|---|
| `ICAH.NotCH` | The ¬CH assumption — definitional for ICAH, not a Mathlib gap |
| `ICAH.RCFSubfieldRealElementary` / `ICAH.RCFModelComplete` | The ℝ-specialized consequence that the inclusion of any *real‑closed* subfield of ℝ into ℝ is elementary. This follows from model completeness of RCF (Tarski–Seidenberg) and is the single remaining Mathlib gap |

Highlights of what is **proved** (no axioms beyond the above):

- `Real.isRealClosed` — ℝ is real closed (`Real.sqrt` + IVT), `ICAH/RealClosed.lean`.
- `exists_rc_subfield` — for every `ℵ₀ ≤ κ ≤ 𝔠` there is a **real‑closed** subfield of ℝ of cardinality exactly `κ` (relative algebraic closure of a generated subfield), `ICAH/FieldOnStratum.lean`.
- `fieldOnStratum` — every stratum carries a `SizeAwareField` (Equiv‑transport from such a subfield); formerly an axiom.
- `ElemChain.tarskiVaughtDirectLimit` — Tarski–Vaught for `Language.DirectLimit`: the direct limit of an elementary chain compatibly embedded in ℝ is elementarily equivalent to ℝ; formerly an axiom and formerly misnamed as a Łoś-style result.
- `exists_cofinal_rc_family` — the **honest M6**: a `𝔠.ord`‑indexed monotone family of intermediate‑size real‑closed subfields whose union is all of ℝ (`ICAH/CofinalFamily.lean`). The earlier ℕ‑indexed formulation was vacuous by König's theorem (`cof 𝔠 > ℵ₀`).

Two former axioms were **deleted as mathematically false** and replaced by sound refinements: `subfieldIsRealClosed` (ℚ is a counterexample) and `subfieldStratumElemEmb` (elementarity requires real‑closedness; see `RCSubfieldStratum` + `RCFSubfieldRealElementary`).

See `AGENTS.md` for the full per‑file status and the contributor workflow.

---

## 1) Mathematical specification

### 1.1 Hypothesis (working formal statement)

For each countable ordinal $n<\omega_1$ there exists a subset $R[\!\le n]\subseteq\mathbb R$ and a cardinal $\kappa_n$ with

$$
\aleph_0 < \kappa_n < 2^{\aleph_0} \quad\text{and}\quad \sharp R[\!\le n] = \kappa_n,
$$

such that:

1. (**Internal arithmetic**) There is a real‑closed field structure
   
   $$
   F_n = \big(R[\!\le n],+_n,\cdot_n,<_{n}\big)
   $$
   
   and the graphs of $+_n,\cdot_n$ and the order are **first‑order definable** in the language of ordered rings *with parameters from the same stratum*.

2. (**Elementary chain**) For $m\le n$ we have an elementary embedding $F_m \preceq F_n$ (language of ordered rings). Hence $\bigcup_{n<\omega_1}F_n \preceq \mathbb R$ and is elementarily equivalent to $\mathbb R$.

3. (**Limit size**) The colimit field $F_\omega:=\bigcup_{n<\omega_1}F_n$ has $\sharp F_\omega = 2^{\aleph_0}$.

4. (**Physical proxy; optional**) There exist natural systems with configuration‑space Hausdorff dimensions satisfying $\dim_H\mathcal C_n=\log_2\kappa_n$.

> **Consistency note.** Items (1)–(3) are to be developed relative to ZFC plus additional assumptions (e.g. $\neg$CH or a definability‑driven framework). When CH holds, no classical cardinal strictly between $\aleph_0$ and $2^{\aleph_0}$ exists; formalisation can then treat "size" as a *definability rank* invariant while retaining the algebraic/model‑theoretic content.

### 1.2 Definability viewpoint

We work in the language $\mathcal L_{\mathrm{or}}=\{0,1,+,\cdot,<\}$. A subset $S\subseteq \mathbb R^k$ is **definable inside a structure** $M\models \mathrm{Th}(\mathbb R\text{CF})$ if it is the interpretation of an $\mathcal L_{\mathrm{or}}$-formula with parameters from $M$. The slogan for ICAH is:

- **Arithmetic that remembers its layer**: the graphs of $+_n,\cdot_n$ are definable over $F_n$ and compatible with the inclusion $F_n\hookrightarrow \mathbb R$.
- **Elementary chain principle**: $(F_n)_{n<\omega_1}$ is an elementary, directed system; Tarski–Seidenberg (quantifier elimination for real‑closed fields) is the main engine for preservation of definability.

---

## 2) Formalisation roadmap (Lean 4 + Mathlib)

We structure the proof effort into independent layers; each compiles with axioms/stubs that you later discharge.

### 2.1 Core data structures

- `Stratum` — a record of:
  - `n : Ordinal` (intended countable),
  - `S : Set ℝ`,
  - `κ : Cardinal`,
  - witnesses `h_card : (# {x // x ∈ S}) = κ` and `h_bounds : aleph0 < κ ∧ κ < continuum`.

- `SizeAwareField` — a light wrapper bundling a carrier, its designated cardinal, and a `LinearOrderedField` instance.

These live in:
```
ICAH/Strata.lean
ICAH/SizeAwareField.lean
```

### 2.2 Definability interface

Add a module (to be created by you) `ICAH/Definability.lean`:

- `open FirstOrder` and import `Mathlib/ModelTheory` pieces.
- Define:
  ```lean
  namespace ICAH
  abbrev LOR := FirstOrder.Language.ring
  -- A predicate: a relation/function on a subtype `S` is definable with parameters in `S`.
  structure DefinableOn (S : Set ℝ) (n : ℕ) (k : ℕ) : Prop := ...
  ```
- Provide helpers to lift definability through finite products, images, and projections (use quantifier elimination for RCF once available).

### 2.3 Field on a stratum — ✅ done

The former placeholder axiom

```lean
axiom fieldOnStratum (R : Stratum) :
  ∃ F : SizeAwareField, F.carrier = R.carrier ∧ F.κ = R.κ
```

is now a **theorem** in `ICAH/FieldOnStratum.lean`. The construction follows path (B) strengthened by an existence argument:

1. **Existence of a matching subfield:** `exists_rc_subfield` produces, for any `ℵ₀ ≤ κ ≤ 𝔠`, a real‑closed subfield `K ⊆ ℝ` with `#K = κ`, by taking the relative algebraic closure (`relAlgebraic`) of the subfield generated by a set of size `κ` and proving `relAlgebraic_isRealClosed` via the root‑closure criterion `isRealClosed_of_forall_root` (`ICAH/RealClosed.lean`).
2. **Transport:** the field structure is carried from `K` to the stratum's carrier along a cardinality `Equiv` (`Equiv.field`, `LinearOrder.lift'`).
3. **Real‑closedness of ℝ itself:** `Real.isRealClosed` is proved from `IsRealClosed.of_linearOrderedField` using `Real.sqrt` and the intermediate value theorem for odd‑degree polynomials.

### 2.4 Elementary chain and limit — ✅ done (modulo `RCFSubfieldRealElementary`)

- `ElemChain` packages a directed system of elementary embeddings `F_m ↪ₑ F_n`; `DirectLim` is its `Language.DirectLimit`.
- `ElemChain.tarskiVaughtDirectLimit` (**proved**, formerly an axiom): if every level embeds elementarily and compatibly into ℝ, the direct limit is elementarily equivalent to ℝ. Proof: `Language.DirectLimit.lift` + Tarski–Vaught test.
- `directLimit_card_eq_iSup` and `directLimit_card_lt_continuum` (**proved**): cardinal accounting for countable direct limits, including the closure theorem that countable chains of intermediate strata stay below `𝔠`.
- `RCSubfieldStratum` bundles a stratum whose carrier is a **real‑closed** subfield; the hypothesis `RCFSubfieldRealElementary` / `RCFModelComplete` supplies the inclusion-form elementary embedding into ℝ. This is the only remaining gap.
- **Honest M6** (`ICAH/CofinalFamily.lean`): since `cof 𝔠 > ℵ₀` (König), no ℕ‑indexed chain of intermediate‑size strata can union to ℝ. Instead, `exists_cofinal_rc_family` builds a `𝔠.ord`‑indexed monotone family of intermediate‑size real‑closed subfields with union ℝ, and `cofinal_family_limit_size` shows the union has cardinality `𝔠`.

### 2.5 Optional physics interface (non‑blocking)

Create `ICAH/Physics.lean`:

- Abstract class `ConfigSpace` with a boxed definition `HausdorffDim : Set (ℝ^m) → EReal`.
- Axiomatise (for now) existence of models with $\dim_H = \log_2\kappa_n$. This remains a placeholder until you connect to concrete math.

---

## 3) Repository layout

```
icah-lean/
├─ lean-toolchain               -- toolchain pin
├─ lakefile.lean                -- deps (Mathlib)
├─ Makefile                     -- build / sorry-count / axiom-count targets
├─ .github/workflows/ci.yml     -- CI: build + axiom audit (#guard_msgs) + sorry count
├─ ICAH.lean                    -- umbrella import
├─ ICAH/Prelude.lean            -- smoke tests
├─ ICAH/Axioms.lean             -- NotCH + exists_intermediate_cardinal
├─ ICAH/SizeAwareField.lean     -- size-aware ordered fields
├─ ICAH/Strata.lean             -- strata + M1 cardinal lemmas
├─ ICAH/Definability.lean       -- LOR definability kernel (M2)
├─ ICAH/RealClosed.lean         -- IsRealClosed ℝ + root-closure criterion (M4)
├─ ICAH/FieldOnStratum.lean     -- exists_rc_subfield, fieldOnStratum thm, RCFSubfieldRealElementary (M3+M4)
├─ ICAH/ElementaryChain.lean    -- ElemChain, Tarski-Vaught direct limit, cardinal closure (M5)
├─ ICAH/CofinalFamily.lean      -- 𝔠.ord-indexed cofinal RC family (honest M6)
└─ ICAH/Main.lean               -- ICAHStatement + icahTheorem + axiom audit
```

---

## 4) Build, cache, and run

### 4.1 Prereqs

- Install **elan** (Lean toolchain manager).
- VS Code + Lean 4 extension recommended.

### 4.2 Commands

```bash
make cache         # lake exe cache get — fetch Mathlib precompiled cache (~8 GB)
make build         # lake build (also enforces the axiom audit via #guard_msgs)
make sorry-count   # should print 0
make axiom-count   # should print 0
make clean
```

Open `ICAH/Prelude.lean` to confirm the environment is healthy. CI (`.github/workflows/ci.yml`) runs the same build + audit on every push.

---

## 5) Development milestones

1. **M1 – Cardinal scaffolding** — ✅ **done.**  
   `Stratum`, `SizeAwareField`, cardinal bound lemmas, `syntheticStratum` example.

2. **M2 – Definability kernel** — ✅ **done.**  
   `DefinableOn` API, products/preimages, `graphDefinable_add` / `graphDefinable_mul`.

3. **M3 – Internal field operations** — ✅ **done.**  
   `exists_rc_subfield` + Equiv transport; `fieldOnStratum` is now a theorem.

4. **M4 – Real‑closedness** — ✅ **done.**  
   `Real.isRealClosed`, `isRealClosed_of_forall_root`, `relAlgebraic_isRealClosed` (`ICAH/RealClosed.lean`, `ICAH/FieldOnStratum.lean`).

5. **M5 – Elementary chain** — ✅ **done modulo `RCFSubfieldRealElementary`.**  
   `tarskiVaughtDirectLimit` proved (DirectLimit.lift + Tarski–Vaught); the inclusion of the real-closed subfield underlying an `RCSubfieldStratum` into ℝ is elementary by the `RCFSubfieldRealElementary` / `RCFModelComplete` hypothesis (Tarski–Seidenberg consequence, the one Mathlib gap).

6. **M6 – Size of the limit** — ✅ **done (reformulated).**  
   `directLimit_card_eq_iSup` and `directLimit_card_lt_continuum` proved for ℕ‑chains; the cofinal statement is the `𝔠.ord`‑indexed `exists_cofinal_rc_family` + `cofinal_family_limit_size`, avoiding the König obstruction.

7. **M7 – Optional physics stub** — not started; compartmentalised, non‑blocking.

**Next milestone: M8 — prove `RCFSubfieldRealElementary`** (from quantifier elimination / model completeness of RCF in Mathlib's `ModelTheory` framework), reducing the project to the single explicit hypothesis `NotCH`. See `AGENTS.md` § "Closing the remaining hypothesis gap".

---

## 6) Assumptions and regimes

- **Set‑theoretic backdrop.**  
  The "intermediate size" clause uses classical cardinality. It is **consistent** with ZFC when $\neg$CH holds (e.g., $2^{\aleph_0}=\aleph_2$ or larger).  
  If you want to work *without* assuming $\neg$CH, reinterpret "size" as a **definability rank** invariant; most algebra/model‑theory goals still make sense.

- **Definability vs absoluteness.**  
  When you later study forcing robustness, rely on standard absoluteness for Borel/analytic sets and c.c.c. forcing to keep the strata stable (to be formalised).

---

## 7) How to contribute

- Keep modules compiling by replacing axioms with `by exact ...` proofs incrementally.
- Prefer **small PRs**: one lemma or one instance at a time.
- Add docstrings `/-! ... -/` and `#print axioms` to check unwanted axioms.
- Provide tests/examples in new `Examples/` files; avoid bloating core modules.

---

## 8) FAQ

**Q: Doesn't CH forbid intermediate sizes?**  
Only if CH holds. In ZFC, $\neg$CH is consistent and yields many cardinals between $\aleph_0$ and $2^{\aleph_0}$. ICAH can be developed relative to such universes; alternatively, you can phrase the hierarchy via definability ranks.

**Q: Why real‑closed fields?**  
Because $(\mathbb R,+,\cdot,<)$ admits quantifier elimination (Tarski–Seidenberg). Definability is stable under algebraic constructions, enabling elementary embeddings.

**Q: Is the physics part necessary?**  
No. It’s an optional conjectural bridge; the formal core is purely set‑theoretic and model‑theoretic.

---

## 9) License

MIT for code; text in this README under CC‑BY 4.0.

---

## 10) Acknowledgements & references (informal)

- Classical model theory of real‑closed fields and Tarski–Seidenberg.
- Independence phenomena around CH (Gödel, Cohen; modern expositions).
- Recent definability‑stratified approaches to the continuum (for guiding intuition).
- Formalisation inspiration from proof‑assistant work on forcing and cardinal arithmetic.

---

### Appendix A: Minimal API sketch (historical — superseded by the implemented modules)

```lean
/-- Language of ordered rings. -/
abbrev LOR := FirstOrder.Language.ring

/-- A relation/function on a subtype of ℝ is definable with parameters
    from that subtype. Flesh out with a proper FOL definition. -/
structure DefinableOn (S : Set ℝ) : Prop := (dummy : True)

/-- Elementary embedding between strata fields. -/
structure ElemEmb (A B : Type _) [LOR.Structure A] [LOR.Structure B] :=
(toFun : A → B)
(isElementary : FirstOrder.ElementaryEmbedding LOR A B toFun)
```

This sketch predates the implementation. The real API now lives in `ICAH/Definability.lean` (`LOR`, `DefinableOn`) and `ICAH/ElementaryChain.lean` (`ElemChain`, `↪ₑ[LOR]`). Both paths were ultimately used: direct real‑closedness for construction (M4), elementary substructure via `RCFSubfieldRealElementary` for the chain (M5).

Happy proving!
