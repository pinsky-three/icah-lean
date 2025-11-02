
# ICAH Lean Project

**Intermediate‑Cardinality Arithmetic Hypothesis (ICAH)** — a Lean 4 + Mathlib workspace for formalising a stratified view of the continuum and building real‑closed field structures on intermediate‑size layers. This README serves as a technical design document *and* contributor guide.

---

## 0) Elevator pitch

ICAH proposes that the classical continuum can be approached via a transfinite ladder of **definability strata** $\{R[\!\le n]\}_{n<\omega_1}\subseteq\mathbb R$ with associated sizes $\kappa_n$ satisfying

$$
\aleph_0 \;<\; \kappa_n \;<\; 2^{\aleph_0},
$$

and that each stratum supports a real‑closed field $F_n$ whose field operations are first‑order definable *within the same stratum*. The directed union $\bigcup_{n<\omega_1} F_n$ is conjectured to be **elementarily equivalent** to $(\mathbb R,+,\cdot,<)$; the limit field $F_\omega$ has cardinality $2^{\aleph_0}$. Optional: certain physical configuration spaces (quasicrystals, fracton phases) exhibit Hausdorff dimensions matching $\log_2\kappa_n$ (testable proxy).

This repository provides the **formal scaffolding**: cardinal bookkeeping, first‑order definability interfaces, and an elementary‑chain architecture in Lean 4.

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
  def LOR := FirstOrder.Language.ordRing
  -- A predicate: a relation/function on a subtype `S` is definable with parameters in `S`.
  structure DefinableOn (S : Set ℝ) (n : ℕ) (k : ℕ) : Prop := ...
  ```
- Provide helpers to lift definability through finite products, images, and projections (use quantifier elimination for RCF once available).

### 2.3 Field on a stratum

Replace the placeholder axiom:
```lean
axiom fieldOnStratum (R : Stratum) :
  ∃ F : SizeAwareField, F.carrier = R.carrier ∧ F.κ = R.κ
```
with a construction:

1. **Carrier:** `carrier := {x : ℝ // x ∈ R.S}`.
2. **Operations:** define `+_R, ⋅_R` by restricting the real operations and **proving closure** under your stratum hypotheses (this is where definability/elementarity assumptions enter).
3. **Order:** inherit `≤` from ℝ; check linearity.
4. **Real‑closedness:** either
   - (A) show `F_R ≺ ℝ` (elementary substructure) and use “elementary substructures of RCF are RCF”, or
   - (B) prove directly: every positive has a square root; every odd polynomial has a root.

### 2.4 Elementary chain and limit

- Define a directed system of embeddings `ι_{m n} : F_m ↪ₑ F_n` for `m ≤ n`.
- Use `ModelTheory.ElementarySubstructure` and `Substructure.iSup` to form the union object `F_ω`.
- Prove `F_ω ≺ ℝ` (union of an elementary chain is elementary) ⇒ elementarily equivalent to ℝ.
- Cardinal accounting with `Cardinal`:
  - Show `#⟪F_n⟫ = R.κ` for each `n`.
  - Supply a hypothesis ensuring `#⟪F_ω⟫ = 2^aleph0`.

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
├─ ICAH.lean                    -- umbrella import
├─ ICAH/Prelude.lean            -- smoke tests (compiles out-of-the-box)
├─ ICAH/SizeAwareField.lean     -- size-aware ordered fields
├─ ICAH/Strata.lean             -- strata, cardinal bounds (placeholders)
├─ ICAH/Main.lean               -- statement stub `ICAHStatement`
└─ (you will add)
   ├─ ICAH/Definability.lean
   ├─ ICAH/ElementaryChain.lean
   └─ ICAH/Physics.lean
```

---

## 4) Build, cache, and run

### 4.1 Prereqs

- Install **elan** (Lean toolchain manager).
- VS Code + Lean 4 extension recommended.

### 4.2 Commands

```bash
elan toolchain install leanprover/lean4:stable
lake update
lake exe cache get   # fetch mathlib precompiled cache (optional, speeds up builds)
lake build
```

Open `ICAH/Prelude.lean` to confirm the environment is healthy.

---

## 5) Development milestones (with suggested PR granularity)

1. **M1 – Cardinal scaffolding**  
   Formalise `Stratum`, `SizeAwareField`, and the `Cardinal` facts you’ll need.  
   *Deliverable:* Lemmas `SizeAwareField.card` and bounds for a synthetic example.

2. **M2 – Definability kernel**  
   Minimal API to talk about definable functions/relations on subtypes of ℝ.  
   *Deliverable:* Composition/product/projection lemmas.

3. **M3 – Internal field operations**  
   Pick a concrete family of strata (e.g., definability ranks you can actually verify) and build `+_n` and `⋅_n` that are closed and definable.  
   *Deliverable:* Instances `[LinearOrderedField ⟪F_n⟫]`, proofs of closure.

4. **M4 – Real‑closedness**  
   Path A: elementary‑substructure route; Path B: direct real‑closed axioms.  
   *Deliverable:* `theorem F_n_realClosed : RealClosedField ⟪F_n⟫`.

5. **M5 – Elementary chain**  
   Provide embeddings, prove union is elementary, show `F_ω ≡ ℝ`.  
   *Deliverable:* `theorem union_elementary_equiv : Th ⟪F_ω⟫ = Th ℝ`.

6. **M6 – Size of the limit**  
   Establish `#⟪F_ω⟫ = continuum`.  
   *Deliverable:* a cardinal arithmetic proof using your hypotheses.

7. **M7 – Optional physics stub**  
   Formal statement of the proxy conjecture. Keep it compartmentalised.

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

### Appendix A: Minimal API sketch (to implement)

```lean
/-- Language of ordered rings. -/
abbrev LOR := FirstOrder.Language.ordRing

/-- A relation/function on a subtype of ℝ is definable with parameters
    from that subtype. Flesh out with a proper FOL definition. -/
structure DefinableOn (S : Set ℝ) : Prop := (dummy : True)

/-- Elementary embedding between strata fields. -/
structure ElemEmb (A B : Type _) [LOR.Structure A] [LOR.Structure B] :=
(toFun : A → B)
(isElementary : FirstOrder.ElementaryEmbedding LOR A B toFun)
```

Fill this API progressively — keep proofs modular so you can switch between the “elementary substructure” and “direct real‑closedness” paths.

Happy proving!
