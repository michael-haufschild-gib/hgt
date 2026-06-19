# The completed (σ,∂)-system as a constrained gauge theory (Dirac/BRST reframe)

- **ID:** gauge-constraint-brst-reframe
- **Stage:** 0-backlog
- **Type:** STRUCTURAL (organizing lens) — with one falsifiable methodological claim; pure-analogy parts are EMBASSY
- **Priority:** FOUNDATIONAL
- **Source:** chat thread 2026-06-19 (gauge/constraint reading of "the object is fixed by a constraint, not
  propagated by a flow"); ../../door/bucket-time-and-non-holonomic-time.md (#62, #138 constraint-not-flow),
  ../../door/bucket-the-seam-archimedean-obstruction.md (#71), `compute-omega-h2-gl.md` (#27 §S), `substrate-hypothesis.md` ·
  00-status rows #27, #62, #71, #138
- **Statement:** The completed `(σ_p, ∂_s)`-module `𝓜⁺` is a **constrained gauge system** in the precise
  Dirac/BRST sense, under the dictionary

  | gauge / constrained-Hamiltonian | HGT object | status |
  |---|---|---|
  | gauge potential `A_μ` (redundant raw description) | the connection generators `{σ_p}, ∂_s` | N1⁺ |
  | field strength `F_{μν}` | the multi-`q` curvature `F_{pq}` (N2) | flat⟺holonomic; curved⟺non-holonomic |
  | pure gauge `A_μ=∂_μλ` (flat) | holonomic / `corank<∞` / integrable | G3 |
  | genuine field `F≠0` | **non-holonomic / `corank=∞`** (arithmetic) | G3, seam |
  | Gauss's law (first-class constraint) | the FE `Λ(s)=Λ(1−s)` | #138 |
  | gauge group | difference-Galois group `G_L` | G4 |
  | gauge anomaly `∈H²` (Schwinger / Mickelsson–Faddeev) | **`ω∈H²(G_L)`** | #27 |
  | constraint surface | the `σ`-fixed-modulus locus `= Re=½` | #31 |
  | gauge-invariant observable = holonomy / Wilson loop | unitary holonomy of the completed connection | **G5 ⟺ RH** |
  | WDW timelessness; internal clocks | A2: no native clock, only the many clocks `σ_p` | #61 |

  The load-bearing consequence (not analogy): **BRST says compute the obstruction cohomology, do not
  construct the quotient.** This is a *mechanism* for the substrate-hypothesis verdict — it predicts the
  C-axis (construct a native object) keeps returning BRIDGE while the D-axis (study `ω` directly) is the
  live route — and it yields two concrete handles (anomaly inflow; Wess–Zumino coboundary test).

## Goal
Supplies the **"why"** behind `substrate-hypothesis.md` (D-axis over C-axis) as a gauge-theoretic mechanism
rather than an observation, and packages two computational handles for `ω`. **It does not re-derive the
`ω`-computation** — that is banked in `compute-omega-h2-gl.md` §S–§W (Kontsevich–Vishik multiplicative
anomaly, `a_∞=½log2π=−ζ'(0)`, FE-gluing = Schanuel = DSS, exponential-period seam). This card adds the
organizing layer and the inflow recipe, and it **surfaces the crux** carded separately as
`omega-rh-coupling-vs-orthogonality.md`.

## Door passport
- **Door-2.** As a *lens* this is a re-reading; on the C-axis it grades **EMBASSY** (physical analogy). It is
  load-bearing only where it makes a claim the Kontsevich–Vishik framing alone does not: (a) the BRST
  methodological prediction (D-axis is forced, not chosen), and (b) the anomaly-inflow subtraction recipe.
  Grade those **STRUCTURAL**; quarantine the rest as EMBASSY. Honest: the gauge picture independently
  reproduces #71 (`ω=0⟺RH`) — evidence the framing is structural, not decorative, but not itself a theorem.
- **Door-4.** The non-holonomic = curved-connection identification puts the object exactly at the weld
  (`corank=∞` = `F≠0` = not pure gauge), where all parents fail.

## Gates
- [ ] 0 → 1  in-progress: write the dictionary rigorously (each row a precise identification or a flagged
  analogy); state the BRST methodological claim as a falsifiable prediction; specify the inflow recipe and
  the coboundary test as concrete computations; Door passport graded per row.
- [ ] 1 → 2  fully-proven: n/a for the lens (STRUCTURAL); the *handles* graduate via their own cards
  (`compute-omega-h2-gl.md`, `omega-rh-coupling-vs-orthogonality.md`).
- [ ] 2 → 3  formalized: n/a unless a handle yields a Lean-able statement.
- [ ] 3 → 4  publication-ready: "ζ's theory as a constrained gauge system: why the obstruction, not the
  object, is the content."

## Approach
1. **Dirac skeleton.** Primary constraint → consistency → Gauss's law (first-class) → the constraint
   *generates* the redundancy. Identify the HGT analog of "first-class": does the FE constraint generate the
   `G_L`-quotient? Per #135/#136 the FE-cocycle is purely archimedean / the prime generators are
   Fourier-diagonal, so the FE does **not** reduce to the prime side — the "first-class self-consistency" is
   exactly the open question (= whether `ω=0`). State this precisely.
2. **Anomaly inflow (Callan–Harvey) as a computation.** Over `F_q` the geometric "bulk" gives `ω=0` (Deligne,
   single Frobenius, all CC; `g5-over-fq-deligne-unitarity.md`, `archimedean-weil-ii-bedrock.md`). Compute the
   `F_q` trivializer (single Frobenius + Hard-Lefschetz/geometric polarization), then **subtract**: `ω(ℚ)` =
   the trivializing data ℚ lacks = the missing `F₁` (#70) + the missing polarization (#151). Makes `ω` a
   *difference*, not an absolute computation.
3. **Wess–Zumino consistency = the coboundary test.** An anomaly is real iff the cocycle is not a coboundary.
   Prime part already acyclic (`compute-omega-h2-gl.md` §R, `H(t)E(−t)=1`); leading archimedean part is a
   counterterm (`a_∞=−ζ'(0)`, §S item 5). Reduce "ω≠0?" to: is the `s=1` Stieltjes residue a coboundary in
   the place/FE complex? — equivalent to freshness (`regularization-freshness.md`) / Schanuel.
4. **Wilson-loop reading of G5.** RH = unitarity of the holonomy of the curved completed connection around
   loops = the gauge-invariant observable. Connect to `weil-positivity-operator.md` / `carrier-herglotz-rh.md`.

## Cross-references
- `compute-omega-h2-gl.md` (#27) — **the `ω`-computation home**; this card is its organizing/methodology layer, not a re-derivation.
- `substrate-hypothesis.md` — the D-axis verdict this card supplies a mechanism for (BRST: obstruction, not quotient).
- `omega-rh-coupling-vs-orthogonality.md` — **the crux this lens surfaces** (coupled vs orthogonal).
- `../2-fully-proven/constraint-not-flow-theorem.md` (#138) — the FE-as-constraint = the Gauss-law row.
- `../2-fully-proven/archimedean-prime-cross-term.md` (#135/#134) — FE-cocycle purely archimedean = "not first-class on the prime side."
- `g5-over-fq-deligne-unitarity.md`, `../1-in-progress/archimedean-weil-ii-bedrock.md` — the `F_q` bulk for the inflow subtraction.

## Log
- 2026-06-19 — created in 0-backlog from the chat thread. Reads `𝓜⁺` as a constrained gauge system; the new
  content is the **BRST methodological mechanism** (compute the obstruction, not the quotient ⟹ D-axis forced)
  + the **anomaly-inflow recipe** (`ω(ℚ)` = `F_q`-bulk trivializer subtracted) + the **Wilson-loop reading of
  G5**. SO-1 check: the `ω`-as-multiplicative-anomaly computation is **already banked** in `compute-omega-h2-gl.md`
  §S–§W and `substrate-hypothesis.md` §6–§7; this card does not re-derive it. Grep-confirmed the gauge/BRST/
  Wilson/Wess–Zumino/inflow framing was absent from `drafts/`.
