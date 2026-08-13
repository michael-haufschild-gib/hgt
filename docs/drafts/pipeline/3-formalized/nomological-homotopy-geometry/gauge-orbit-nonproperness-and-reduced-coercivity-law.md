# Gauge-orbit nonproperness and reduced coercivity law

- **ID:** `nhg-gauge-properness-obstruction`
- **Stage:** 3 — formalized in Lean 4
- **Lean gate:** [LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED] (2026-08-13)
- **Status:** `[PAPER-PROVED] [UNIVERSAL FIELD THEOREM] [ANALYTIC GATE]`
  `[NO ROUTE INPUT] [NOT RH] [LEAN-PROVED]`

## 1. Setup

Let a topological group `G` act continuously on a Hausdorff space `X`. Let

\[
 q:X\longrightarrow Y
\tag{GP.1}
\]

be a continuous observer and let

\[
 \mathcal S:X\longrightarrow\mathbb R
\tag{GP.2}
\]

be a continuous action. Assume both are gauge invariant:

\[
 q(gx)=q(x),
 \qquad
 \mathcal S(gx)=\mathcal S(x).
\tag{GP.3}
\]

A map is proper when inverse images of compact sets are compact.

## 2. Orbit obstruction

### Theorem 2.1 — invisible noncompact orbit closure kills properness

If some orbit closure `overline{Gx}` is noncompact, neither `mathcal S` nor

\[
 (q,\mathcal S):X\longrightarrow Y\times\mathbb R
\tag{GP.4}
\]

is proper.

#### Proof

By `(GP.3)`, the orbit is contained in the fibre

\[
 \mathcal S^{-1}(\{\mathcal S(x)\})
\]

and also in

\[
 (q,\mathcal S)^{-1}(\{(q(x),\mathcal S(x))\}).
\]

Each displayed target singleton is compact. By continuity and invariance, the orbit closure remains
in both fibres. If either map were proper, its corresponding fibre would be compact, contradicting
the noncompact closed subspace `overline{Gx}`. QED.

### Corollary 2.2 — free proper noncompact gauge actions

If `G` is locally compact, acts freely and properly, and is noncompact, then every orbit is closed
and homeomorphic to `G`. Hence no gauge-invariant action and no invariant observer--action pair can
be proper on `X`.

## 3. Reduction theorem

Assume the orbit space `X/G` is Hausdorff and write `pi:X->X/G`. Invariance gives unique maps

\[
 \bar q:X/G\longrightarrow Y,
 \qquad
 \bar{\mathcal S}:X/G\longrightarrow\mathbb R
\tag{GP.5}
\]

with `q=bar q pi` and `mathcal S=bar mathcal S pi`.

### Theorem 3.1 — reduced properness is the correct gate

1. Properness of `(q,mathcal S)` implies properness of `(bar q,bar mathcal S)`.
2. If `G` is compact and `X` is locally compact Hausdorff, `pi` is proper. Therefore properness of
   `(bar q,bar mathcal S)` implies properness of `(q,mathcal S)`.
3. For a free proper action of noncompact `G`, `(bar q,bar mathcal S)` may be proper while
   `(q,mathcal S)` never is.

#### Proof

For a compact set `K subset Y times R`, the reduced inverse image is the continuous image under
`pi` of the unreduced inverse image. Thus unreduced properness implies reduced properness. For
compact `G`, the orbit projection is proper in the stated setting; composition proves item 2. For item 3,
take `X=G times Y` with `G` acting on the first factor, `q(g,y)=y`, and any proper function
`bar mathcal S:Y->R`. The reduced pair can be proper, while every unreduced fibre contains the
noncompact closed orbit `G times {y}`; Theorem 2.1 applies. QED.

## 4. Relative slice form

Let `S subset X` be a gauge slice meeting each relevant orbit and suppose the restriction

\[
 (q,\mathcal S)|_S:S\longrightarrow Y\times\mathbb R
\]

is proper. This does not make the unreduced pair proper; it supplies **properness modulo gauge**.
Different slices must be compared by the structured Morita rule before their coercivity data can be
identified.

## 5. Field consequences

1. Gauge invariance and unreduced coercivity are incompatible in the presence of a noncompact
   invisible gauge-orbit closure.
2. The cyclic law action can be a valid variational functional while failing every unreduced
   properness test.
3. Observer recurrence controls lifted history only after reduction, framing, or a proved proper
   slice theorem.
4. Adding a gauge-breaking norm by hand changes the field unless the frame is source-selected.
5. Compact gauge sectors are qualitatively different: reduction can preserve properness there.

## 6. Hostile boundary

- A noncompact orbit that is not closed does not alone contradict compactness of its containing
  fibre; noncompact orbit closure or a proper action is the exact hypothesis.
- Properness modulo gauge says nothing about boundedness below or existence of minimizers without
  further assumptions.
- Global gauge anomalies and singular quotient strata are not addressed.
- The theorem supplies an obstruction and the correct reduced target; it does not construct a
  coercive field realization.

## 7. Lean formalization status

- **Status:** `[LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED]`
- **Module:**
  `formal/GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/GaugeProperness.lean`
- **Umbrella wiring:**
  `formal/GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry.lean`, imported by
  `formal/GaloisForLFunctions/HTGeometry.lean`.
- **Exact formal targets:** `gaugeOrbit_nonproperness` (Theorem 2.1),
  `freeProperNoncompact_gaugeOrbit_nonproperness` together with
  `orbitHomeomorph` and `orbit_isClosed` (Corollary 2.2),
  `reducedPair_proper_of_unreducedPair_proper`,
  `compactGroup_orbitProjection_isProperMap`,
  `compactGroup_unreducedPair_proper_of_reducedPair_proper`, and
  `noncompactProduct_reducedProper_unreducedNotProper` (all three clauses of Theorem 3.1).
- **Infrastructure proved, not assumed:** compact-preimage properness and composition/descent;
  compact-group quotient projection properness; free proper orbit closed embedding/homeomorphism;
  explicit free proper first-factor product action; reduced graph properness and unreduced
  nonproperness witness.
- **Leaf verification:**
  `lake env lean GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/GaugeProperness.lean`
  passed on 2026-08-09.
- **Final gates:** umbrella build and scratch-file `#print axioms` audit passed on 2026-08-13;
  card promoted to Stage 3.
