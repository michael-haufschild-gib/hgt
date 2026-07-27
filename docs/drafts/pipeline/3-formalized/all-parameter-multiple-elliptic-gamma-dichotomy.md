# All-parameter multiple elliptic Gamma differential dichotomy

- **ID:** `all-parameter-multiple-elliptic-gamma-dichotomy`
- **Stage:** 3-formalized / publication artifact complete
- **Type:** THEOREM / PUBLICATION CAPSTONE
- **Scientific status:** `[THEOREM] [PROOF CLOSED] [PUBLICATION READY]`
- **Target paper:**
  `../4-publication-ready/multiple-elliptic-gamma-rational-rank-dichotomy/`

## Target theorem

Let `I` be a finite nonempty index set, let `tau_i` lie in the complex upper half-plane, and let
`G_I(z;tau)` be the Nishizawa multiple elliptic Gamma function. Then exactly one of the following
holds:

1. `rank_Q span_Q({1} union {tau_i}) = 2`, and `G_I` and its logarithmic derivative are
   differentially algebraic over `C(z)`;
2. `rank_Q span_Q({1} union {tau_i}) >= 3`, and `G_I` and its logarithmic derivative are
   hypertranscendental over `C(z)`.

Equivalently, hypertranscendence occurs exactly when the period family contains two labels whose
periods, together with `1`, are rationally linearly independent.

For an arbitrary index type, including infinite and empty types, form the rank-three graph whose
edges are pairs `q,r` for which `1,tau_q,tau_r` are rationally independent. For every finite
section `S`, including the empty section:

1. its raw function and logarithmic derivative are differentially algebraic exactly when `S`
   contains no graph edge;
2. both are hypertranscendental exactly when `S` contains a graph edge.

Thus the low sections are exactly the finite faces of the graph's independence complex and the
high sections are its edge-generated upward closure among finite sets. The edgeless case is
exactly one positive rational affine line.

## Formal status

Both halves and their exact arithmetic interface are unconditional:

- `FiniteUnipotentTranslationDifferentialAlgebraicity.lean`;
- `MultipleEllipticGammaTerminalFace.lean`;
- `MultipleEllipticGammaCommonStepNilpotence.lean`;
- `MultipleEllipticGammaPeriodRankDichotomy.lean`;
- `multipleEllipticGamma_exactPeriodRankDichotomy`;
- `multipleEllipticGammaFace_exactPeriodRankLaw`.
- `multipleEllipticGamma_everyFiniteSection_exactRankThreeGraphLaw`;
- `finiteSectionContainsRankThreeEdge_mono`;
- `multipleEllipticGamma_everyPeriodFamily_exactFiniteSectionLaw`;
- `multipleEllipticGammaNonRationalDAExample_not_liesOnRationalRay`;
- `multipleEllipticGammaNonRationalDAExample_differentialAlgebraic`.

## Low-rank route

If no rank-three minor exists, choose one period `omega`. Positivity of imaginary parts makes
`1,omega` rationally independent and forces

```text
tau_i = a_i + b_i omega,   a_i,b_i in Q,   b_i > 0.
```

Clearing denominators and synchronizing the positive integral coefficients gives one
upper-half-plane step `beta` with

```text
beta = m_i tau_i + k_i,   m_i in Z_{>0},   k_i in Z
```

for every `i`. Unit periodicity removes each `k_i`. The intrinsic coface recurrence telescopes
one `beta`-difference into a finite sum of translates of a codimension-one face. Induction through
the finite deletion cube shows that the `(card I + 1)`-st `beta`-difference of the logarithmic
derivative vanishes; the terminal zero-period face is the constant `-2*pi*i`.

A unit-periodic meromorphic function with a nilpotent `beta`-difference has a finite-dimensional
translation orbit stable under the rationally independent shifts `1` and `beta`. The
two-shift stable-space theorem makes it differentially algebraic over `C(z)`. The identity
`G'/G = Psi` transfers the result from the logarithmic derivative to `G`.

## Publication audit

- [x] main theorem and proof organized around augmented rank;
- [x] finite-unipotent lemma and common-step descent presented self-containedly;
- [x] exact correspondence with Kato's non-rational-period question checked against primary source;
- [x] arbitrary-cardinality rank-three graph decides every finite section, including empty;
- [x] infinite scope stated without claiming an undefined infinite-order product;
- [x] all residual partial-result framing and open-case language removed;
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- [x] formal lint passed;
- [x] final module build passed;
- [x] PDF built and visually audited;
- [x] antagonist and general-journal reviews passed after substantive repairs.

## Publication gate

The paper's novelty claim is the exact all-parameter differential classification, including the
non-rational augmented-rank-two phase and every nonempty deletion face. Formal verification is
internal and contributes no novelty or significance claim.
