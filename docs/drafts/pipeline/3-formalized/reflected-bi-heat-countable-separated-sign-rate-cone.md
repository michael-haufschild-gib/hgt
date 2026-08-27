# Reflected bi-heat countable separated-sign rate cone

- **ID:** RBH-CSSF
- **Stage:** 3-formalized
- **Type:** COUNTABLE INCOMMENSURATE SIGNED RECEIVER CLASSIFICATION
- **Parent:** RBH-SSF
- **Frontier-map policy:** read only

## Frozen conjecture

Let countable low- and high-rate packets have nonnegative magnitudes `p_i,q_j`,
positive rates `lambda_i,mu_j`, and positive witnesses in both packets.  Suppose
one separator `kappa>0` satisfies

`lambda_i < kappa ≤ mu_j`

for every index.  Assume `Σ p_i < ∞` and the high packet has every positive
hyperbolic moment,

`Σ q_j sinh(mu_j*T) < ∞` for every `T>0`.

Define

`F(t) = -Σ' p_i sinh(lambda_i*t) + Σ' q_j sinh(mu_j*t)`

and

`D = Σ' q_j*mu_j - Σ' p_i*lambda_i`.

Prove the exact countable classification

`(∀t, F(t)=0 ↔ t=0) ↔ 0≤D`.

Also prove the sharper oriented form `0≤D ↔ ∀t>0, 0<F(t)`, then transport
the packet through arbitrary real-power RBH apertures to an RH-equivalent
receiver.

## Corpus basis

- `ReflectedBiHeatSeparatedSignFiniteRateCone` proves finite analogue and exact
  wall derivative limit atom-by-atom.
- `sinh_div_self_strictMonoOn` compares every low and high rate through one
  separator.
- `tendsto_tsum_of_dominated_convergence` is already used by
  `DirichletIncrementDominated` for interchanging a one-sided limit and `tsum`.
- `tendsto_tsum_zero_of_dominated` and nonnegative `tsum` order lemmas provide
  countable tail control.
- Mandatory corpus search found no countable separated-sign hyperbolic packet
  classification.

## Attack

1. Derive summability of both first moments from stated packet assumptions.
2. Use dominated convergence at `t→0+` to prove `F(t)/t → D`.
3. Compare `sinh(rate*t)/rate` through `kappa`; one positive low atom makes
   the countable inequality strict, proving `D≥0 → F(t)>0`.
4. Normalize the low packet by `sinh(kappa*t)`.  Each normalized atom tends to
   zero and is dominated by summable `p_i`; Tannery gives vanishing low packet.
   One positive high atom then forces `F(t)>0` eventually.
5. Prove local uniform convergence on compact intervals from the endpoint
   hyperbolic moment, hence continuity.  If `D<0`, the wall germ is negative and
   eventual high-rate dominance is positive, so IVT produces an extra root.
6. Factor countable physical aperture sums and derive RH equivalence.

## Provisional literature audit

Classical total-positivity and variation-diminishing theory treats sign changes
under totally positive kernels.  The primary literature source checked
(Ben-Avraham–Sharon–Zarai–Margaliot, arXiv:1807.02779) develops finite-dimensional
variation-diminishing systems, not this countable hyperbolic-sine moment cone or
its RBH aperture interpretation.  Search found no exact theorem matching the
statement.  Priority remains provisional pending broader expert review.

## Status

- Mandatory corpus search complete.
- Conjecture frozen.
- Paper proof dependency-closed.
- Formalized in
  `GaloisForLFunctions.RHTower.ReflectedBiHeatCountableSeparatedSignRateCone`.
- Direct `lake env lean` check passed.
- Targeted module build passed.
- Axiom audit passed: only `propext`, `Classical.choice`, and `Quot.sound`.

## Formal theorem package

- `tendsto_reflectedBiHeatCountableSeparatedSignReporter_div_self_nhdsGT_zero`
- `reflectedBiHeatCountableSeparatedSignReporter_pos`
- `reflectedBiHeatCountableSeparatedSignWallOriented_iff`
- `tendsto_reflectedBiHeatCountableLowRateSum_div_sinh_atTop`
- `continuousOn_reflectedBiHeatCountableSeparatedSignReporter_Icc`
- `exists_pos_reflectedBiHeatCountableSeparatedSignReporter_eq_zero_of_derivative_neg`
- `reflectedBiHeatCountableSeparatedSignWallSelective_iff`
- `reflectedBiHeatCountableSeparatedSignApertureGap_eq_reporter`
- `reflectedBiHeatCountableSeparatedSignApertureGap_eq_zero_iff`
- `riemannHypothesis_iff_reflectedBiHeatCountableSeparatedSignApertureGap_eq_zero`

## New exact insight

The finite separated-sign cone survives countable completion without a uniform
rate gap.  Pointwise inequalities `lambda_i<kappa≤mu_j`, finite low mass, and
all positive high hyperbolic moments suffice.  No countable tail correction
appears: packet has only wall zero exactly when first wall derivative is
nonnegative.

Key new rigidity mechanism is two-ended.  Near wall, endpoint hyperbolic moments
dominate divided series and expose exact first moment.  At infinity, normalized
low packet tends to zero by Tannery even when low rates accumulate at separator;
one positive high atom forces eventual positivity.  Local uniform convergence
then turns negative derivative into constructive additional positive root.

Countable real-power aperture factorization transports full cone to exact RH
receivers.

## Failure boundaries

- Two or more rate-order sign changes.
- No strict pointwise low/high separator.
- Packets without full positive hyperbolic moments.
- Source-derived coefficient laws and non-diagonal collision channels.
