# TH: coarse eighth-moment absorption fails at the actual center

- **ID:** TH-growth-coarse-eighth-absorption
- **Stage:** 5-failed
- **Type:** FALSIFIED sufficient comparison
- **Source:** ../1-in-progress/theta-c5-curvature-defect-growth.md

## Exact obstruction

The literal residual
`R(q)=dominantPair(q)/(2P(q)^2)-C(q)[D8(q)+(3^7 M0(q)^2+5^7 M0(q)^4+7^7 M0(q)^6)M8(q)]`
is strictly negative at `q=pi-3/2`, the actual source center.
`transferAbsorptionResidual_center_neg` proves this without extra premises.
This is not a falsification of the complete growth-transfer sign, C5, or RH.

At q=5/3, the dominant second atom alone makes the coarse cubic loss exceed
the pair reserve, even after replacing the partition denominator by 1 and
discarding all deep and higher odd losses. The exact rational comparison
uses the full degree-dependent pair and eighth moment polynomials. The
analytic inequality exp(19/2)<16384 gives dominantAtomScale(5/3)>1/4096.
It follows that R(5/3)<0. The strictly increasing weighted residual
exp(8q)R(q)/C(q), together with pi-3/2<5/3, yields the actual-center result.

## Positive survivor and paper proof

The normalized literal pair satisfies `r'+8r>0` on q>=3/2. Exact shifted
polynomial identities reduce this to `(P'+2P)Q-PQ'>0`, proved coefficientwise.
The partition strictly decreases. The deep eighth moment cools at rate8;
all adverse moment products cool at least at rate9. Thus
`exp(8q)R(q)/C(q)` strictly increases throughout q>=3/2. This is a nontrivial
source-specific comparison and implies at most one residual sign crossing.
The exact upper bound `completeTransfer<=-R` remains valid but cannot prove
the complete center sign. The failure specifically requires restoring
cancellations lost in the dominant cubic monomial estimate.

## Lean status

- `ThetaCuspCurvatureDefectGrowthPairRelativeCooling`: source pair rate-eight inequality.
- `ThetaCuspCurvatureDefectGrowthResidualMonotonicity`: strict weighted residual increase.
- `ThetaCuspCurvatureDefectGrowthResidualCenterObstruction`: actual-center strict negative sign.

All three are wired in RHTower. Their required final leaf audits
`lake --old env lean -o ... <leaf.lean>` exited0 with empty logs.
Scratch endpoint axiom audits report only propext, Classical.choice, Quot.sound.
No numerical evaluation, added premise, heartbeat increase, or umbrella build.

## Next conjecture

Retain the exact dominant cubic convolution. The proposed polynomial
comparison is `J3_bare <= 2^8 * bareMoment0 * J2_bare` on q>=3/2,
transported to the source as `J3_dominant <= 2^8 * atomMoment0 * J2_dominant`.
The factor is a degree-eight comparison, not a fit to computed values.
Combined with actual mass<1/399 it leaves pair reserve, unlike the killed
bound. Deep-tail mixed sectors and pure odd sectors5,7 still need absorption.
The new conjecture is not yet accepted; its exact point-and-ray cubic
polynomial and reserve sign are being checked at default Lean limits.

2026-10-02 continuation: the replacement pure-cubic conjecture is now
formalized in GrowthDominantCubic with final leaf audit0. Its source
corollary w3J3<J2/4 is unconditional on x>=0. The mixed deep-tail remainder
is being isolated as a positive convolution measure with support>=14.
