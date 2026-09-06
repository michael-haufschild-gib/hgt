# Literal half-order cross terms grouped by gcd

- **Stage:** 1-in-progress
- **Type:** [BRIDGE] producer audit for SD1; no proof claim
- **Chain:** completed Guinand–Weil source -> marked rectangular current -> affine Suzuki checkpoints -> signed curvature -> coherent boundary -> Xi-screw Green -> RH.
- **Objective:** determine whether the exact gcd partition supplies the missing signed cross-channel order. The unconditional quadratic diagonal estimate is already closed.

## Frozen claim SG1
Use the exact D, K_d and C_d=mu(d)K_d from the active SD1 card. Put
`G_r(M)=sum_(1<=d,e<=M, d!=e, gcd(d,e)=r) C_d(M) C_e(M)`.
SG1 proposes `G_r(M)<=0` for every M and positive r. Summing SG1 would give SD1; it is a stronger independent producer, not a reformulation of SD1. No part of SD1 or its factor one changes if SG1 fails.

## Corpus basis and scope
`RHTower.Sieve.sum_offDiagPairs_eq_sum_primitiveTriples` in `Sieve/PrimitiveRatioDecomposition.lean` supplies the exact partition. `mobius_coprime_dilation_pair_product` in `MobiusAdditiveCircleBoundary.lean` retains the orientation mu(ab) and squarefree cofactor mass. Neither theorem supplies the sum's sign. Generic decreasing-weight and mixed flat/geometric producers are already rejected and will not be retested here.

## Audit protocol
1. Screen every integer endpoint M<=100 and every possible positive gcd using the literal half-order channels; record the first strict positive component and the complete endpoint decomposition. Numerical values guide a paper proof only.
2. If SG1 fails, prove a concrete arithmetic witness analytically, and retain the strongest exact positive statement exposed by the obstruction, including the complete gcd reconstruction and any exact dilation relation. Formalise only dependency-closed statements. A failed component sign does not refute the total SD1 inequality.
3. If no failure appears, investigate the exact arithmetic source; do not treat finite evidence as proof.

## Execution constraints
Direct `lake env lean` checks of new work only, one foreground Lean process. Reuse existing oleans; restore only a specifically missing one. No large rebuilds, no umbrella builds, and no repeated axiom audits of old work.

## Screen outcome and paper continuation

Every M<=100 and every r<=M was screened: 5050 component values, including 168 strict positive components at the numerical tolerance. The first was M=11,r=1. Direct 80-digit evaluation gives G_1(11) approximately 0.0625159666952040; G_2, G_3, G_5 are negative and the full cross sum is approximately -0.0545935145526145. These are numerical observations, not Lean certificates. All remaining G_r(11) vanish by exact support.

**Frozen positive survivor to prove:** exact integer homothety of the unsigned channel, K_(ra)(rM)=sqrt(r) K_a(M). Multiplicativity gives C_(ra)(rM)=sqrt(r) mu(r) C_a(M) when r and a are coprime; shared prime factors annihilate both Möbius products. Hence the gcd-r component at rM is r*mu(r)^2 times the gcd-one component at M with primes dividing r excluded. In particular, if r is prime greater than M, G_r(rM)=r G_1(M). An analytic positive witness at M=11 would therefore produce positive actual gcd components at unbounded cutoffs, without deciding the sign of the complete cross sum. This identity and its prime specialization are paper deductions from exact quotient-block transport; they must be checked in Lean before promotion.

Analytic witness plan: use existing decimal-nine logarithm bounds for 2,3,5, harmonic half-reciprocal bounds to place gamma in a short rational interval, elementary log bounds for log(8/7), and rational square-root sandwiches. No screening result will be imported as a proof premise.

### Analytic witness bounds sufficient for closure
A short rational box suffices: C_1(11) in [0.15,0.18], -C_2 in [0.20,0.21], -C_3 in [0.19,0.20], -C_5 in [0.14,0.15], -C_7 in [0.10,0.11], C_6 in [0.13,0.14], C_10 in [0.023,0.025]. Other channels vanish. In this box the gcd-one sum is strictly positive and the complete off-diagonal is strictly negative (paper interval arithmetic to be certified). To obtain the box, harmonic n=16 gives gamma>0.5768; the existing corrected upper gives gamma<0.57722. `log_le_half_sub_inv` at 8/7 and `Real.log_le_sub_one_of_pos` at 7/8 give `3 log2 -15/112 <= log7 <= 3 log2 -1/8`. Existing log2/log3/log5 decimal-nine inequalities and rational square-root sandwiches then bound the literal finite sums. This uses analytic inequalities, not the screened values, as proof inputs.

Current homothety scratch: `/tmp/ccm_fu_gcd_transport.lean`. It proves the natural floor identity `(r*M-1)/(r*d)=(M-1)/d` for positive r,d, then exact `C_(rd)(rM)=sqrt(r)*mu(r)*C_d(M)` when r and d are coprime. Only direct Lean checks are being used.
