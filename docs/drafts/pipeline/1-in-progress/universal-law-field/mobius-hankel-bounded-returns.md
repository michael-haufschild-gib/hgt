# Möbius Gamma--Hankel bounded returns

- ID: ULF-MHBR-001
- Stage: 1-in-progress
- Type: CONJECTURE
- Target: for every epsilon>0, some 1<r<1+epsilon has arbitrarily large N with C_N(r)<=B_r.
- Status: [OPEN CORE]; no unconditional RH proof.

## Higher-law question

Can literal multiplicative inversion impose a global signed-energy ceiling in additive order,
without pointwise cancellation or positivity of individual insertion steps? The candidate law
would concern the full integer formation, not independent prime cells or a chosen phase.

Write E_N(a;r)=Gamma(r) sum_(1<=m,n<=N) a_m a_n/(m+n)^r and
D_N(r)=Gamma(r) sum_(n<=N) mu(n)^2/(2n)^r. Then C_N(r)=E_N(mu;r)-D_N(r).

## Audited facts and exact RH edge

- [CORPUS] `MobiusLaplaceGammaHankelWall`: E_N is the exact weighted Laplace-square
  integral; D_N is uniformly bounded for fixed r>1; positivity gives only C_N>=-D_N.
- [CORPUS] `MobiusLaplaceMellinPlancherelBridge`:
  `mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_implies_riemannHypothesis`.
  Constants may depend on r. Cutoffs may depend on r. No uniformity as r decreases to 1 is required.
- [CORPUS] `MobiusGammaHankelTransverseEscapeCone`: an off-line zero forces C_N(r)->+infinity
  throughout a nonempty interval 1<r<2 Re(rho). A few negative cutoffs do not exclude this.
- [CORPUS] `GibbsSignedCovarianceAccumulation`: prime insertion has a signed forcing term;
  bounding accumulated forcing against its baseline is exactly bounding the endpoint.
  `GibbsCriticalDissipationAntiscaleResonance`: the undissipated antiscale channel has actual
  finite-prime resonances. `GibbsAntiscaleFirstTraceFrame`: scalar normalization does not remove it.
- [CORPUS] `PrimeSquareMobiusSectorFracture`: finite periodic Euler clocks have positive mean
  prod_(p in P)(1-1/p)^2 and agree with mu where P covers all prime factors. These are not the
  squarefree-support-truncated Gibbs coefficients; do not interchange the two approximations.
- [CORPUS] `MobiusFinitePrimeApertureSourceConsumption`: matching finite Euler aperture to N
  reproduces the complete arithmetic prefix, not an extra averaging parameter.
- [CORPUS] `MobiusAdditiveCircleBoundary`: circle Parseval does not bound evaluation at 1.
- [CORPUS] `MobiusAdditiveTriangleChowlaFrontier`: diagonal deletion leaves aggregated binary
  correlations. A generic covariance inequality does not settle their sign.
- [LITERATURE] Liflandsky, arXiv:2607.09797v3: half-power Laplace decay implies RH;
  its stronger converse uses extra assumptions. Verjovsky, arXiv:2607.25002v2: smoothing and
  local-moment reformulations do not prove cancellation at the distinguished arithmetic point.
- [LITERATURE] Helfgott--Thompson, arXiv:2101.08773: exact Heath--Brown/Vaughan decomposition
  supplies fast computation, not a square-root upper bound on the answer.

## Frozen candidate

[CONJECTURE] Collective diagonal dominance: C_N(r)<=0 for every N and every r>=1.
Meaning: additive cross-interference of the actual Möbius prefix never increases integrated
energy above its diagonal budget. This is stronger than bounded returns and is not being
asserted as a universal-field theorem. Its appeal is the full signed, source-fixed comparison;
there is no chosen zero, divisor, phase, or auxiliary convergence hypothesis.

Evidence, not proof: previous RunPod scan at r=1,1.01,1.1,1.5 and every 2<=N<=20000 found
negative total covariance. Thousands of positive increments rule out monotone descent as an
explanation. No statement about all N follows from the scan.

## Proof-attempt loop

1. Independent insertion contraction: [FALSIFIED AS A PROOF PRINCIPLE] by the existing exact
   antiscale resonance. Survivor: retain signed accumulated forcing, not its absolute majorant.
   The candidate total bound itself is not falsified.
2. Fixed-prime averaging: [REJECTED AS A SUBSTITUTE] finite periodic clocks have a positive
   mean, whereas matching squarefree-support apertures simply reproduce the target prefix.
   Survivor to test: remove the periodic mean before comparing energies.
3. Global centering: quantitative attack in progress. Subtracting mean b_N changes every matched
   physical coefficient by b_N. Its coherent energy is at least Gamma(r)b_N^2 N^2/(2N)^r.
   Prove the exact compatibility cost before claiming this repair transports the target.

The next proof obligation is a source-specific upper bound on signed covariance. None of the
reformulations above is counted as supplying it. Failed intermediate arguments do not falsify
collective diagonal dominance or the weaker requested bounded-return statement.
