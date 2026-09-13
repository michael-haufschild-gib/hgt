# Actual dyadic-root heat producer: all-clock obstruction and positive reserve

- Stage: 5-failed; this heat producer is falsified, not the analytic-root route.
- Status: no RH proof. Direct checks, four targeted builds, and all 20 public-theorem axiom audits passed.
- Scope: test the actual signed convolution-half heat producer for the first root rung.
- Previous boundary: dense heat schedules failed; sparse clocks were unexcluded.
- New boundary: every positive heat clock tending to zero fails with every cofinal pole clock.

## Frozen construction test

Write `a = squarefreeConvolutionHalf`, `b = zetaBinomialHalf`,
`c = moebiusBinomialHalf`, `q = mPart 2 c`. The existing exact identity is `a = b * q`.
For real positive `t`, put

`B(t) = sum b(m) m^(-2/3) exp(-m*t)` and
`F(t) = sum a(n) n^(-2/3) exp(-n*t)`.

**Positive survivor [PROVED HERE]:** there exists a fixed `delta > 0` with
`Re F(t) >= delta * B(t)` for every positive `t`.
More precisely, `norm(F(t)-B(t)) <= (1-delta)*B(t)`.

## Dependency-closed paper proof

1. The binomial recurrence gives `abs(choose(1/2,k)) <= abs(choose(-1/2,k))`.
   Multiplicativity gives `norm(c(n)) <= b(n)`; at `n=4` the coefficients are
   `1/8` and `3/8`, so the inequality is strict.
2. Absolute convergence at exponent `4/3`, the positive-half convolution square,
   and the telescoping p-series bound give
   `sum norm(c(d))*d^(-4/3) < sum b(d)*d^(-4/3) <= 2`.
   Consequently the correction tail beyond `d=1` has mass strictly below one.
3. Absolute convergence justifies
   `F(t) = sum c(d)*d^(-4/3)*B(d^2*t)`.
   Positivity gives `0 <= B(d^2*t) <= B(t)` for `d>=1`.
   Subtracting the entire absolute correction tail yields the estimate with
   `delta = 2 - sum norm(c(d))*d^(-4/3) > 0`.
   Lean rearranges the equivalent product-indexed series using the summable
   majorant `norm(q(i)*i^(-2/3))*b(j)*j^(-2/3)*exp(-j*t)`.
4. The prime coefficients `b(p)=1/2` and divergence of prime reciprocals give
   `B(t) -> +infinity` as `t -> 0+`, hence the same for `Re F(t)`.
5. At `s=2/3` the pole-factor Cayley coordinate is `-2`. The positive-half
   partial sum is at most `-1/2` for `N>=3`. Central-binomial weights
   `centralBinom(k)/2^k` are nondecreasing; their alternating partial sums
   satisfy `T(2m+4)<=-1` and `T(2m+3)>=3/2`. Hence the actual pole-factor
   product has norm at least `1/2` for every `N>=4`.
6. The Carleman factor is fixed and nonzero at `2/3`. Local boundedness of the
   normalized family would therefore bound every sufficiently late raw heat
   sample, contradicting step 4 for every positive heat clock tending to zero.
   Cofinality of the pole clock supplies step 5. No heat-gap condition is used.

## No-go closure

- Exact rejected claim: the literal `poleClearedFirstTraceLaplaceTwoClockApprox`
  has a locally bounded family on `rightHalf` for some positive heat clock
  tending to zero and some cofinal pole-degree clock.
- Strongest positive survivor: the complete signed-source reserve inequality,
  together with actual all-time divergence and the uniform pole-factor floor.
- Consequence for the RH chain: sampling cannot repair this producer. A
  replacement must compensate its unbounded source mass while preserving the
  actual Euler germ. Analytic continuation through possible zeros remains open.
- Paper status: dependency-closed. Lean source estimates, normalization, and the
  no-existence theorem passed direct checks without heartbeat changes.

## Adversarial audit

- A signed series is not termwise positive. Use the exact square-supported
  correction and its complete absolute mass, not selected positive coefficients.
- Do not rearrange a merely conditionally convergent double sum.
- Sparse sample bounds at `6/11` alone need not control a continuous heat profile.
  This test instead uses one different real point in the required open region.
- Divergence of the raw heat sum alone does not exclude a normalized limit:
  retain the actual pole factor and nonzero Carleman factor.
- Even complete failure of this producer does not retire the analytic-root route.
  A replacement must construct the same Euler germ with justified continuation.

## Verification

- Scratch directory: `/tmp/dyadic-root-source-mass.PxcZPF`.
- Lean status: coefficient domination, strict prime-square comparison, and the
  complete correction tail `< 1` passed `lake env lean` in `Coefficients.lean`.
  Production module `RHTower.SquarefreeConvolutionHalfSourceMass` is umbrella-wired;
  targeted build audit passed. The complete heat rearrangement, positive reserve,
  and divergence also passed `lake env lean`; production module
  `RHTower.SquarefreeConvolutionHalfHeatMass` is umbrella-wired and its targeted
  build passed. `PoleFactorTwoThirdsLowerBound` and
  `SquarefreeConvolutionHalfLaplaceAllClocksNoGo` also passed direct checks and
  targeted builds. All four modules are umbrella-wired. `Axioms.lean` audits all
  20 public theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- No numerical experiments, custom axioms, placeholders, or heartbeat increases.
- Final global `scripts/formal_tools.py lint` reports seven unrelated unreachable modules:
  `RHTower.Sieve.KloostermanGlobalCollisionCoprime`,
  `HTGeometry.NormalizedPureStateInfidelity`, `HTGeometry.QuantumLeastSquaresGram`,
  `HTGeometry.QuantumNullPrincipalAngle`, `HTGeometry.QuantumStagHuntDecoherence`,
  `HTGeometry.QuantumStagHuntGraphPotential`, and `HTGeometry.QuantumStagHuntPotential`.
  These unrelated files and umbrellas were not changed for this investigation.
- No changes to the global-root receiver or its hypotheses.

## Search audit

- Corpus deep/method searches were partial: 57,397 inventoried files in the first
  snapshot; compiler coverage was incomplete. Candidate names were checked
  against local sources and in `/tmp/dyadic-root-source-mass.PxcZPF/Names.lean`.
- Broad `lacunary` search found [Peres--Yang, June 2026](https://arxiv.org/html/2606.28860v1).
  Theorems 1.1--1.2 concern almost every dilation parameter of an integer orbit;
  they do not provide the fixed-source heat-sample bound needed here. The present
  attack therefore retains every heat time rather than borrowing a metric
  almost-everywhere conclusion.
- Broad `resummation` search found [Martin, August 2026](https://arxiv.org/abs/2608.04182).
  Its abstract reports finite-loop effective-potential rules. No global analytic
  root-continuation conclusion was identified there; it is not used as a premise.
