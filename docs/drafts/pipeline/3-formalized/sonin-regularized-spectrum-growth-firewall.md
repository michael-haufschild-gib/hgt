# Regularized Sonin spectrum: logarithmic prefix budget

[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]. Scoped F2 retirement, not RH.

## Exact claim

Fix `a>0`. Let `K_a` be `soninAllPrimeResidualOperator a ha` and `C_a` be
`soninAllPrimeColumnOperator a ha`. For either operator, including rectangular
singular values for `C_a`,

`sum_(j<N) s_j = O_a(1+log(N+1))`.

Consequently neither `K_a* K_a` nor `C_a* C_a` has all power traces equal to
`normalizedPrimeArchMoment`. In particular `SoninAllPrimeExactTraceMomentWeld`
is false, using its already-proved equivalence to matching at one finite positive
aperture. No claim is made about aperture-escaping projective normalizations,
unsubtracted principal channels, or arbitrary Sonin architectures.

## Checked corpus inputs

- `SoninTimeBandSchatten.centralSoninProjectionCorrection_memSchattenClass_one`:
  the common correction `J_a` is genuinely trace class, not merely compact.
- `SoninTimeBandIdeal.centralSoninDilationCornerResidual_eq_correction_factorization`:
  `R_i=(1-Q)D_i J_a-J_a D_i Q0`, with `||D_i||<=2` and both complements contractive.
- `SoninPrimePowerRegularization`: exact coefficient
  `w_(p,k)=1/((k+2)*p^((k+2)/2))`; the prime-square slice is `1/(2p)`.
- `SoninAllPrimeResidualKernel`, `SoninCoupledPrimeResidual`: literal block-diagonal
  and common-input column assemblies, both retaining unsquared weighted residuals.
- `SoninAllPrimeMomentApertureContinuity`:
  `soninAllPrimeExactTraceMomentWeld_iff_exists_exact_positive_aperture`.
- `XiDeterminantIdealConsequences`: exact self-adjoint Xi determinants need
  singular-value prefixes asymptotic to a positive multiple of `log(N)^2`.
  The squared-Xi normalization below must not be identified with its unsquared API.

## Dependency-closed paper argument

1. Put `J=J_a`. Ideal inequalities give
   `||R_i||_1<=4||J||_1` and `||R_i||_2<=4||J||_2`, uniformly in prime and depth.
2. For integer `M>=2`, retain exactly `p<=M, k<M`. Write either literal assembly
   as `A=H_M+E_M`. Every retained block/column is the original `w_i R_i`, with its
   original prime/depth label. Isometric coordinate embeddings preserve nuclear
   norm, and disjoint output coordinates give exact squared-HS disintegration.
3. Since `p>=2`, the geometric depth sums give absolute constants `b,c` with
   `sum_retained w_i <= b sum_(2<=n<=M) 1/n <= b(1+log M)` and
   `sum_discarded w_i^2 <= c/M`. For the latter, split discarded indices into
   `p>M` and `k>=M`: the first is bounded by a constant times
   `sum_(n>M) n^-2 <= 1/M`; the second by a constant times `2^-M sum_(n>=2)n^-2`.
   Hence `||H_M||_1<=B_a(1+log M)` and `||E_M||_2^2<=D_a/M`.
4. Ky Fan's variational inequality and finite Cauchy--Schwarz give, for every
   trace-class `H` with Hilbert--Schmidt residual `E=A-H`,
   `sum_(j<N) s_j(A) <= ||H||_1 + sqrt(N)*||E||_2`.
   Taking `M=max(2,N)` proves the claimed prefix budget for both assemblies.
   No bounded synthesis of unweighted prime columns is assumed.
5. Exact moment matching implies RH by the existing positive source Hankel
   endpoint. This implication is used inside the contradiction, not assumed.
   The exact Xi zero-copy enumeration then identifies the target moments with
   `sum_n b_n^(2r+2)`, where `b_n` is the ordered reciprocal-Xi approximation
   sequence, including both signs and every divisor-multiplicity copy.
6. Lidskii and the rectangular Gram-square law identify source traces with
   `sum_n s_n(A)^(2r+2)`. Positive power sums determine decreasing nonnegative
   summable sequences: if their heads differed, dividing their moment bounds by
   the larger head's powers would give a positive constant bounded by a geometric
   sequence tending to zero; removing equal finite prefixes proves equality at
   every index. Apply this to `s_n(A)^2` and `b_n^2`. Thus `s_n(A)=b_n`, whose
   prefix has unconditional Riemann--von Mangoldt residue `1/(2*pi)` at scale
   `log(N+1)^2`, contradicting step 4. For the column, coordinate synthesis is
   isometric and gives the required literal-column prefix comparison.
7. Compact aperture capture and continuity turn the block-diagonal cofinal
   moment weld into the fixed-aperture equality just excluded.

The determinant interpretation is `det(1-z^2 A* A)=(XiC(z)/XiC(0))^2`, not
unsquared Xi. Lean uses the direct multiplicity-exact moment argument above;
it does not need or claim a newly formalized squared-determinant theorem.

## Hostile audit and positive survivor

- Trace class alone for each block is insufficient: its constant and common
  source factor are retained in steps 1--3.
- Square-summable coefficients alone would only give a square-root prefix bound.
  The literal harmonic prime-square profile supplies the logarithmic head cost
  and inverse-linear squared tail cost simultaneously.
- The column assembly is not a bounded mixing of the block-diagonal assembly.
  Step 2 uses finite nuclear sums and exact HS tails; it never assumes that mixing.
- This is not an RH contradiction. It rejects this regularized moment producer,
  even if RH is true. Restoring the principal Euler shell is outside its premises.
- Positive survivor: the explicit, coefficient-faithful head/tail budget in
  steps 1--4, not merely the negation of moment matching.

## Literature status

Finite time-band spectral smoothing is established theory; see
[Bonami--Karoui](https://arxiv.org/abs/1509.02646). Here it is already formalized
via the exact Fourier Taylor expansion. Ky Fan inequalities and Fredholm
logarithmic derivatives are established tools. The claimed delta is their
application to these two literal corpus assemblies; scientific priority is unverified.

## Lean state

Nine `SoninRegularized*` modules and `HTGeometry.OrderedPositiveMomentDetermination`
are wired and pass individual `lake env lean` checks. Prime-box coefficient mass
is at most `2(1+log M)`; discarded squared mass is at most `4/M`. Both literal
assemblies satisfy:

`sum_(j<N) s_j(A_a) <= 8 ||J_a||_1 (1+log(N+1)) + sqrt(512 a^2)`.

Both normalized prefixes tend to zero; the two exact discarded HS energies agree.
Final audited exclusions:

- `SoninRegularizedMomentWeldNoGo.not_soninAllPrime_exact_positive_aperture_moments`.
- `SoninRegularizedMomentWeldNoGo.not_soninAllPrimeExactTraceMomentWeld`.
- `SoninRegularizedCoupledMomentNoGo.not_soninAllPrimeCoupled_exact_positive_aperture_moments`.

These are module-qualified references; declarations themselves live in `RHTower`.
Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`; formal lint passes.
No full or umbrella
build run. Positive salvage is the exact source head/tail budget, not a replacement
RH producer. STC, CSB cofinal normalization, singular/varying-aperture families,
and unsubtracted principal Euler channels are not retired by these statements.
