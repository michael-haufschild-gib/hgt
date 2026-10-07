# Exact sampled polar mass on the separated Fejer lattice

Status: dependency-closed paper proof, now formalized in WeilWorkExposingRayLatticeMass.lean. Complete scratch and final installed leaf/cache audits pass, with standard axioms only. The universal WP02 lower inequality remains OPEN.

Let psi be the actual `fejerTest`, and R its actual `flatBumpCorr (17/50) (17/1000)`. Fix X>=4 and integer M>=0. For arbitrary finite coefficient rows c_ij, j=0,...,M, and real weights alpha_i, put f_i(u)=sum_j c_ij psi(u-jX). Define

    C_jk = sum_i alpha_i Re(conj(c_ik)*c_ij),
    b_d = sum_(j,k : j=k+d) C_jk,
    b_0 = sum_i alpha_i sum_j |c_ij|^2,
    n_d = ceil(exp(dX)), eta_d=log(n_d)-dX, 1<=d<=M.

No energy-sign premise is imposed. All sums are finite. Actual sources are compact C2, and the polar subclass is specified by their two actual Fourier values at +/-i/2.

## Rounding, separation, and exact sampling

For t=dX>=4, exp(t)>=1+t>=5. The ceiling lies in [exp(t),exp(t)+1), and exp(1/4)>=1+1/4. Thus n_d<exp(t+1/4), giving 0<=eta_d<1/4 and n_d>=2. This is an analytic inequality, not a numerical computation.

The established source bounds give R(y)=0 for |y|>=17/25, R(-y)=R(y), and R(eta)>=1/4 for 0<=eta<=1/4. Expand the actual autocorrelation:

    sum_i alpha_i Re(weilTest(f_i,f_i)(y)) = sum_j,k C_jk R(y-(j-k)X).

At y=log(n_d), the j-k=d terms contribute b_d R(eta_d). Every other integer difference is separated by at least X-eta_d>=15/4>17/25, so every omitted term vanishes exactly. Self-autocorrelation has even real part; in the normalization of `atomCoeff`,

    trace(n_d) = 2 b_d R(eta_d).

This retains every pair, including complex coefficients, diagonal terms and all site counts. For M=0 the positive-lag sum is empty.

## Unconditional defect identity

Set P_i(+)=sum_j c_ij exp(jX/2), P_i(-)=sum_j c_ij exp(-jX/2). Expanding Re(P_i(+) conj(P_i(-))) and pairing (j,k) with (k,j) gives

    sum_i alpha_i Re(P_i(+) conj(P_i(-)))
       = b_0 + 2 sum_(d=1)^M b_d cosh(dX/2).

The diagonal is exactly b_0; no positivity assumption on alpha is needed for this equality. Substitute the exact samples and divide only by R(eta_d)>=1/4:

    b_0 + sum_(d=1)^M cosh(dX/2) trace(n_d)/R(eta_d)
       = sum_i alpha_i Re(P_i(+) conj(P_i(-))).

This is the strongest exact positive-survivor identity, including the polar defect of arbitrary coefficient rows.

## Actual polar specialization and stability

The Fourier translation identity gives fhat_i(i/2)=psihat(i/2)P_i(-) and fhat_i(-i/2)=psihat(-i/2)P_i(+). Both profile factors are nonzero: psi is real, nonnegative, compact, and equal to one on a nonempty central interval; its exponential-weighted integrals are strictly positive. Consequently actual polar vanishing forces P_i(+)=P_i(-)=0. The exact recovered mass law is

    b_0 = -sum_(d=1)^M cosh(dX/2) trace(n_d)/R(eta_d).

For nonnegative alpha, b_0>=0. Since cosh is positive and R>=1/4, this also proves

    b_0 <= 4 sum_(d=1)^M cosh(dX/2) |trace(n_d)|.

If every sampled trace is nonnegative, b_0=0, and every row with alpha_i>0 is zero. Thus every nonzero positive polar mixture in this class has a strictly negative sampled atom. In particular it cannot be repaired to complete zero trace by adding further nonnegative polar mixtures on the same profile lattice, regardless of site count or energy budget. Extend coefficient rows by zero to a common M to cover every finite repair.

## Prior work, scope, and utility

The continuous polar moment identity is already `integral_weilTestEvenPart_mul_cosh_eq_zero`. Finite covariance and Gram expansions are classical and already in the corpus. `WeilWorkDeficitGeometricRadicalObstruction` already proves injective power-sampling for broad truncated Riemann kernels on j*log(b), using an outer convolution coefficient. A new generic lattice no-go alone would be redundant.

The proposed contribution is exact mass recovery and weighted stability for the actual narrow Fejer source at arbitrary real spacing, with explicit rounded integer samples and the full polar defect retained. It identifies why the successful short-step overlapping geometric completion must leave this separated-lattice class. External scientific novelty is not established. Nonlattice centres, overlapping profiles, and arbitrary atom repairs remain outside the statement. No lower bound for the universal matched cone follows.

### Strengthening found during the paper audit

Only fhat_i(i/2)=0 is needed for the recovered mass: the real pole product already vanishes when P_i(-)=0, regardless of P_i(+). Thus the exact identity and stability theorem hold on the larger one-half-pole subclass, and in particular on actual polar tests. This is a source-level strengthening of the same identity, not a new positivity premise. Its profile multiplier is admitted directly as a strictly positive exponential-weighted integral.


## Formal closure

The seven public capstones are `sampled_trace`, `sampled_mass_balance`, `polar_mass_identity`, `mixture_mass_identity`, `mixture_mass_stability`, `exists_negative_sample` and `sampled_nonnegative_iff_zero_active`, namespace RHTower.ExposingRayLattice. The exact identities and stability bound allow real mixture weights; nonnegativity enters only the positive-mass/sign classification. M=0 and zero weights are covered. All proofs use the literal profile, explicit samples and the exact atom normalization.

The classification is for the specified finite packet class, not arbitrary repairs. The universal exposing-ray lower bound and its RH conclusion remain unproved. EVIDENCE.md records final audits and prior-source limitations.
