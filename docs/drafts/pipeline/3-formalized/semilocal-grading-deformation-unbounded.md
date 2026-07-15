# Unbounded semilocal grading deformation

- **ID:** semilocal-grading-deformation-unbounded
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Scientific status:** CANDIDATE NEW SCIENTIFIC KNOWLEDGE, provisional pending independent review
- **Parent source:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2
- **Inputs:** `semilocal-all-even-jacobi-prolate-residue-tower.md`;
  `semilocal-prolate-control-deformation.md`

## Statement

Fix a prime `p`. Let `theta_p` be the exact source Sonin isomorphism. There is no bounded operator
`Khat_p` for which

`theta_p^(-1)N_ptheta_p=N_infinity+Khat_p`                  (0)

as an equality of closed operators with domain `Dom(N_infinity)`. Equivalently, the formal grading
deformation from the transported prolate control to the genuine semilocal cyclic grading has no
bounded-perturbation realization.

More precisely, let

`G_p(s)=|1-p^(-1/2)exp(i log(p)s)|^(-2)`

be the inverse Euler metric on the archimedean cyclic spectral line. The commutator form

`[N_infinity,G_p]`

is unbounded. If `p_n` is the positive-leading-coefficient archimedean orthonormal Jacobi basis, there
are constants `0<c_p<=C_p` such that for every `k>=1`,

`c_p k^(1/4)<=|<p_0,[N_infinity,G_p]p_(2k)>|<=C_p k^(1/4)`. (1)

Consequently the ground-row smoothing

`P_0[N_infinity,G_p](N_infinity+1)^(-alpha)`                (2)

extends boundedly--and then is rank-one trace class--if and only if `alpha>3/4`.

The bounded-perturbation no-go follows from metric self-adjointness of the pulled-back semilocal
number operator.

## Quantitative Euler matrix coefficient

Put `r=p^(-1/2)`, `ell=log p`,

`phi(t)=cosh(t)^(-1/2)`,

`c_n=sqrt((2n)!)/(2^n n!)`.

The Poisson expansion and the all-even archimedean transform law give

`|<p_0,G_pp_(2k)>|
 =2c_(2k)/(1-r^2)
   sum_(m>=1) r^m phi(m ell)tanh(m ell)^(2k)`.              (3)

Every term is positive after removal of the common sign `(-1)^k`.

Choose

`m_k=ceil(log_p(sqrt(8k)))`.

Then

`8k <= p^(2m_k) < 8p^2k`.                                  (4)

Writing `x=p^(m_k)`,

`tanh(m_k ell)=(x^2-1)/(x^2+1)
 >=1-2/x^2 >=1-1/(4k)`.

Bernoulli's inequality gives

`tanh(m_k ell)^(2k) >=1/2`.                                (5)

Moreover `cosh(log x)<=x` for `x>=1`, so

`r^(m_k)phi(m_k ell)>=p^(-m_k)>=(p sqrt(8k))^(-1)`.         (6)

The central-binomial/Wallis bound gives

`c_(2k)>=c k^(-1/4)`                                       (7)

for an absolute constant `c>0`. Keeping only the `m_k` term in (3) and using (5)--(7) yields

`|<p_0,G_pp_(2k)>|>=c'_p k^(-3/4)`.                        (8)

For the reverse bound, use

`phi(m ell)<=sqrt(2)p^(-m/2)`

and

`tanh(m ell)^(2k)<=exp(-4k p^(-2m))`.

Thus the sum in (3) is at most a constant times

`sum_(m>=1)p^(-m)exp(-4k p^(-2m))`.

After writing `u_m=sqrt(k)p^(-m)`, this becomes

`k^(-1/2)sum_(m>=1)u_m exp(-4u_m^2)`.

The last sum is uniformly bounded in `k`: below `u=1` it is a geometric tail, and above `u=1` it
decays superexponentially along the geometric lattice. The upper Wallis bound
`c_(2k)<=Ck^(-1/4)` therefore gives

`|<p_0,G_pp_(2k)>|<=C'_p k^(-3/4)`.                        (9)

Together, (8)--(9) prove the sharp two-sided order.

## Unbounded commutator

On the algebraic number-operator domain, use the commutator form

`q_G(f,g)=<N_infinity f,G_pg>-<f,G_pN_infinity g>`.

Since `N_infinity p_0=0` and `N_infinity p_(2k)=2k p_(2k)`, equations (8)--(9) give

`|q_G(p_0,p_(2k))|
 =2k|<p_0,G_pp_(2k)>|
 asymp_p k^(1/4)`.

Both test vectors have norm one, so the form cannot be represented by a bounded operator. This proves
(1) and unboundedness of `[N_infinity,G_p]` in the bounded-commutator sense.

For (2), the coefficient on `p_(2k)` has magnitude comparable to

`k^(1/4)(2k+1)^(-alpha)asymp k^(1/4-alpha)`.

A ground-row operator is bounded exactly when this coefficient sequence lies in `ell^2`. The series

`sum_k k^(1/2-2alpha)`

converges exactly when `alpha>3/4`. Whenever bounded, the operator has one-dimensional range and is
therefore trace class. This proves the threshold.

## From the metric commutator to `K_p`

Let

`A_p=theta_p^*theta_p=G_p^(-1)`

up to an irrelevant positive normalization scalar, and pull the semilocal number operator back:

`Nhat_p=theta_p^(-1)N_ptheta_p=N_infinity+Khat_p`,

under the bounded-perturbation hypothesis (0).

Self-adjointness of `N_p` in the semilocal Hilbert space is equivalent to metric self-adjointness

`Nhat_p^*A_p=A_pNhat_p`.                                   (8)

If `Khat_p` were bounded, (8) would give the bounded commutator identity, in form sense,

`[N_infinity,A_p]=A_pKhat_p-Khat_p^*A_p`.                  (9)

Thus `A_p` would belong to the bounded `C^1` domain of the derivation by `N_infinity`. The inverse of
a bounded invertible `C^1` element is again `C^1`, with

`[N_infinity,A_p^(-1)]
 =-A_p^(-1)[N_infinity,A_p]A_p^(-1)`.

Since `A_p^(-1)=G_p`, this would make `[N_infinity,G_p]` bounded, contradicting (1). Therefore no
bounded `Khat_p` satisfying (0) exists.

## Lean formalization

Formalized in:

- `formal/GaloisForLFunctions/RHTower/SoninSemilocalGradingDeformation.lean`
- `formal/GaloisForLFunctions/RHTower/SoninSemilocalGradingBounds.lean`
- `formal/GaloisForLFunctions/RHTower/SoninSemilocalGradingNoGo.lean`

The theorem surface is:

- `abs_semilocalOnePrimeEvenJacobiCoefficient_eq_magnitudeSeries`: exact positive series (3);
- `exists_semilocalOnePrimeMatchedDilation`: matched prime dilation (4);
- `tanh_nat_mul_log_prime_pow_lower_of_matched` and
  `semilocalOnePrimeRawMagnitude_lower_of_matched`: estimates (5)--(6);
- `semilocalArchimedeanJacobiNormalization_pow_four_bounds`: Wallis estimate (7);
- `abs_semilocalOnePrimeEvenJacobiCoefficient_sharp_order`: literal two-sided
  `k^(-3/4)` coefficient order (8)--(9);
- `abs_semilocalOnePrimeGroundCommutatorRow_sharp_order` and
  `semilocalOnePrimeGroundCommutatorRow_unbounded`: (1) and unboundedness;
- `summable_semilocalOnePrimeGroundRowSmoothedSquare_iff`: exact threshold (2);
- `semilocalOnePrimeGroundRowOperator_isTraceClass`: the bounded row is represented by a
  rank-one trace-class operator;
- `no_semilocalOnePrime_boundedPerturbationRealization`: the inverse-metric commutator identity
  rules out every bounded perturbation satisfying the stated metric self-adjointness and Jacobi-row
  identities.

The main declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Attack and limits

- `[PROVED]` The arithmetic grading deformation has no bounded-perturbation realization relative to
  the transported prolate control.
- `[PROVED]` The obstruction is quantitative and comes from optimally matched prime-dilation
  frequencies `p^(2m)asymp k`, not from one low Jacobi coefficient.
- `[PROVED]` The exact ground-row smoothing threshold is `alpha=3/4`; at and below it even the first
  row is unbounded, while above it that row is rank-one trace class.
- `[PROVED]` No numerical experiment, zero data, or RH assumption enters the proof.
- `[CLOSED SHORTCUT]` Bounded-perturbation and bounded Kato--Rellich arguments cannot construct the
  genuine semilocal prolate operator from the transported control.
- `[OPEN CORE]` Failure of bounded realization does not mean uncontrollable. The live possibilities
  are a newly constructed relative graph/domain relation or a two-resolvent Schatten estimate for the
  formal grading difference.
- `[OPEN CORE]` The theorem does not decide self-adjoint extension, Sonin reduction, or cancellation
  of the control corner.

## Novelty and significance audit

- **Proof gate:** complete above; all inequalities are explicit.
- **Significance gate:** passed provisionally. The parent paper leaves the semilocal prolate operator
  formal because of its domain problem. This theorem proves that the missing domain analysis cannot be
  removed by treating the genuine grading as a bounded perturbation of the canonical transported
  control.
- **Parent-theory gate:** the Euler metric, Jacobi grading, and nonunitarity of `theta_p` are SEARCH.
  The quantitative commutator lower bound and its consequence for `K_p` are the claimed result.
- **Literature gate:** targeted searches of the parent paper, its q-series sequel, and semilocal
  prolate/operator-algebra literature found no theorem asserting this unbounded grading deformation or
  the `k^(1/4)` commutator lower bound.

Scientific novelty remains provisional pending independent proof and literature review.
