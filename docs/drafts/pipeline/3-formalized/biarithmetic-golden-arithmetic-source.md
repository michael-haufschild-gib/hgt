# The actual golden arithmetic source reduces to one geometric tower

- **ID:** biarithmetic-golden-arithmetic-source
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** Reading the damped inverse of the actual ACS golden zeta series on the prime-five norm lattice gives a source with absolutely convergent mean for every real `0<=t<=1`. Its complete complex paid ideal equals that of the primary geometric tower.

## Exact source and proof

Put `alpha=(5+sqrt(5))/2`, `beta=(5-sqrt(5))/2`, `a=alpha*t`, `b=beta*t`.
Define `c_t(5^r)` to be the real part of coefficient `r` of the already verified formal
inverse `goldenInverseSeriesAt t`, and set `c_t(n)=0` off powers of five, including zero.
The actual ACS root sum and difference identify its roots with these two real numbers.
The constant coefficient is one, and every positive coefficient is
`-(a^r-b^r)/sqrt(5)`. Therefore, at every natural index,

`c_t=delta_1-(1/sqrt(5))*I_a+(1/sqrt(5))*I_b`.

For `0<=t<=1`, both towers have absolutely convergent means because
`0<=a<=alpha<5` and `0<=b<=beta<sqrt(5)`. The secondary tower is critical Wiener by the
exact geometric-tower criterion. So is the unit source; hence
`d=delta_1+(1/sqrt(5))*I_b` is critical Wiener and has a uniformly bounded receiver.
The exact paid-perturbation and nonzero-scalar laws now give `P(c_t)=P(I_a)`.
All source hypotheses in this application follow from the displayed parameter interval.
The same absolutely convergent tower sums give the actual mean
`m_t=(5-6t+t^2)/(5-5t+t^2)=1/Z(t/5)`: use `alpha+beta=5`, `alpha*beta=5`,
and `alpha-beta=sqrt(5)` to simplify the sum of the three means. In particular the
mean is one at `t=0` and zero at `t=1`. This is also the residue normalization required
by the separate intrinsic counting model.

The exact admission threshold is separately formalized in
`biarithmetic-golden-source-admission.md`.

## Scope

This compares the ordinary-integer divisor-prefix receivers of the norm-lattice
coefficients. It does not identify them with the different intrinsic generalized-integer
counting receiver. The exact tower-digit theorem gives the primary receiver at every
horizon. Detailed growth, all normalized Gram tangents, and the complete ideal classification still
require their separate analytic proofs.

- [x] Dependency-closed paper proof, actual-series definition, and parameter bounds.
- [x] Lean coefficient lift, real root identities, exact mean, and paid-ideal equality; six clean scratch axiom audits.
- [x] Direct repository check of `GoldenArithmeticSource.lean` and umbrella import.
- [x] Six main declarations transitively audited: only `propext`, `Classical.choice`, and `Quot.sound`.

Main declarations: `golden_root_bounds`, `goldenArithmeticSource_eq_towers`,
`golden_remainder_criticalWiener`, `summable_abs_goldenArithmeticSource_div`,
`goldenArithmeticSource_mean`, and `paidIdeal_goldenArithmeticSource`.
