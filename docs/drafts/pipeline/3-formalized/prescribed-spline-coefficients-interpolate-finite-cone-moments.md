# Prescribed spline coefficients interpolate finite cone moments

- **ID:** SC2-finite-prescribed-spline
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** SC2; prescribed-coefficient cone obstruction.
- **Statement:** Every finite set of positive two-prime cone frequencies admits
  arbitrary sufficiently small complex moments at distinct heights, with exact
  coefficients `(sinh z/z)^8` and multiplicity one.

## Exact theorem

Let `p != q` be primes, `delta>0`, and `S` a finite set of distinct positive
numbers `m log p+n log q`, with natural `m,n`. Put `F(z)=(sinh z/z)^8`.
There exist `n>=1` and `C,H_0,epsilon>0`, independent of `H` and the target,
such that for every `H>=H_0` and every complex vector `r` satisfying

`|r_t| <= epsilon*n/H^8` for every `t in S`,

there are distinct `gamma_1,...,gamma_n` in `[H,H+C]` satisfying

`sum_j F(delta+i gamma_j) exp(i t gamma_j)=r_t` for every `t in S`.

The more general theorem only needs distinct positive frequencies and a
positive lower bound for `|t+8-2j|`, `0<=j<=8`. It requires no separation
between shifted pairs of frequencies.

## Proof

Write `A_delta(x)=sinh(delta+i x)^8`, `v_t(x)=A_delta(x) exp(i t x)`,
and `g_t=v_t'`. The reciprocal numerator has the convergent expansion

`1/A_delta(x)=256 exp(-8 delta) exp(-8 i x)
               * (1-exp(-2 delta) exp(-2 i x))^(-8)`.

Termwise integration gives a bounded negative-frequency primitive `h_s`
with `h_s'=-exp(-i s x)/A_delta(x)`. Integration by parts gives

`integral g_t h_s = integral exp(i(t-s)x) + endpoint error`.

The conjugate pairing instead contains

`exp(i(t+s)x) ((u-r)/(1-r*u))^8`,

where `u=exp(2 i x)` and `r=exp(-2 delta)`. Its frequencies are positive;
a bounded primitive controls its integral uniformly in translation.
Consequently the continuous real Jacobian associated with

`P(y)(x)=2 Re sum_s h_s(x)y_s`

approaches the identity as the averaging interval grows. Explicit derivative
bounds control replacement of the integral by a fine equally spaced grid.

Choose spacing `h=pi/(2 Lambda)` so the grid error is at most `1/8`.
Choose a parameter radius `rho>0` so `|P(y)(x)|<=h/4` and the nonlinear
numerator error is at most `1/8` on that ball. The numerator has only the
nine frequencies `t+8-2j`. Their nonzero gap gives an exact geometric-sum
bound for the baseline residual. Increasing the number of nodes makes both
this residual and the continuous Jacobian error small enough.

Place the grid at `x_j=H+h+jh`. The exact denominator normalization
`q_H(x)=H^8/(delta+i x)^8` satisfies, on `[H,H+C]`,

`|q_H-1|<=8(C+delta)/H`, `|q_H'|<=8/H`.

Taking `H_0` sufficiently large therefore makes the normalized exact map

`M_H(y)_t=(H^8/n) sum_j F(delta+i(x_j+P(y)(x_j)))
                              exp(i t(x_j+P(y)(x_j)))`

satisfy `|M_H(0)|<=rho/4` and have Lipschitz defect from the identity at most
`1/2` on the closed parameter ball. The closed-ball inverse theorem covers
every target of norm at most `rho/4`. Quarter-spacing displacement keeps
nodes distinct and inside `[H,H+(n+1)h]`. Set `epsilon=rho/4`.

Finally, `t+8-2j` cannot vanish on the positive prime cone. Exponentiation
would equate a rational number to a nonzero integer power of `e`; the zero
integer-shift case follows from prime factorization. A uniform gap over the
whole cone follows because only finitely many cone times lie below nine.

## Uniform growth on prime-cone windows

For `0<d<D`, `C_0>=1`, and square windows `N_k=ceil(C_0*8^k)`, the same
interpolation witnesses can be chosen uniformly for `d<=delta<=D` with

`n_k, C_k, H_{0,k}, 1/epsilon_k <= U*R^k`

for fixed `U>0`, `R>1`. The numerator, reciprocal numerator, and dual-primitive
bounds are uniform on this strip. A window of cardinality `m`, frequency radius
`L`, and separation `sigma` has common scalar envelope

`X=V*(m+1)^2*((L+9)^2+1/sigma)`.

The explicit parameter choices give costs `O(X^6)`, `O(X^5)`, `O(X^9)`, and
`O(X^3)`, respectively. Baker's theorem bounds inverse separation polynomially
in `N`; cardinality and radius are also polynomial. Substituting the geometric
cutoffs proves the claimed common geometric bound.

## Formalization and scope

Namespace `GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments`:

- `SplineFiniteCorrection.lean`:
  `exists_prescribed_spline_finite_correction` and
  `exists_two_prime_prescribed_spline_finite_correction`.
  `exists_prescribed_spline_finite_correction_data` retains the explicit
  parameter formulas for these same interpolation witnesses.
- `SplineDiscreteJacobian.lean`:
  `norm_spline_discrete_jacobian_defect_le` and
  `exists_spline_correction_parameters`, including explicit parameter
  formulas and an upper bound on the number of nodes.
- `SplineQuantitativeCorrection.lean`:
  `exists_prescribed_spline_correction_polynomial_bound`.
- `SplineWindowBounds.lean`: `finite_spline_data_le_window_envelope`.
- `SplineConeWindowCosts.lean`:
  `exists_two_prime_spline_geometric_corrections`.
- `SplineWeilCoefficient.lean`: `cubicSpline_Wsummand` identifies the exact
  prescribed coefficient against zeta's spline `Wsummand`.

Direct `lake --old env lean` audits pass. Transitive axiom reports contain
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports are wired.

This finite theorem supports the formalized
[exact-coefficient cone construction](two-prime-cone-prescribed-spline-weights.md).
The assertion about actual zeta zeros remains open.
