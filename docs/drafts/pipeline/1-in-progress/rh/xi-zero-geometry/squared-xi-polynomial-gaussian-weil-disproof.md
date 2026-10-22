# Squared-Xi polynomial--Gaussian Weil disproof family

- **ID:** `squared-xi-polynomial-gaussian-weil-disproof`
- **Stage:** 1-in-progress
- **Type:** THEOREM / RH-COMPLETE FILTERED HEAT SOURCE REDUCTION
- **Scientific status:** `[PAPER COMPLETE CRITERION] [FILTERED ENDPOINT LEAN-FORMALIZED] [COMPLETENESS LEAN OPEN] [NO NEGATIVE SOURCE VALUE YET]`
- **Parent:** `squared-xi-parabolic-heat-trace-disproof.md`
- **Statement:** RH is equivalent to nonnegativity of every polynomial-square Gaussian trace on
  the multiplicity-exact squared centered Xi divisor.  If RH is false, one real polynomial cancels
  the entire lower finite packet and the Gaussian suppresses the remaining tail, producing a
  strict negative finite differential expression in the completed Gaussian prime/Gamma source.

## 1. Filtered heat trace

For each multiplicity copy `q`, put

```text
z_q=(rho_q-1/2)*(-i),       u_q=z_q^2.                    (1)
```

For `t>0` and `P in R[U]`, define

```text
H_(P,t)=sum_q P(u_q)^2*exp(-t*u_q).                      (2)
```

The existing unconditional strip and height estimates give the uniform sector

```text
Re(u_q) > |z_q|^2/2 > 0.                                 (3)
```

Consequently every series `(2)` is absolutely summable: polynomial growth is absorbed by half
of the Gaussian, and the other half is dominated by the already summable divisor
`sum_q |z_q|^(-2)`.

Critical-line reflection sends `u_q` to `conj(u_q)`.  Since `P` has real coefficients, `(2)` is
real unconditionally.

## 2. RH-positive direction

Under RH every `z_q` is a nonzero real number, hence every `u_q` is positive real.  Termwise,

```text
P(u_q)^2*exp(-t*u_q) >= 0,                               (4)
```

so `H_(P,t)>=0` for every real polynomial and every positive time.

Thus one strict negative value in `(2)` proves `not RiemannHypothesis`.

## 3. Completeness: every off-line orbit has a negative filtered heat witness

Assume RH is false and select a nonreal centered spectral point `alpha`.  Because its real part is
the nonzero zero ordinate and its imaginary part is the transverse displacement,

```text
u_0=alpha^2
```

is nonreal.  Let `A_0=Re(u_0)`.

By `(3)` and reciprocal-square summability, only finitely many distinct squared divisor values
have real part at most `A_0+1`.  Choose `delta>0` so that the finite conjugation-closed packet

```text
S={u_q : Re(u_q)<=A_0+delta}                             (5)
```

contains `u_0,conj(u_0)` and has no value with real part strictly between the boundary of `S` and
`A_0+delta`.

For each `t>0`, real Lagrange interpolation on the conjugation-closed set `S` gives
`P_t in R[U]` with

```text
P_t(u_0)= i*exp(t*u_0/2),
P_t(conj(u_0))=conj(P_t(u_0)),
P_t(u)=0                    for u in S\{u_0,conj(u_0)}.  (6)
```

Every divisor copy above `u_0` or its conjugate then contributes exactly `-1` to `(2)`, while all
other copies in `S` contribute zero.

The Lagrange basis is fixed.  Hence there are constants `C,d`, independent of `t`, such that

```text
|P_t(u)| <= C*exp(t*A_0/2)*(1+|u|)^d.                    (7)
```

Outside `S`, `Re(u)>=A_0+delta`.  Combining `(3)` and `(7)` gives, for `t>=1`,

```text
|P_t(u_q)^2*exp(-t*u_q)|
 <= C^2*(1+|u_q|)^(2d)*exp(-t*(Re(u_q)-A_0)).            (8)
```

After one half of the gap `delta` is extracted, the remaining exponential is bounded by a
constant multiple of `|z_q|^(-2)`.  Dominated convergence and reciprocal-square summability show
that the tail in `(8)` tends to zero as `t->infinity`.

The finite packet contributes a fixed negative integer and the tail tends to zero.  Therefore

```text
exists t>0, exists P in R[U], H_(P,t)<0.                 (9)
```

This proves the exact criterion

```text
RiemannHypothesis
  <-> forall t>0, forall P in R[U], 0<=H_(P,t).          (10)
```

Strict negativity is open in `t` and in the finitely many coefficients.  Rational approximation
therefore reduces the disproof family to positive rational times and rational polynomials.

Lean now formalizes unconditional polynomial-weighted Gaussian summability, Schwarz reality, the
RH-positive direction, and the strict-negative RH-false endpoint in
`RHTower/XiGaussianHeatTraceDisproof.lean`.  The interpolation-plus-tail completeness direction is
still paper-only.

## 4. Completed source differential

Write

```text
P(U)^2=sum_(j=0)^D a_j U^j.                              (11)
```

Absolute convergence permits termwise heat differentiation, giving

```text
H_(P,t)=sum_(j=0)^D a_j*(-1)^j*d^j/dt^j Theta_Xi(t).    (12)
```

Substituting the completed Riemann--Weil Gaussian identity from the parent card turns `(12)` into
one finite differential expression in

```text
2*exp(t/4),   W_infinity(F_t),   Psi_prime(t).           (13)
```

All pole, Gamma, and prime-power terms remain inside the same differentiated completion.  A strict
negative value of this source expression is the required unconditional RH disproof.

## 5. Anti-theatre audit

- This is a complete filtered family, unlike the bare Gaussian trace: interpolation removes the
  finite low packet that can mask an off-line quartet.
- The completeness proof is a source-friendly restatement of Weil positivity, not itself a source
  sign.  It is not claimed as new scientific knowledge or as an RH disproof.
- Selecting `P_t` from an assumed off-line zero proves completeness but is not an admissible source
  producer.  The live direction must exhibit one rational `(P,t)` from `(12)--(13)` before reading
  the divisor.
- Separate estimates of the pole, Gamma, and prime pieces that destroy their cancellation remain
  invalid.
- Small time is protected for every fixed polynomial by the positive highest differentiated
  archimedean term.  A viable source attack must use a coupled degree/time scaling or a finite
  interior time.

## Open source core

`[CONJECTURE]` There is a positive rational `t` and a rational polynomial `P` for which the exact
completed differential expression `(12)--(13)` is strictly negative.

The first discriminator is a cancellation-preserving source representation of the full quadratic
coefficient form in `(12)`.  If it factors as a positive Gram for all `t`, this filtered Gaussian
coordinate is retired despite completeness; if it has an explicit negative source direction, that
direction is the RH-false witness.

## Gates

- [x] prove unconditional sector and absolute-summability mechanism on paper
- [x] prove Schwarz reality and RH-positive direction on paper
- [x] prove false RH produces a negative polynomial--Gaussian trace
- [x] reduce the family to rational times and rational polynomials
- [x] identify the exact finite differential of the completed Gaussian source
- [x] formalize polynomial-weighted Gaussian summability and Schwarz reality
- [x] formalize `negative filtered heat trace -> not RiemannHypothesis`
- [ ] formalize the completeness implication `not RH -> exists negative filtered heat trace`
- [ ] prove one strict negative completed source differential
