# Continuum prime towers retain a reflected Cholesky mode

- **ID:** continuum-prime-tower-reflection-cholesky
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Arithmetic Orientation Theory's finite KMS identity; TG source-orientation investigation.
- **Statement:** The complete half-line ratio-minus-product tower, plus one diagonal mass, is a sum of three nonnegative continuum energies.

## Goal

Transfer the lattice tower decomposition to actual continuum profiles without
replacing a reflected pairing by a square. This is a bridge, not a proof of
TG's all-prime residual sign. Its diagonal mass still needs shared payment.
No external novelty claim is made.

## Exact theorem and proof

Fix `L>=0`, `0<=r<=1`, and a continuous real function `F`, zero above
`(N+1)L`. Only its restriction to the nonnegative half-line is used. Put

```
M = integral_0^((N+1)L) F(x)^2 dx,
R = sum_(k=1)^N r^k integral_0^((N+1)L) F(x) F(x+kL) dx,
H = sum_(k=1)^(2N+1) r^k integral_0^(kL) F(x) F(kL-x) dx,
U_j(theta) = sum_(i=j)^N r^(i-j) F(theta+iL),  0<=theta<=L.
```

Then, writing squared norms for integration over `[0,L]`,

```
M + 2R - H = (1-r) ||U_0||^2
  + (r/2) ||U_0 - U_0(L-.)||^2
  + (1-r^2) sum_(j=1)^N ||U_j||^2 >= 0.
```

**[PROVED HERE].** Splitting each integral into cells of length `L`
gives `M+2R=integral_0^L (sum_i u_i^2 +
2 sum_k r^k sum_i u_i u_(i+k))`, where
`u_i=F(theta+iL)` vanishes for `i>N`. The finite KMS identity, proved
by telescoping `u_i^2+2r u_i U_(i+1)=U_i^2-r^2 U_(i+1)^2`, gives
`M+2R=||U_0||^2+(1-r^2)sum_(j=1)^N||U_j||^2`.

In `H`, partition `x=theta+iL`, with `0<=i<k`. Set `j=k-i-1`;
the other endpoint is `(L-theta)+jL`, and the weight is `r^(i+j+1)`.
Terms with either index above `N` vanish by the support condition.
The finite Cauchy product therefore gives
`H=r integral_0^L U_0(theta)U_0(L-theta) dtheta`.
The change of variables `theta -> L-theta` preserves `||U_0||^2`.
Expansion of the difference square proves the displayed decomposition.
All integrands are continuous on finite intervals; all sums are finite.
Every coefficient on the right is nonnegative.

The degenerate interval `L=0` gives zero on both sides. The same algebra
and coefficient signs include `r=0` and `r=1` without a limiting argument.

For a prime `p`, take `L=log p` and `r=p^(-1/2)`, and multiply by
`log p`. These are the literal critical prime-power weights, with the
ratio and reflected correlations both retained. A compact half-line test
has such a finite support bound for every `L>0`.

## Scope and remaining open core

The result charges one diagonal mass per prime. Summing it supplies no
uniform bound for the complete prime--Gamma--polar form. It is not counted
as a discharged TG positivity premise. The next proof must account for
the aggregate diagonal through the complete signed source.

## Gates

- [x] Well-posed, source-preserving continuum statement.
- [x] Dependency-closed paper proof.
- [x] Exact Lean theorems and transitive axiom audit.
- [x] Final direct source check.
- [x] Umbrella import; umbrella not compiled.

## Lean certificate

Module: `GaloisForLFunctions.ArithmeticOrientationTheory.ContinuumTowerReflectionCholesky`.

- `continuumTowerCrossing_eq_reflected_pairing`: exact reflected continuum pairing.
- `continuumTower_reflection_cholesky`: complete three-term decomposition.
- `continuumTower_compensated_nonneg`: positivity after the single diagonal payment.
- `continuumPrimeTower_eq`: equality with literal von Mangoldt prime-power weights.
- `continuumPrimeTower_compensated_nonneg`: unconditional prime-tower specialization.

The source-copy audit passed with `lake --old env lean` and `#print axioms`.
The decomposition, reflected-pairing identity, literal arithmetic equality,
and arithmetic positivity theorem depend only on `propext`,
`Classical.choice`, and `Quot.sound`. No new olean or raised limits were used.

Final command, exit 0 without warnings:

```
lake --old env lean GaloisForLFunctions/ArithmeticOrientationTheory/ContinuumTowerReflectionCholesky.lean
```

## Research assessment

The finite KMS identity was already in the corpus. The addition is its exact
continuum transfer, the reflected-fibre term, and the equality to the literal
von Mangoldt tower. This does not discharge TG's shared residual-area sign.
No new criterion or assumed analytic estimate was added. The remaining
research must attack the joint signed source payment, rather than treating
further regularity or a separate bound for each tower as the requested advance.
