# Exponential-wall Hankel contraction law

- **ID:** ULF-EWHC-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor operator theorem
- **Parent:** `ULF-SCIN-001`
- **Statement:** literal prime-mixed Stokes formation lands at a positive trace-one strict
  contraction whose Burnol supersymmetric partner has kernel `24rs/(1+r+s)^4`.

## 1. Why this theorem matters

The wall landing in `ULF-SCIN-001` was known to be nuclear with integral trace, but nuclearity
alone gives no sub-unit control. The corpus's exact two-copy coherence value supplies a stronger
law: the whole infinite-rank formation operator has operator norm strictly below one before any
zero or divisor is supplied.

This is a direct sub-unit source anchor, not amplification and not an assumed positivity. It does
**not** identify the wall determinant with Xi; that identification is already false.

## 2. Source operator

Let

```text
mu(dx)=exp(-x) dx on (0,infinity),
kappa(x,y)=8(xy)^(3/2)/(x+y)^3,
(A f)(x)=integral kappa(x,y) f(y) mu(dy).              (EWHC.1)
```

Under exponential quantile transport, `A` is exactly the positive wall operator `A_0` of
`ULF-SCIN-001`. Hence

```text
A=A*,   A>=0,   A is Schatten-one,   Tr A=1.           (EWHC.2)
```

No spectral parameter occurs in `(EWHC.1)`.

## 3. Theorem A: exact Burnol partner

Define the feature and synthesis maps

```text
v_x(r)=2 x^(3/2) r exp(-xr),
(Vf)(r)=integral v_x(r)f(x)mu(dx).                     (EWHC.3)
```

Then `V` is Hilbert--Schmidt, `||V||_2^2=1`, and

```text
A=V*V.                                                 (EWHC.4)
```

Its opposite-order partner `B=VV*` acts on `L2((0,infinity),dr)` by the explicit weighted
Hankel kernel

```text
b(r,s)=24rs/(1+r+s)^4.                                 (EWHC.5)
```

Consequently `B` is positive Schatten-one, `Tr B=1`, and `A,B` have the same nonzero
eigenvalues with multiplicity. In particular their ordinary Fredholm determinants agree.

**Proof.** Direct Gamma integration gives

```text
integral_0^infinity |v_x(r)|^2 dr
 =4x^3 integral_0^infinity r^2 exp(-2xr)dr=1,
<v_x,v_y>=8(xy)^(3/2)/(x+y)^3=kappa(x,y).
```

Since `mu` is a probability measure, `V` is Hilbert--Schmidt with squared norm one, and the
Gram identity gives `(EWHC.4)`. Reversing the order gives

```text
b(r,s)
 =4rs integral_0^infinity x^3 exp(-(1+r+s)x)dx
 =4rs * 3!/(1+r+s)^4,
```

which is `(EWHC.5)`. Standard Hilbert--Schmidt product and cyclic spectral laws give the
remaining statements. QED.

## 4. Theorem B: exact strict contraction

The corpus proves the squared-coherence identity

```text
Tr(A^2)=||A||_2^2
 =integral integral kappa(x,y)^2 mu(dx)mu(dy)
 =16/35.                                               (EWHC.6)
```

Therefore

```text
||A||=||B|| <= 4/sqrt(35) < 1.                        (EWHC.7)
```

Thus `I-A` and `I-B` are boundedly invertible, with norm-convergent Neumann series. Moreover

```text
det(I-zA)=det(I-zB) != 0  whenever |z|<sqrt(35)/4,      (EWHC.8)
e_2(A)=(Tr(A)^2-Tr(A^2))/2=19/70.                      (EWHC.9)
```

**Proof.** Positivity and Schatten-one membership make `(EWHC.6)` the Hilbert--Schmidt norm
identity. Operator norm is bounded by Hilbert--Schmidt norm, and `16/35<1`. Neumann
invertibility and the zero-free Fredholm disc follow from `(EWHC.7)`. The second elementary
symmetric trace identity gives `(EWHC.9)`. QED.

## 5. Checked corpus locks

- `routePPrimitiveGammaJuliaStokesCofinalChildTraceClass` supplies positive nuclearity and trace.
- `integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq` supplies
  exact value `16/35`.
- `routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_two` independently gives `19/70`.
- `routePPrimitive_GammaJulia_Stokes_expWallXiTau_projectiveJetNoGo` rules out every scalar
  rescaling of wall tau germ to Xi tau germ.
- `routePPrimitiveGammaJuliaStokesWallSignedSquareQuadraticJet_ne_thetaCanonical` rules out fixed
  canonical theta/Xi jet identification.
- `RoutePPrimitiveGammaJuliaStokesApertureWallXiDivisorNoGo` proves exact wall/Xi divisor
  identification false.

## 6. Exact significance and limit

This theorem upgrades source object from “trace-one nuclear” to “trace-one strict contraction”
and places it on the same Burnol continuum used by prime collision budget. It therefore supplies
a canonical source resolvent `(I-A)^-1` and a zero-free determinant neighborhood larger than unit
disc.

It cannot by itself select RH. Direct conjugacy, scalar rescaling, and equality of its divisor
with Xi are closed by locks above. Any valid completion law must add a source-derived
theta/Poisson relative boundary operation which changes divisor-bearing operator while preserving
unsquared prime formation data and strict bound `(EWHC.7)`.

## 7. Lean status

Paper theorem only. Its analytic inputs are already Lean-proved; operator synthesis,
opposite-order kernel, and strict operator-norm corollaries are not yet packaged as one Lean
module.
