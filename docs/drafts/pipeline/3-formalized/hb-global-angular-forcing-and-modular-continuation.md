# HB full angular forcing and modular continuation

Stage: formalized in Lean 4; final leaf audit pending. Type: `[BRIDGE]`.
RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical
causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

The complete mixed Einstein source has the sufficient angular equation
`(Delta-L)H=(L/2)S²`, where `L=(2s+1)(2s+2)`. The two physical parameters are
`s=rho-2` and `s=-rho-1`. The existing complete mixed-source proof establishes that
both values of L are nonreal at every actual Xi occurrence rho. This card closes
the full forcing's L² admission and the scalar field's missing modular inversion
at those occurrences. Construction of the global response remains open.

## Literal full source and its cusp subtraction

Set `u=rho-1/2` and write the original full scalar cusp field as `S=P+T`, where

```
P(u,y) = Lambda(2u)*y^(1/2-u) + Lambda(1+2u)*y^(1/2+u)
T(u,x,y) = 2*(positive signed scalar tail + negative signed scalar tail).
```

Both signed tails are the original infinite arithmetic Fourier–Bessel series.
The centered cusp parameter u differs from the corpus's rotated `xiSpectralPoint`.

For y≥l>0, the actual integral Bessel bound implies, with n=N+1,

```
|K_nu(2*pi*n*y)| ≤ besselBound(nu,l)*exp(-n*l/2)*exp(-y/2).
```

Here `n*y ≥ (n*l+y)/2`, and `besselBound(nu,y)` decreases with y. Multiplication
by the original coefficients and summation against their proved exponential
majorant gives

```
|value(u,nu,a,d,sign,x,y)| ≤ C(u,nu,d,l)*y^a*exp(-y/2),
C = besselBound(nu,l)*sum_N |coefficient(u,d,N)|*exp(-(N+1)*l/2).
```

The bound is uniform in x. Multiplication by any complex height power shifts the
real exponent; the resulting power times exp(-y/2) tends to zero and is bounded
on the remaining compact interval. Therefore every complex-power-weighted tail
is bounded on the half-strip. The exact identity

`S²-P²=2*P*T+T²`

then bounds the complete squared-source remainder, including all cross terms.

Use the already constructed differential cusp-power response H0 with its actual
amplitude L/2 and both actual Weyl coefficients. It obeys
`(Delta-L)H0=(L/2)P²`. Set

```
chi(y) = Real.smoothTransition(y-2)
F = (L/2)*S² - (Delta-L)(chi*H0).
```

This is the literal differential expression: no transition-region derivative is
dropped. Above height 3, `F=(L/2)(S²-P²)`; below height 2, `F=(L/2)S²`.
The latter identity is proved by equality of local germs, including both actual
Laplacian derivatives. The smooth cutoff and full scalar regularity give
continuity of F on the positive-height chart.

The Hilbert measure is exactly `UpperHalfPlane.volume.restrict ModularGroup.fd`,
using the invariant hyperbolic volume. Its finiteness is proved in the corpus's
`HTGeometry.ModularFundamentalDomainVolume`. The modular cell lies above height
1/2. A compact rectangle controls its portion below height 4; the full-tail bound
controls the rest. Thus F is bounded on the entire cell and belongs to its L²
space. `forcingVector` is constructed from this actual `MemLp` proof, and
`forcingVector_coe` identifies its representative with F almost everywhere.
No critical-line or supplied integrability hypothesis is used.

## Actual modular inversion at Xi parameters

The existing primitive-pair Poincare formula supplies inversion only in its
absolute-convergence chamber. Its equality with the full cusp series cannot be
applied directly at Xi parameters. The new continuation proof removes this gap.

Each arithmetic coefficient `n^u*sum_(d|n) d^(-2u)` is entire in u, as is the
Bessel order family. On a spectral ball |u|<R, the actual coefficient and Bessel
bounds give one summable majorant, uniform in u:

```
|coefficient| ≤ n^(3R+1)
|K_u(2*pi*n*y)| ≤ exp(-n*y)*exp(R²/(2y))*sqrt(2*pi/y).
```

Locally uniform convergence of the original series proves that T is entire in u.
Define

```
Q(u) = u*(2u-1)*(2u+1)
Ehat(u,z) = (2u+1)*Xi(2u)*y^(1/2-u)
          + (2u-1)*Xi(1+2u)*y^(1/2+u)
          + Q(u)*T(u,z).
```

Ehat is entire. For every nonreal u, it equals Q(u) times the original scalar
field. The proof uses the actual Xi/completed-zeta identity and Gamma nonvanishing
at nonreal arguments. This qualification matters: the literal Gamma-times-zeta
product is totalized at Gamma poles. Ehat supplies the continuation values there;
no global identification with that raw product is asserted.

In a neighborhood of `u=2+I`, the actual convergent Poincare representation and
its inversion law prove `Ehat(u,-1/z)=Ehat(u,z)`. The entire identity theorem
propagates this equality to all u. At every actual Xi occurrence, Im u is nonzero
and Q(u) is nonzero, so cancellation gives the original scalar's inversion law,
without a chamber or critical-line assumption.

The full residual F is horizontally periodic, including its differential cutoff
terms. It also matches under inversion wherever both chart heights are below 2.
This open overlap contains the compact circular modular seam. Thus the actual
cell source has the required matching identities. The height-dependent cutoff
response is not asserted to be globally invariant on the entire upper half-plane;
a constructed quotient extension and its operator domain remain separate work.

## Lean surface and validation

All modules are under `formal/GaloisForLFunctions/RHTower/`.

| Module | New public theorems | Proved surface |
|---|---:|---|
| `ThetaCuspHawkingBMAngularCuspBounds` | 3 | Full Bessel and tail height decay; weighted bounds |
| `ThetaCuspHawkingBMGlobalAngularForcing` | 10 | Full squared remainder; actual cutoff residual; boundedness; L² vector |
| `ThetaCuspHawkingBMAngularSpectralContinuation` | 3 | Entire arithmetic coefficients; locally uniform majorant; entire full tail |
| `ThetaCuspHawkingBMGlobalAngularModularity` | 7 | Entire normalized field and inversion; actual Xi inversion; residual seam laws |

All scratch checks passed without warnings using `lake env lean`. Final audit
status is pending. No experimental computation or numerical proof certificate is
used. Each finished leaf is imported once by RHTower; no umbrella build is needed.

## Remaining physical response obligation

Construct the quotient-compatible closed hyperbolic energy form and its dense,
injective embedding into this actual L² space. The existing Friedrichs-form
operator and nonreal resolvent results become applicable only after those actual
objects and properties are proved. Identify the weak operator with the literal
hyperbolic Laplacian, obtain the smooth global response, and prove its physical
causal prescription. Arbitrary cell boundary conditions or an assumed
self-adjoint operator cannot discharge this construction.

The complete SS/VV sectors, original left-QNM pairing, and independent fixed-clock
extinction law remain open. Neither source admission nor modularity proves RH.
