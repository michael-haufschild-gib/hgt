# P-G154: Prime--Gamma exterior reflection projector

## Status

In progress. Route P, hard producer seam.

## Question

Can the global four-leg prime--Gamma determinant be dephased before scalarization so that its
cross-zero Cauchy--Binet minors collapse exactly to critical-line reflection pairs, and can a
source-Cayley resolvent then supply the forced transverse Green normalization without charging
critical-line zeros?

## Prior obstruction

The unphased exterior determinant contains all Cauchy--Binet cross minors. The already-formalized
Ward--Green exterior packet instead inserts `1 / Im z` after passing to individual zeros. That
gives a sharp RH quantum but leaves no direct prime--Gamma estimate of the packet-local energy.

## Conjecturing loop

### C1: dephase the global determinant by one common phase

Failed. A common bilinear phase selects pairs whose phase product is one, but the two prime clocks
do not send a zero and its critical-line reflection to inverse phases.

### C2: orient determinant rows oppositely in prime time and equally in Cayley time

Live. Give first determinant row prime phases `(z₂^a,z₃^b)` and second row their conjugates, while
giving both rows the same horizontal Cayley phase `u^c`. Cesaro survival conditions become

`z₂(rho)=z₂(sigma)`, `z₃(rho)=z₃(sigma)`, and `u(rho)u(sigma)=1`.

Two-prime injectivity forces equal ordinates. Cayley injectivity then forces
`sigma = 1 - conj rho`. The two ordered surviving minors add to the square of the reflected
Pluecker coordinate; since that coordinate is purely imaginary, the negative dephased determinant
is its positive norm square. Critical-line fixed points contribute zero identically.

### C3: divide by the Cayley reflection gap

Refined. Direct division by `u(rho)-u(1-conj rho)` is not itself a finite source polynomial. For
`x = 2 Re rho - 1`, `y = 1/2 - Re rho`, and
`u=(x-i)/(x+i)`, the exact identity is

`1/y = 2 i (1-u)/(1+u)`.

For `0 <= R < 1`, replace `(1+u)^{-1}` by the convergent source-Cayley geometric orbit
`sum_{k>=0} (-R u)^k`. First dephase each fixed `R`; then send `R` to one. On-line poles are
removable after exteriorization because the reflected Pluecker coordinate is already zero there.

## Target theorem chain

- [x] exact finite exterior determinant Cauchy--Binet expansion with oriented phase rows;
- [x] three-clock Cesaro projector onto reflection pairs;
- [x] ordered reflected minors equal negative Pluecker norm square;
- [x] Abel/Cayley resolvent limit equals exact transverse-normalized exterior packet energy;
- [x] every finite approximant is an explicit prime--Gamma four-leg source expression;
- [ ] absolute source bound below `4 * (96 / 145)^2`;
- [ ] unconditional closed Lean proof of RH.

## Novel knowledge audit

If proved, C2 is not repackaging an existing zero-side detector: it removes the documented global
cross-minor contamination at source level by a mixed covariance law (contragredient prime clocks,
covariant Cayley clock). C3 identifies the Ward Green pole as the boundary value of a regular
Cayley-source resolvent, with exterior vanishing providing the exact removable-kernel mechanism.

## Verification gates

- [x] `lake env lean formal/GaloisForLFunctions/RHTower/HedenmalmPrimeGammaExteriorReflectionProjector.lean`
- [x] `lake build GaloisForLFunctions.RHTower.HedenmalmPrimeGammaExteriorReflectionProjector`
- [x] `#print axioms` audit
- [x] umbrella import
