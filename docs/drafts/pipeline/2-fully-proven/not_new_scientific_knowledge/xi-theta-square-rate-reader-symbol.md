# Explicit infinite square-rate reader symbol

- **ID:** xi-theta-square-rate-reader-symbol
- **Stage:** 2-fully-proven
- **Type:** BRIDGE THEOREM / EXACT INFINITE INTERPOLATION, [PROVED]
- **Date:** 2026-07-10
- **Lean:** formal/GaloisForLFunctions/RHTower/XiThetaSquareRateReader.lean
- **Parents:** xi-theta-heat-reparametrization.md, xi-theta-heat-node-singularity.md

## Constraint

The compactified heat nodes accumulate at zero, so no symbol holomorphic across a connected
compactified domain can carry the infinite Kronecker-delta data. The surviving construction must
move the accumulation point to infinity and interpolate the square rates there.

## Canonical rate-plane symbol

In the dimensionless rate variable define

B(z) = sin(pi sqrt(z)) / sinh(pi sqrt(z)).                  (1)

The quotient is independent of the sign of the square root. On the principal slit plane it is the
canonical product quotient

B(z) = product_(m>=1) (m^2-z)/(m^2+z).                     (2)

For every positive integer n,

B(n^2)=0,

B'(n^2)=(-1)^n pi/(2n sinh(pi n)) != 0.                    (3)

Indeed, sqrt(n squared)=n, the numerator is sin(pi n)=0, the denominator is nonzero, and the
chain and quotient rules give (3).

## Exact infinite reader symbol

Let

Q_n(z) = B(z)/(B'(n^2)(z-n^2)),                            (4)

with the removable value Q_n(n squared)=1. Equivalently, Q_n is the inverse node slope times the
analytic difference quotient of B at n squared. Then

Q_n(n^2)=1,

Q_n(m^2)=0 for every m != n.                               (5)

There is no finite cutoff in (5). The one formula annihilates the entire square spectrum. In the
physical heat-rate variable lambda_m=pi m squared, set

R_n(s)=Q_n(s/pi).                                          (6)

Then R_n(lambda_n)=1 and R_n(lambda_m)=0 for every m not equal to n. Thus the exact heat atoms
produced by the logarithmic source reparametrization now have an explicit infinite rate-plane
interpolation symbol, with no reader-existence proposition.

## Attack verdict

- [FALSIFIED] Only finite Lagrange or finite Blaschke probes are available.
- [PROVED] The square spectrum has a closed-form, fixed-index, exact infinite interpolation symbol.
- [PROVED] Its node derivative is nonzero, so normalization is canonical rather than chosen.
- [NOT YET CLAIMED] The symbol has already been realized as an L2 source-side functional inside the
  current Lean library.

## Novelty and significance gate

The sine/sinh canonical-product quotient is classical and is not claimed as new mathematics. The
project advance is an execution bridge: it composes the exact theta heat rates with a concrete
infinite symbol and removes the symbol-existence interface. The new-knowledge claim remains the
forced compactified-boundary singularity in the parent theorem.

## Open core

[OPEN CORE] Prove the physical symbol is in the right-half-plane Hardy class with boundary norm
`sqrt(2/pi) sinh(pi n)`, construct its Paley-Wiener L2 representative, and transport that
representative through the critical trace and reflected balanced-Perron seam.

## Gates

- [x] 0 -> 1: rate-plane category selected by the compactified-node obstruction.
- [x] 1 -> 2: explicit symbol, simple node slope, and infinite delta interpolation proved.
- [x] 2 -> 3: interpolation surface formalized without an existence proposition.
- [ ] 3 -> 4: requires the Hardy/Paley-Wiener representative and reflected Perron charge.
