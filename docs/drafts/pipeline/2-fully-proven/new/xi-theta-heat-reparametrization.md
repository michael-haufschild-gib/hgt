# The completed source returns exactly to shifted heat coordinates

- **ID:** xi-theta-heat-reparametrization
- **Stage:** 2-fully-proven
- **Type:** THEOREM / COMPOSITE TRANSFORM BRIDGE, [PROVED HERE]
- **Date:** 2026-07-10
- **Lean:** formal/GaloisForLFunctions/RHTower/XiThetaHeatReparametrization.lean
- **Parents:** xi-theta-critical-log-translation-seam.md,
  xi-theta-reader-superexponential-conditioning.md

## Medalist correction

The direct assertion that a square-rate Laplace reader acts on the completed critical trace is
false: the critical trace is Fourier in log x. But this does not imply that Laplace readers are
irrelevant. Inverse Fourier recovers the positive logarithmic source, and a second exact coordinate
change may return it to the heat variable.

The fixed-index audit is decisive. Perron fixes m before contour depth tends to infinity. Therefore
the exp(pi m squared) condition number is a finite constant and is not by itself fatal.

## Definitions

For a real logarithmic profile f define

T(f)(y)
  = (1/2) exp(-log(1+y)/4) f(log(1+y)),    y >= 0.           (1)

For the m-th square rate put

e_m(y)=exp(-pi m^2 y),

e_m^shift(y)=exp(-pi m^2)e_m(y).                            (2)

## Theorem A [PROVED]: exact atom-level composite bridge

For every m and y at least zero,

T(thetaSquareLogAtom_m)(y)=e_m^shift(y).                    (3)

For y greater than zero the same identity holds with the strict positive-half atom.

### Proof

Substitute u=log(1+y) into

thetaSquareLogAtom_m(u)=2 exp(u/4)exp(-pi m^2 exp u).

The normalization in (1) cancels 2 exp(u/4), while exp(log(1+y))=1+y. The result is

exp(-pi m^2(1+y))
  = exp(-pi m^2)exp(-pi m^2 y).

The endpoint y=0 is excluded only for the strict indicator convention; it is measure zero.

## Theorem B [PROVED NEW]: conditioning is exactly the boundary shift

For every y,

exp(pi m^2)e_m^shift(y)=e_m(y).                             (4)

Thus the lower bound exp(pi m squared) from the conditioning theorem is not an unexplained new
archimedean wall. It is exactly the scalar required to move the heat domain from x greater than one
back to y=x-1 greater than zero.

## Theorem C [PROVED NEW]: intrinsic Jacobian-weighted Hilbert norm

For every real logarithmic profile f,

integral_(y>0) |T(f)(y)|^2 dy
  = (1/4) integral_(u>0) exp(u/2)|f(u)|^2 du.                (5)

### Proof

The map y=exp(u)-1 is an injective differentiable equivalence of the positive half-line with
Jacobian exp(u). The square of the normalization in (1) is

(1/4)exp(-u/2).

Multiplying by the Jacobian gives exactly (1/4)exp(u/2).

Equation (5) identifies the non-artificial Hilbert topology required by the composite route:
T is one half of an isometry from the logarithmic source weighted by exp(u/2) to ordinary heat L2.
No reader-existence or change-of-measure Prop remains.

## Consequence for the Blaschke route

The direct pipeline

critical trace -> Laplace reader

remains falsified. The composite pipeline

critical trace
 -> inverse logarithmic Fourier
 -> positive source
 -> T
 -> shifted heat exponentials
 -> multiplication by exp(pi m squared)
 -> Laplace/Hardy reader

is atomwise exact.

This reopens the square-rate reader as a fixed-index route. What remains is not a variable mismatch
but the functional-analytic composition.

## What fails before what works

- [FALSIFIED] The Blaschke probe directly pairs with the completed critical trace.
- [FALSIFIED] Superexponential conditioning alone kills a Perron argument that fixes m first.
- [PROVED] Inverse log-Fourier followed by T produces exactly the shifted heat atom.
- [PROVED] The condition-number factor exactly removes the boundary shift.
- [PROVED] The source-to-heat map has the exact intrinsic weighted Hilbert norm (5).
- [OPEN CORE] Construct the infinite square-rate biorthogonal reader through the half-plane
  Paley-Wiener isometry, then calculate its reflected/Perron charge.

## Novelty and significance gate

- **Bridge ingredients:** logarithmic Fourier inversion, heat exponentials, and coordinate changes
  are parent theory.
- **Novel project statement:** equations (3)-(4) identify the exact missing seam between the
  completed critical source and the previously disconnected square-rate reader. They also explain,
  rather than merely bound, the exp(pi m squared) condition number.
- **Significance:** a route retired for the wrong reason is restored in a precise composite form,
  while the genuinely missing functional-analytic theorem is isolated.

## Gates

- [x] 0 -> 1: direct-versus-composite transform distinction isolated.
- [x] 1 -> 2: atom reparametrization and boundary normalization proved.
- [x] 2 -> 3: formalized and axiom-audited.
- [ ] 3 -> 4: requires the Paley-Wiener composite reader and Perron composition.
