# Canonical H2 and L2 reader for the theta square-rate spectrum

- **ID:** xi-theta-square-rate-hardy-reader
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** BRIDGE THEOREM / CANONICAL PALEY-WIENER READER, [PROVED ON PAPER] [FORMALIZED]
- **Date:** 2026-07-10
- **Parents:** xi-theta-square-rate-reader-symbol.md,
  xi-theta-square-rate-boundary-energy.md
- **Lean gap:** closed.  The reader was built directly in `L²(0,∞)` as an orthogonal residual, so no half-plane Paley--Wiener surjectivity was needed.

## Statement

Let lambda_m=pi m squared and let R_n be the physical-rate interpolation symbol from the parent
proof. With the right-half-plane Hardy normalization

||F||_H2^2 = sup_(x>0) (1/(2pi)) integral_R |F(x+it)|^2 dt,

R_n belongs to H2 and

||R_n||_H2^2 = (2/pi) sinh(pi n)^2.                         (1)

Let PW be the unitary Laplace Paley-Wiener map from L2(0,infinity) onto this H2 space, and define
canonically

r_n = PW^(-1)(R_n).                                         (2)

Then

||r_n||_L2 = sqrt(2/pi) sinh(pi n),                          (3)

integral_0^infinity r_n(y) exp(-lambda_m y) dy
  = 1  if m=n,
  = 0  if m!=n.                                             (4)

Thus the shifted heat family from the completed theta source has the fixed-index coefficient
functional

C_n(f) = exp(lambda_n) integral_0^infinity r_n(y) f(y) dy,  (5)

and C_n(exp(-lambda_m)exp(-lambda_m y)) is the Kronecker delta at n.

## Proof

### 1. Factor the selected Blaschke zero

The rate sequence satisfies the half-plane Blaschke condition

sum_m lambda_m/(1+lambda_m^2) < infinity,

because lambda_m is pi m squared. Therefore

B_phys(s)=product_(m>=1) (lambda_m-s)/(lambda_m+s)

is an inner function on the right half-plane. Euler's sine and hyperbolic-sine products identify it
with the explicit parent symbol `B(s/pi)`. Write

b_n(s)=(lambda_n-s)/(lambda_n+s),

B_phys(s)=b_n(s) B_n(s),

where B_n is again inner. Since

b_n(s)=-(s-lambda_n)/(s+lambda_n),

the normalized reader is

R_n(s) = -B_n(s)/(B_phys'(lambda_n)(s+lambda_n)).             (6)

### 2. Uniform interior Hardy control

For x>0, innerness gives |B_n(x+it)|<=1. Hence

integral_R |R_n(x+it)|^2 dt
 <= |B_phys'(lambda_n)|^(-2)
    integral_R dt/((x+lambda_n)^2+t^2)
 = |B_phys'(lambda_n)|^(-2) pi/(x+lambda_n).                 (7)

The physical derivative has norm

|B_phys'(lambda_n)|=1/(2n sinh(pi n)).                       (8)

Using lambda_n=pi n squared, the right side of (7) is at most `4 sinh(pi n)^2`.
Thus R_n is in H2.

As x decreases to zero, B_n(x+it) tends to its unit-modulus boundary value for almost every t, and
(6) is dominated by the square-integrable Cauchy majorant

2n sinh(pi n)/sqrt(lambda_n^2+t^2).

Dominated convergence therefore recovers the exact boundary energy from the parent theorem:

sup_(x>0) integral_R |R_n(x+it)|^2 dt = 4 sinh(pi n)^2.

This proves (1).

### 3. Paley-Wiener transport

The half-plane Paley-Wiener theorem is a unitary identification when the H2 norm includes the factor
1/(2pi). Definition (2) therefore gives (3) without a choice of representative. Evaluation of a
Laplace transform at lambda_m is pairing with the heat exponential exp(-lambda_m y). The exact
interpolation identities for R_n give (4). Multiplying the output by the fixed scalar
exp(lambda_n) proves (5) for the boundary-shifted atoms.

## Attack verdict

- [PROVED PAPER] The explicit symbol has uniform interior Hardy control and the exact predicted H2
  norm.
- [PROVED PAPER] The source-side L2 reader is canonical as the inverse Paley-Wiener image; no reader
  existence proposition remains mathematically.
- [DISCHARGED] The superexponential boundary denormalization is a fixed scalar exp(lambda_n), applied
  after the L2 pairing, and is finite for every Perron-fixed n.
- [OPEN FORMALIZATION] Build the half-plane H2 and Paley-Wiener unitary surface in Lean, or connect an
  existing L2 Fourier unitary to the positive-support theorem.

## Novelty and significance gate

The Blaschke and Paley-Wiener ingredients are classical, so this is a bridge theorem rather than a
new-knowledge claim. It is structurally decisive for the project: the reader is now a named
canonical object with exact norm and exact heat pairings, leaving the reflected completed-source
charge rather than reader existence as the mathematical frontier.

## Open core

[OPEN CORE] Express C_n directly as a functional of the completed critical cosine trace and compute
its action on the reflected theta half inside the third-order balanced Perron seam.

## Gates

- [x] 0 -> 1: explicit rate-plane symbol and exact boundary energy proved.
- [x] 1 -> 2: interior H2 control, exact H2 norm, and canonical L2 reader proved on paper.
- [x] 2 -> 3: complete; see the Lean formalization section.
- [ ] 3 -> 4: requires the reflected balanced-Perron charge and final contradiction composition.

## Lean formalization (complete and unconditional)

Equation `(1)` was already in the tree.  The remaining items were formalized without the
half-plane Paley--Wiener surjectivity: the reader is constructed directly in `L²(0,∞)` as the
normalised orthogonal residual of one heat exponential against the closed span of all the others,
and its norm is computed in closed form.

- `formal/GaloisForLFunctions/RHTower/XiThetaSquareRateHardy.lean` — equation `(1)`
  (`normalized_csSup_integral_sq_norm_thetaHeatRateReaderSymbol_line`) and the interpolation
  identities `thetaHeatRateReaderSymbol_self` / `_other`.
- `formal/GaloisForLFunctions/HTGeometry/CauchyMatrixDeterminant.lean` — the Cauchy determinant
  over an arbitrary field (a mathlib gap).
- `formal/GaloisForLFunctions/HTGeometry/CauchyDeterminantStep.lean` — the division-free
  consecutive relation for a symmetric Cauchy matrix.
- `formal/GaloisForLFunctions/HTGeometry/HalfLineExponentialGram.lean` — the half-line exponentials
  have a Cauchy Gram, hence a closed-form Gram determinant and linear independence.
- `formal/GaloisForLFunctions/HTGeometry/HalfLineExponentialDistance.lean` — the Blaschke distance
  law for the Gram--Schmidt length.
- `formal/GaloisForLFunctions/HTGeometry/HalfLineExponentialCoDistance.lean` — the same with one
  rate deferred to the end, giving the distance to the span of all the other exponentials up to a
  cutoff.
- `formal/GaloisForLFunctions/HTGeometry/PuncturedSineProduct.lean` — the punctured Euler sine
  product in closed factorial form and the limit of its factorial ratio (a mathlib gap).
- `formal/GaloisForLFunctions/RHTower/XiThetaSquareRateBlaschkeLimit.lean` — Euler's hyperbolic
  sine product on the real line, its punctured form, and the square-rate Blaschke limit
  `∏_{m≠j} (m²-j²)/(m²+j²) → (-1)^{j-1} π j / sinh (π j)`.
- `formal/GaloisForLFunctions/RHTower/XiThetaSquareRateReaderNorm.lean` — the physical heat rates
  and the exact limiting co-distance `π / (2 sinh (π(n+1))²)`.
- `formal/GaloisForLFunctions/HTGeometry/HalfLineExponentialReader.lean` — the canonical
  biorthogonal reader, its Kronecker pairings, its norm, and its uniqueness.
- `formal/GaloisForLFunctions/HTGeometry/HalfLineExponentialResidualLimit.lean` — the projection
  residual is exactly the limit of the finite co-distances.
- `formal/GaloisForLFunctions/RHTower/XiThetaSquareRateReaderL2.lean` — equations `(2)`--`(5)`:
  canonicity (`thetaSquareRateReader_unique`), the exact norm `(3)`
  (`norm_thetaSquareRateReader` = `√(2/π)·sinh(π(n+1))`), the Kronecker pairing `(4)`, and the
  coefficient functional `(5)`.
