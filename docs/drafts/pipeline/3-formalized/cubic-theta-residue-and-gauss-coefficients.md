# Cubic theta residue and Gauss coefficients

- **ID:** cubic-theta-residue-and-gauss-coefficients
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [metaplectic Möbius descent](../1-in-progress/metaplectic-mobius-descent.md)
- **Statement:** The actual cubic residual source has nonzero scalar normalization, the exact cubic Gauss coefficients, and squarefree-times-cube unramified Fourier support.

## Theorem

Let `O = ℤ[ω]`, `δ = 1+2ω`, and let `T(h)` denote the Fourier–Bessel
coefficient of `cubicSourceResidualFunction`. Put `C = conjugate(T(1))`.
Then `C ≠ 0`. For nonzero primary generators `a,b`, with `(a)` squarefree,

`C⁻¹ conjugate(T(ab³)) = |b| conjugate((δ/a)₃) G(a)/|a|`,

where `G(a) = cubicUnitGaussSum 1 a` is the actual finite sum for the
primitive trace character. Its normalization has modulus one. Consequently
`|T(ab³)| = |C| |b|`. For every unramified ideal `I`, `T(gen(I)) ≠ 0`
if and only if `I = A B³` with `A` squarefree and both primary generators
nonzero. Thus prime valuations congruent to two modulo three vanish.

## Proof

1. The cubic Eisenstein residue at `s = 4/3` is a nonzero vector in the
   actual quotient `L²` space with Laplace eigenvalue `8/9`. Its rational
   source projection preserves the nonzero constant cusp coefficient.
   Weighted Fourier tests and the positive Whittaker kernel identify a
   continuous automorphic representative and its normally convergent
   Fourier–Bessel expansion at every positive height.
2. On the common finite cover of the prime-cube correspondences, subtract
   `N(p)⁻¹` times the source from its cube average. The two interior cusp
   valuation strata have zero Gauss sum; the endpoints have total weighted
   phase `N(p)²`. Hence this difference has zero rational cusp averages.
   Inverse branches preserve zero averages on a common `p⁶` cell, so every
   finite adjoint trace is orthogonal to the source residue. The difference
   belongs to the span of those source correspondence images; pairing with
   itself forces it to vanish.
3. Fourier transport changes frequency `h` to `hp³` and height `v` to
   `v/|p|³`. The height factor cancels the correspondence eigenvalue, giving
   `R(hp³) = R(h)` for the arithmetic residue. Combining this with the
   exact local scattering recurrences gives the three residue classes:
   exponents zero retain `R(h)`, exponents two vanish, and exponents one
   contribute `N(p)^(-2/3) G₂(9h,p)`.
4. Fourier normalization converts that first-power factor to a conjugate
   normalized Gauss sum. Coprime multiplication and primary ideal
   factorization give the displayed formula on squarefree-times-cube
   support. The identity `δ⁴ = 9` and cubicity replace `(9/a)₃` by `(δ/a)₃`.
5. If `T(1) = 0`, the support formula kills every primary coefficient.
   Translation by one forces every surviving frequency outside `3O` to
   be primary or negative primary; frequency negation preserves the
   coefficients. Thus all surviving frequencies lie in `3O`, making the
   source periodic under every Eisenstein translation. Conjugating
   translations by the rational Weyl matrix then contradicts the lower
   cusp's nontrivial cubic character. Therefore `C ≠ 0`.
6. Prime Gauss norms and coprime multiplication give `|G(a)/|a|| = 1`.
   The coefficient formula now gives its exact magnitude and the reverse
   implication in the support classification.

## Lean

Module `GaloisForLFunctions/MetaplecticMobiusDescent/Eisenstein/CubeAveragesAndNormalizedGauss.lean`:

- `cubicSourceResidualFunction_cube_eigenrelation`
- `rationalSourceScatteringResidue_prime_power_table`
- `rationalSourceThetaScalar_ne_zero`
- `normalized_sourceFourier_squarefree_cube`

Module `GaloisForLFunctions/MetaplecticMobiusDescent/Eisenstein/CuspAveragesAndBesselMellin.lean`:

- `sourceFourier_squarefree_cube_norm`
- `sourceFourier_squarefree_cube_support_iff`

All pass `lake --old env lean` with unchanged imports and default limits.
Uniform transformed-weight estimates and mean-square descent remain on
the parent card.
