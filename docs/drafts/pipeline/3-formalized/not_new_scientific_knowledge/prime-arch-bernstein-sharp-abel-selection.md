# Prime--archimedean Bernstein sharp Abel selection

- **ID:** `prime-arch-bernstein-sharp-abel-selection`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT AN RH PROOF]`
- **Statement:** The completed Xi endpoint-purity susceptibility has one exact Abel radius.  The
  RH phase has radius one.  In every false phase, the same finite source-attained maximal packet
  selects the radius `B⁻²`, a strictly positive `B²ⁿ/√n` coefficient asymptotic, a finite
  nonzero square-root Abel boundary, positive radial blow-up, and failure of every single-valued
  meromorphic germ agreeing with the interior real susceptibility.

## Theorem

Let

\[
 \mathcal S(t)=\sum_{n\ge0}
   \operatorname{primeArchEndpointBernsteinPurity}(n)t^n.
\]

There is a unique exact radius `R` in the unconditional collar

\[
 \frac{250000}{251001}<R\le1.
\]

Exactly one of the following phases holds.

1. `RiemannHypothesis` and `R=1`.
2. `¬ RiemannHypothesis`, `R<1`, and there are a nonempty finite packet `D` and reals
   `1<beta<B`, `L>0` such that `R=B⁻²`, the coordinates in `D` have maximal affine amplitude
   `B`, every coordinate outside `D` has amplitude at most `beta`, and

\[
 \sqrt n\,\frac{\operatorname{primeArchEndpointBernsteinPurity}(n)}{(B^2)^n}
   \longrightarrow L,
\]

\[
 \sqrt{1-B^2t}\,\mathcal S(t)\longrightarrow\sqrt\pi L>0,
 \qquad \mathcal S(t)\longrightarrow+\infty
 \quad(t\uparrow B^{-2}).
\]

No meromorphic function at `B⁻²` agrees with `ℒ S` on an interior left neighborhood.  The
obstruction is parity-exact: after squaring the radial law, a hypothetical continuation `f` would
make `(z-B⁻²)f(z)^2` have meromorphic order both zero and `1+2 ord(f)`.

Consequently, an independently constructed single-valued meromorphic source realization of
`ℒ S` throughout the explicit collar implies RH.  This last condition is the remaining
source-producing theorem; defining continuation from the Xi divisor or from the Abel coefficients
would be circular.

## Formal theorems

- `GaloisForLFunctions.HTGeometry.tendsto_sqrt_one_sub_mul_tsum_of_normalizedCentralBinom_ratio`
- `GaloisForLFunctions.HTGeometry.tendsto_sqrt_one_sub_mul_tsum_of_sqrtNat_mul`
- `GaloisForLFunctions.HTGeometry.tendsto_sqrt_scaled_boundary_mul_tsum_of_halfOrder`
- `GaloisForLFunctions.HTGeometry.tendsto_atTop_of_positive_sqrt_scaled_boundary`
- `GaloisForLFunctions.HTGeometry.false_of_meromorphicAt_of_positive_sqrt_scaled_boundary`
- `RHTower.exists_positive_halfOrder_primeArchEndpointBernsteinPurity_of_not_rh`
- `RHTower.exists_exactRadius_positiveHalfOrder_primeArchEndpointBernsteinAbelBoundary_of_not_rh`
- `RHTower.primeArchEndpointBernsteinAbelSharpSelectionMaster`
- `RHTower.riemannHypothesis_of_primeArchEndpointBernsteinAbelMeromorphicCollar`

## Files

- `formal/GaloisForLFunctions/HTGeometry/CentralBinomialAbelTransfer.lean`
- `formal/GaloisForLFunctions/HTGeometry/ScaledCentralBinomialAbelTransfer.lean`
- `formal/GaloisForLFunctions/HTGeometry/PositiveSquareRootBoundaryBlowup.lean`
- `formal/GaloisForLFunctions/HTGeometry/HalfOrderMeromorphicObstruction.lean`
- `formal/GaloisForLFunctions/RHTower/XiBernsteinPurityHalfOrderAsymptotic.lean`
- `formal/GaloisForLFunctions/RHTower/XiBernsteinPurityHalfOrderAbelBoundary.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinExactHalfOrderAbelBoundary.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinAbelSharpSelectionMaster.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinAbelMeromorphicCollarCriterion.lean`

## Gates

- [x] complete Xi coefficient asymptotic, including the infinite nonmaximal complement
- [x] generic half-order Abel transfer
- [x] exact-radius coupling
- [x] positive radial blow-up
- [x] meromorphic-order parity obstruction
- [x] single sharp selection master theorem
- [x] meromorphic-collar-to-RH criterion
- [x] targeted compilation of every new module
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] independently construct the source-side meromorphic collar
- [ ] RH
