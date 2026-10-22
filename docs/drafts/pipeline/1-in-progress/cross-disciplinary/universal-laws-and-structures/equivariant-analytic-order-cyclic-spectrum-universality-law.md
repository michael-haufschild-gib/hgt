# Equivariant analytic-order and cyclic-spectrum universality law

## Status

Theorem-first survivor. Paper proof complete. New Lean core passed in an exact scratch check;
repository module check is deferred until the final dependency audit because Law268's parent module
does not yet have an object file and project rules reserve `lake build` for final audit.

## Lean-generated inputs

- `RHTower/SeamOfflineReflection.lean`: arbitrary analytic self-map invariance forces
  `(τ'(c))^ord = 1` for scalar-valued carriers.
- `RHTower/CCM/CCMFiniteRamifiedBoundaryNoGo.lean`: scalar-rotation invariance forces
  `ζ^ord = 1` for vector-valued analytic germs.
- `HTGeometry/FiniteAffineCyclicMomentSymmetryUniversalityLaw.lean`: a primitive affine cyclic
  symmetry of an `n`-point spectrum is equivalent to vanishing of its first `n`
  nontrivial-character centered moments.
- `RHTower/CarrierBoxCount.lean`: analytic order is additive over a finite product.
- `Bottcher/ConnectedRepellingRootDefect.lean`: polynomial root multiplicity is analytic order,
  confirming that the order/count bridge is already a corpus mechanism.

## Survivor

The two trivial-character local laws share a stronger missing statement. For a vector-valued
analytic germ and arbitrary analytic self-map fixing `c`, local equivariance

`F(τ(s)) = χ • F(s)`

forces

`(τ'(c)) ^ ord_c(F) = χ`.

For a finite spectrum invariant under primitive rotation of order `d`, its centered characteristic
product has character `ζ^n`. Its analytic order at the center is exactly the number of spectral
points at that center, so this number is congruent to total spectrum size `n` modulo `d`. Therefore
Law268's moment criterion is equivalent to the conjunction of cyclic multiset symmetry,
characteristic-product covariance, and the central-multiplicity congruence.

## Formal targets

- `RHTower.multiplier_pow_analyticOrderAt_eq_character`
- `GaloisForLFunctions.finiteCenteredSpectralProduct_analyticOrderAt_zero`
- `GaloisForLFunctions.finiteCenteredSpectralProduct_cyclic_covariant`
- `GaloisForLFunctions.finiteCenteredSpectrum_centerMultiplicity_modEq_card`
- `GaloisForLFunctions.finiteAffineCyclicMomentCharacterOrderUniversalityLaw`

## Novelty audit

Post-proof searches covered semi-invariant holomorphic germs, cyclic quotient actions, equivariant
characters, rotation eigenfunctions and vanishing order, cyclic polynomial root sets, and roots of
unity. Adjacent primary literature includes Lam--Leung on vanishing root-of-unity sums
([arXiv:math/9511209](https://arxiv.org/abs/math/9511209)), Deninger on invariant circle measures
and Fourier functional equations ([arXiv:1111.6416](https://arxiv.org/abs/1111.6416)), and
Meyer--Nadareishvili on cyclic representation-ring character sectors
([arXiv:2406.11787](https://arxiv.org/abs/2406.11787)). Searches found no statement combining:

1. vector-valued analytic germs;
2. an arbitrary analytic self-map rather than a linear group action;
3. a nontrivial scalar eigencharacter `χ`;
4. the exact local identity `(τ'(c))^ord = χ`; and
5. the finite moment-Torelli consequence identifying characteristic-product character and central
   multiplicity modulo orbit order.

Novelty claim is limited to this joint theorem and equivalence packaging. Local power-series
peeling, character decomposition, Vandermonde/Newton recovery, and cyclic orbit counting are
classical and are not claimed as new.
