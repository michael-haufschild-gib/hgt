# Finite affine cyclic moment-symmetry universality law

## Status

Lean source written.  The exact proof passed warning-free in `/tmp/hgt_law268.lean` against the
current toolchain using a local copy of the already-proved transformation--moment connector.
Direct target checking is deferred to final audit because that connector's `.olean` is absent and
the research protocol permits `lake build` only in final audit.

## Lean-generated inputs

- `HTGeometry/FiniteMultisetTransformationMomentUniversalityLaw.lean`: first `n` power sums
  characterize invariance of an `n`-point multiset under any point transformation.
- `HTGeometry/TorsionFaceExactification.lean`: primitive-root character criterion
  `ζ^k = 1 ↔ d ∣ k`.
- `RHTower/FiniteSuperzetaSpectralTorelliUniversalityLaw.lean`: order-two negation/reflection
  case appears as odd superzeta coefficient vanishing.

## Survivor

For every primitive `d`th root `ζ`, an `n`-point spectrum is invariant under rotation about an
arbitrary center `c`, `z ↦ c + ζ(z-c)`, exactly when its centered power sums of every order
`k ≤ n` outside the trivial character sector (`d ∤ k`) vanish. This is a sharp finite threshold
and simultaneously generalizes all centered parity/reflection criteria from order two to every
finite cyclic order.

## Formal targets

- `GaloisForLFunctions.finiteCyclicScaling_fixed_iff_firstCharacterMoments_vanish`
- `GaloisForLFunctions.finiteAffineCyclicSpectrum_fixed_iff_firstCenteredCharacterMoments_vanish`
- `formal/GaloisForLFunctions/HTGeometry/FiniteAffineCyclicMomentSymmetryUniversalityLaw.lean`

## Novelty audit

Post-proof searches covered primitive-root power-sum vanishing, Newton-sum cyclic symmetry,
rotationally symmetric polynomial roots, and cyclic invariant theory.  Closest primary sources were:

- Demina--Kudryashov, *Point Vortices and Polynomials of the Sawada--Kotera and
  Kaup--Kupershmidt Equations* (`arXiv:1112.4804`), which derives special-family algebraic root
  relations and examples of cyclic root geometry.
- Lam--Leung, *On vanishing sums for roots of unity* (`arXiv:math/9511209`), which classifies
  possible lengths of vanishing sums whose terms themselves are roots of unity.
- Bilu--Luca, *Binary polynomial power sums vanishing at roots of unity*
  (`arXiv:2005.05500`), which studies roots of unity as zeros of polynomial-exponential power
  sums.

None states the arbitrary finite-multiset iff criterion, its exact first-`n` threshold, or the
affine-center version.  Ingredients are classical (Newton identities and cyclic characters), so
novelty claim is restricted to this universal packaging and formal theorem, not to either
ingredient.
