# Finite signed cyclic-divisor moment universality law

## Status

Theorem-first survivor. Paper proof complete; exact Lean check passed warning-free on 2026-07-22.

## Lean-generated inputs

- `HTGeometry/SignedMomentSeparation.lean`: distinct `r` nodes make the first `r` signed power
  moments injective in the complex weight vector.
- `HTGeometry/FiniteAffineCyclicMomentSymmetryUniversalityLaw.lean`: primitive cyclic scaling of an
  unweighted finite spectrum is detected by vanishing nontrivial-character moments.
- Primitive-root power/divisibility API already used by the RHTower Weyl and deck-charge laws.

## Survivor

Let distinct nodes `lam : Fin r → ℂ` be cyclically permuted by `σ` through
`lam(σ i)=ζ lam(i)`, with `ζ` a primitive `d`th root. A complex signed divisor on those nodes
is invariant under cyclic pushforward exactly when its signed moments of orders `0,…,r-1` vanish
in every nontrivial character sector `d ∤ k`.

This extends finite unweighted spectral symmetry to arbitrary complex weights while retaining the
sharp finite Vandermonde threshold.

## Formal targets

- `GaloisForLFunctions.signedMoment_cyclicPushWeight`
- `GaloisForLFunctions.cyclicPushWeight_fixed_iff_firstSignedCharacterMoments_vanish`

## Novelty audit

Post-formalization searches covered finite atomic signed moment recovery, invariant measures under
cyclic actions, cyclic Fourier/character inversion, and vanishing sums of roots of unity. Adjacent
primary sources include Deninger's invariant-measure/Fourier functional equations
([arXiv:1111.6416](https://arxiv.org/abs/1111.6416)), Huang's Fourier-coefficient rigidity for
multiplication-invariant circle measures
([arXiv:1606.06078](https://arxiv.org/abs/1606.06078)), and Lam--Leung's classification problem for
vanishing sums of roots of unity ([arXiv:math/9511209](https://arxiv.org/abs/math/9511209)). None
states the finite distinct-node result here: invariance of arbitrary complex weights under a given
primitive cyclic node permutation iff only the nontrivial-character members of the first sharp
`r`-moment Vandermonde block vanish. Novelty claim is restricted to this theorem packaging and its
sharp finite threshold; character covariance and Vandermonde injectivity are classical inputs.

## Verification

```text
cd formal
lake env lean GaloisForLFunctions/HTGeometry/FiniteSignedCyclicDivisorMomentUniversalityLaw.lean
```

Passed with exit code 0 and no warnings on 2026-07-22.
