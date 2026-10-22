# Finite superzeta parity-reflection universality law

## Status

Exact Lean check passed with
`lake env lean GaloisForLFunctions/RHTower/FiniteSuperzetaSpectralTorelliUniversalityLaw.lean`.

## Lean-generated inputs

- `FunctionalEquationParity.lean`: negation-invariant finite spectrum forces every odd power sum
  to vanish.
- `SuperzetaResolvent.lean`: superzeta coefficients are exactly spectral power sums.
- `FiniteSuperzetaSpectralTorelliUniversalityLaw.lean`: complete finite superzeta trace is faithful
  on spectral multisets of fixed cardinality.
- Even/odd power algebra: negating spectrum fixes even trace coefficients and negates odd ones.

## Survivor

For an `n`-point centered spectrum, vanishing of odd coefficients only through order `n` is
equivalent to negation invariance. Equivalently, for original coordinates `rho`, centered odd
coefficients through order `n` vanish iff the multiset is invariant under `rho ↦ 1 - rho`.
Existing corpus contained only functional-equation symmetry implying odd-moment vanishing. Finite
power-sum Torelli supplies the sharp finite converse, including multiplicities.

## Formal target

`GaloisForLFunctions.finiteSuperzetaOddCoefficients_vanish_iff_negationInvariant`

## Novelty audit

Pending post-formalization literature search.
