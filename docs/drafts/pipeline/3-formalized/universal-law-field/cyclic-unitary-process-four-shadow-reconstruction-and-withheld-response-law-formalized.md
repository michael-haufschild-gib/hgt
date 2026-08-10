# Cyclic unitary process, four-shadow reconstruction, withheld response — Lean certification

- **ID:** ULF-CUPR-1
- **Paper card:** `cyclic-unitary-process-four-shadow-reconstruction-and-withheld-response-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveCyclicProcessFourShadow`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## New infrastructure

- `exists_pow_mem_of_compactSpace` — **powers of any element of a compact topological group return
  to every neighbourhood of the identity at arbitrarily late times.**  Mathlib has no discrete
  recurrence statement; this is proved by pigeonhole against a finite subcover of right translates
  of a symmetric neighbourhood.
- `det_weightedVandermonde` and `rank_orbitCoeff` — the rank of a *rectangular* weighted Vandermonde
  matrix is `min` of its dimensions, obtained from invertible square submatrices.  Mathlib has the
  square Vandermonde determinant only.

## Certified declarations, by clause

| Card item | Lean |
|---|---|
| (2) the moments, (6) the spectrum polynomial | `processMoment`, `spectrumPoly`, `spectrumPoly_monic`, `natDegree_spectrumPoly`, `eval_spectrumPoly`, `coeff_spectrumPoly_top` |
| (3) the rational transfer function | `tsum_processMoment_mul_pow` |
| (4) the Gram matrices | `orbitCoeff`, `momentGram`, `momentGram_apply_of_le` |
| (5) positivity and rank | `momentGram_posSemidef`, `det_weightedVandermonde`, `rank_orbitCoeff`, `rank_momentGram` |
| (7) the recurrence | `moment_recurrence`, `moment_recurrence_fin` |
| (9) the Hankel determinant | `momentHankel`, `momentHankel_eq`, `det_momentHankel`, `det_momentHankel_ne_zero` |
| (10) the Hankel system | `hankel_mulVec_coeff` |
| clause 1: coefficients determined | `coeff_eq_of_moments_eq` |
| clause 2: eigenvalue set determined | `spectrumPoly_eq_of_moments_eq` |
| clause 3: weights determined | `weights_eq_of_moments_eq` |
| clause 5: all later moments determined | `processMoment_eq_of_eq_below` |
| (11) the withheld prediction | `withheld_prediction` |
| (13) recurrence of the observer | `exists_pow_mem_of_compactSpace`, `exists_moment_near_one` |
| (14) escape of the phase lift | `phase_lift_norm`, `tendsto_phase_lift` |
| the four shadows together | `four_shadows` |

The reconstruction clauses are certified as genuine **determinacy** statements — two admissible
processes whose first `2r` moments agree have the same recurrence coefficients, the same spectrum
polynomial, the same weights, and the same moments forever — rather than as an algorithm.  That is
the mathematical content of "the finite record determines the process".

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCyclicProcessFourShadow.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,477 jobs.  `#print axioms` on the
sixteen declarations audited reports only `propext`, `Classical.choice`, and `Quot.sound`.  No
project axiom, placeholder, hypothesis interface, or computation proof is used.

## Exact field consequence

One marked cyclic pair produces four unlike shadows with exact comparison maps — analytic poles,
positive Gram rank, a recurrent compact orbit, and an open real phase lift — and the moments are the
common constitutive coordinates.  The withheld response `m_{2r}` is predicted from
`m₀,…,m_{2r−1}` alone, so this is a real instrument prediction and not a classification made after
seeing the target.  As the card's own boundary states, finite Hankel rank here means rational
transfer and finite process memory; it does not by itself type differential hypertranscendence.
