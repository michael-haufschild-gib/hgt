# Signed archimedean Gamma orbit-charge phase law — formalized

- **ID:** `signed-archimedean-gamma-orbit-charge-phase-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `signed-archimedean-gamma-orbit-charge-phase-law.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/MeromorphicGammaSuperselection.lean` | the meromorphic common-scale orbit-charge classification `(8)`: `differentialAlgebraicOver_gammaCommonScaleProductMero_iff_charge_eq_zero` and `hypertranscendentalOver_gammaCommonScaleProductMero_iff_exists_charge_ne_zero` |
| `HTGeometry/SignedGammaSharpExample.lean` | `sharpNeutralGammaRatio` — the Legendre-duplication reduction exhibiting the two signed orbit charges `(40)`–`(41)` |
| `HTGeometry/GammaMultiplication.lean` | Gauss multiplication `(6)`, real and complex meromorphic forms (mathlib had only `n = 2`) |
| `HTGeometry/DiscreteResidue.lean` | the discrete shift-residue obstruction `(13)` |
| `HTGeometry/GammaProjectiveBoundary.lean`, `PolynomialOnePointRecession.lean`, `DirectionalVandermondePhaseJet.lean`, `GammaPhaseCompletion.lean` | one-point projective boundary `(§5)`, terminal recession `(31a)`, directional phase jets |
| `RHTower/PrimeLogPhaseBudget.lean` | `rank_ℤ Λ_N`, `primesBelow_card_eq_primeCounting'` |
| **`HTGeometry/PrimePhaseBudgetRank.lean`** | `primeLog_primesBelow_linearIndependent_rat`, `primeCounting_le_finrank_of_primeLog_mem`, `primeCounting_le_rank_of_primeLog_mem`, **`primeCounting_le_of_realAutonomousAnnihilator_of_primeLog_mem`** `(37)`, `not_realAutonomousAnnihilator_of_primeLog_mem` `(38)` |
| `HTGeometry/BohrFrequencyRankLaw.lean` | the frequency-rank law consumed by `(37)`: rational frequency rank ≤ order of any nonzero autonomous ADE |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.
The headline dichotomy carries exactly one hypothesis, `hsep`, which is the pairwise integer
separation *defining* a common-scale orbit family — a data condition, not an imported theorem.

## What closed last

The card's own audit recorded `(37)` as "a half-proved inequality that no gate tracks".  Both halves
are now theorems: `rank_ℚ Λ_N = π′(N)` upgraded from the lattice statement by
`LinearIndependent.iff_fractionRing ℤ ℚ`, and the upper bound supplied by the corpus's Bohr
frequency-rank law rather than by an imported numerical input.  The phase-budget law now reads:
every prime logarithm below `N` a Bohr frequency, plus an order-`n` autonomous ADE, forces
`π′(N) ≤ n`; contrapositively, prime saturation of the Bohr module rules out every order-`n`
autonomous algebraic differential equation.

## Boundary

The card's remaining gates are external: an independent audit of the one-phase Bezout boundary
theorem, an independent audit of the directional Vandermonde boundary theorem, and the full
parent-literature and priority audit.  None is a formalization obligation.
