# Euler activation squarefree/valuation disintegration — formalization certificate

- **ID:** `euler-activation-squarefree-valuation-disintegration`
- **Stage:** 3-formalized
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/other/euler-activation-squarefree-valuation-disintegration.md`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Status:** `[UNCONDITIONAL LEAN] [NOT RH] [NO COMPUTATION]`

## Formalized theorem

Diagonal Euler activation has the exact normalized Bernoulli--geometric disintegration described
on paper. For every finite prime palette, the radical pushforward is the normalized squarefree
Gibbs law. The occupancy score is centered with Fisher information
`q / (1 + q)^2`; the conditional geometric valuation score is centered with variance
`q / (1 - q)^2`; the cross term vanishes; and the full Fisher information is their exact
orthogonal sum.

At `σ = 1`, the module constructs the actual prime-indexed Kolmogorov product measure on
`Nat.Primes → ℕ`. Its coordinate occupancy probability is exactly `1 / (p + 1)`. These
independent cylinder probabilities have divergent sum, so the second Borel--Cantelli lemma gives
measure one to configurations with infinitely many occupied primes. Thus the critical source is
an honest probability measure but is almost surely not carried by finite integers.

The earlier module supplies the exact diagonal holonomy/squarefree partition identity, local
activation masses, Möbius-depth/Gamma-Fisher identifications, and completed-current
transgression. `CriticalActivationReesSourceLaw` supplies the section 8 no-go: positivity of the
ordinary `2 × 2` Gram completion forces the cross bound, differentiation drops the divisor grade
by one, the resulting ratio is exactly inverse-square and unbounded, and no uniformly bounded
positive completion survives.

## Source modules and capstones

```text
formal/GaloisForLFunctions/RHTower/EulerActivationSquarefreeDisintegration.lean
formal/GaloisForLFunctions/RHTower/EulerActivationSquarefreeProbability.lean
formal/GaloisForLFunctions/RHTower/CriticalActivationReesSourceLaw.lean

woldActivationHolonomy_diagonal_eq_squarefreePartition
diagonalActivationValuationMass_total
xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher
completedXiSquarefreeCurrentCorrection_eq_normalConnection
finitePrimeActivationOccupancyWeight_eq_gibbs
diagonalActivationMeasure_isProbabilityMeasure
diagonalActivationFullFisher_eq_occupancy_add_valuation
criticalEulerProductMeasure_criticalPrimeOccupied
iIndepSet_criticalPrimeOccupiedSequence
tsum_criticalPrimeOccupiedSequence_eq_top
limsup_criticalPrimeOccupiedSequence
criticalEulerProductMeasure_infinite_occupancy
divisorReesGram_posSemidef_crossBound
monomialDivisorFisher_ratio
monomialDivisorFisher_ratio_unbounded
no_bounded_positive_divisorReesGram
```

## Verification and boundary

All three modules are registered in the `RHTower` umbrella. Direct
`lake env lean GaloisForLFunctions/RHTower/EulerActivationSquarefreeProbability.lean` and
`lake env lean GaloisForLFunctions/RHTower/CriticalActivationReesSourceLaw.lean` checks pass.
Targeted
`lake build GaloisForLFunctions.RHTower.EulerActivationSquarefreeProbability`
and `lake build GaloisForLFunctions.RHTower.CriticalActivationReesSourceLaw` pass. Scratch
`#print axioms` checks for finite Gibbs, full Fisher, critical infinite occupancy, and the bounded
positive-completion no-go report only `propext`, `Classical.choice`, and `Quot.sound`.

This certificate covers every theorem proved in sections 1--6 and 8 of the paper card, including
the probability construction rather than an assumed independent-event abstraction. Section 7's
displayed exceptional extension and trace estimate are explicitly conjectural. This certificate
does not claim the open Gamma/co-Poisson exceptional disintegration, Xi-boundary complete
contractivity, four-unit trace estimate, or RH.
