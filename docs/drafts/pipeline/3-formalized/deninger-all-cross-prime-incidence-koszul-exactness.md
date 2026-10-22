# Deninger all-cross-prime incidence Koszul exactness

**Stage:** 3 — formalized in Lean 4  
**Date:** 2026-08-03

Paper proof:

```text
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/
deninger-all-cross-prime-incidence-koszul-exactness.md
```

Formal module:

```text
formal/GaloisForLFunctions/RHTower/
DeningerCalderonWittAllCrossPrimeIncidenceKoszul.lean
```

## Formal content

- countable carrier of all ordered pairs of distinct primes;
- canonical normalized full-support `ℓ²` packet horizon;
- isometric embedding from completed Xi cohomology into the simultaneous
  all-divisor/all-cross-prime incidence completion;
- coordinate decoder into the actual algebraic Calderón--Witt global
  Milnor-incidence witness for each prime pair;
- continuous completed Green comparison into that carrier;
- bounded local and fibrewise-global packet Koszul differentials;
- unconditional annihilation of every comparison vector and, explicitly,
  the actual completed source Green comparison;
- exact local kernel and exact global kernel;
- residual-coefficient retraction recovering the complete Xi coefficient.

Capstones:

```text
deningerCalderonWittCrossPrimePacketHorizon_norm
deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero
deningerCalderonWittAllCrossPrimeXiIncidenceComparison
deningerArithmeticCompletedGreenToAllCrossPrimeIncidence
deningerCalderonWittPacketKoszulDifferential_eq_zero_iff
ker_deningerCalderonWittPacketKoszulDifferential
deningerCalderonWittGlobalPacketKoszulDifferential_completedGreen
ker_deningerCalderonWittGlobalPacketKoszulDifferential
```

Exact endpoint:

```text
ker(global packet Koszul differential)
  = range(all-cross-prime Xi incidence comparison).
```

Thus Deninger packet compatibility is now a constructed source identity,
not a proposed mechanism.  Its exact cohomology is the whole completed Xi
coefficient carrier, so it cannot itself satisfy Route L conservativity.
Remaining theorem must act nontrivially on this residual coefficient while
retaining Tate--Milnor/source orientation.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerCalderonWittAllCrossPrimeIncidenceKoszul.lean` — pass.
- `lake build GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittAllCrossPrimeIncidenceKoszul` — pass; targeted module only.
- axiom audit for normalization, comparison, local/global exactness, and
  completed Green cycle — only `propext`, `Classical.choice`, `Quot.sound`.
- umbrella import added to `GaloisForLFunctions/RHTower.lean`.
- repository lint reaches only unrelated umbrella failures in modules
  concurrently present outside this Route-L change; this module has no
  `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.

## Arithmetic-source faithfulness upgrade

The same module now proves the infinite identity-coordinate law for actual
Calderón--Witt source witnesses, exact recovery of every finitely supported
ordered-pair coefficient, injectivity of the finite arithmetic source
realization, and linear independence of all ordered cross-prime witnesses.
This rules out duplicate packet labels, including swapped prime pairs.

Additional capstones:

```text
deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness_of_ne
deningerCalderonWittCrossPrimePacketCoordinate_witness
deningerCalderonWittCrossPrimePacketCoordinate_sourceRealization
deningerCalderonWittCrossPrimeAlgebraicSourceRealization_injective
deningerCalderonWittCrossPrimeGammaWitness_linearIndependent
```

Direct module elaboration passes after this upgrade.  Final targeted module
build and axiom audit are recorded after the residual-frontier audit.
