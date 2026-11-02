# Arithmetic degeneration theory (ADT) — programme card

- **ID:** ADT
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0111/fable.md §8 (Q7, "the field the walls are asking for")
- **Statement:** RH as the Hodge–Riemann relation of the degenerating family `W_{φ,c,N}`; dilation
  semigroup as monodromy (one branch per prime, glued at ∞); positivity via rescaled limits,
  extension data and inheritance; carriers = counts, traces, quantized readings.

## Goal
Develop the field of fable §8: answer its questions by Lean theorems (equivalence, classification,
no-go with survivor, or unconditional theorem), build its tools. Folder
`formal/GaloisForLFunctions/ArithmeticDegenerationTheory/`, umbrella
`ArithmeticDegenerationTheory.lean`, README there.

## Plan (pillars)
1. Rescaled limit of the conductor energies = Jordan-totient form (general regular tails; tilted
   spline instance `c⁷E_m(c) → K J₈(m)/φ(m)`).
2. Monodromy: dilation acts on Ramanujan sums by valuation lowering; commuting lowering operators;
   weight strings = conductor towers.
3. Limiting mixed structure of the finite family: rescaled conductor Gram → Jordan form along
   every universal-regime schedule (HWV deviation bound + RAPT orthonormality).
4. Inheritance radius: exactly the RH exponent 1/8 (HWV equivalence) — rescaled extension data.
5. Abstract rescaling calculus (inheritance; degenerate limit inherits nothing).
6. Two-projection structure of the archimedean trace carrier `1 − P − P̂`.
7. Selectivity of the limit (twins, fakes), calibration over `𝔽_q`.

## Lean modules (all check with `lake --old env lean`, wired into the umbrella and MainTheorems)
RegularTailsGiveJordanTotientLimits, TheTiltedSplineHasARegularTail, TheLimitingMixedStructure,
TheDilationsLowerTheConductor, TheWeightStringsOfTheRescaledLimit,
TheRescaledLimitTensorizesOverThePrimes, TheSubthresholdBlockIsUniformlyJordan,
TheMertensFunctionIsAGluingDeterminant, CompleteDegenerationSelectsZeta,
TheMonodromyIsEventuallyIdempotent, TheScalingFormOfTheDegeneration,
TheBranchesAndTheWeightsSeparate, TheConductorEnergyIsAConeSumOfTopStrata,
TheArchimedeanCarrierIsIndefinite, TheDegenerationExponentIsSetByTheProfile,
TheSubthresholdBlockInheritsTheJordanForm, TheGradedPiecesAndTheTopStratumAreMoebiusDual.

## Open
- Second-order rescaled limit at the critical curve `c⁸ ≍ log N` on fixed packets: deterministic
  `O(c/log N)` corrections versus the zero-dependent part.
- Threshold block `m ≍ c` and its coupling to the pure block (whole-space `1/9 → 1/8`).
- Twists with non-summable defect (Liouville, cofinite flips); lattice fakes.
- Carriers: semilocal trace at `2`; Voronoi duality of the cone count.
- README §9 for the full list.
