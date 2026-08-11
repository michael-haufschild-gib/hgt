# Source-edge harmonic/polar reconstruction law — Lean formalization record

- **ID:** ULF-SFHM-2/3-LEAN
- **Stage:** 3-formalized
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [NO COMPUTATIONAL PROOF]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.SourceFormationHarmonicMechanics`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

Lean certifies one literal arithmetic formation with five coupled executions:

1. adjacent power-dilated Möbius channels are oriented prime-exponent edges;
2. consecutive edges conserve their endpoint boundary and marked edges reconstruct history;
3. real refinement energy splits exactly into coarse energy plus centered fluctuation;
4. complex character responses reconstruct the character, telescope coherently, and retain
   positive variation history;
5. the parity character closes on every even coherent block while positive history equals `4n`;
6. phase-quotiented radial refinement vanishes exactly on the unit circle.
7. the faithful analytic realizations of the same depth-12 finite-abscissa sources have maximal
   countable differential rank over the full zeta differential field.
8. one-sided unweighted radial edge energy is summable exactly for `q ≤ 1`, while simultaneous
   forward/reflected admission holds exactly at `q = 1`; on a prime radial character this selects
   exactly zero real drift.

The premise-free theorem `rankTwelve_fiveShadow_fusion_certificate` packages incidence,
coherent character execution, polar harmonicity, recurrent/open history, and analytic
differential independence into one closed proposition.

## Main declarations

- `primeExponentEdge_eq_boundary`
- `sum_primeExponentEdge`
- `adjacent_mPart_moebius_apply_prime_pow`
- `completeResolutionNormalizedArithmetic_prime_edge`
- `rankTwelveFiniteAbscissaSource_prime_edge`
- `rankTwelveFiniteAbscissaSource_relativeDifferentialIndependent`
- `marked_edge_reconstruction`
- `refinement_energy_pythagoras`
- `twoEdge_refinement_energy_identity`
- `primeRadial_twoEdge_refinement_energy_eq_zero_iff`
- `complexCharacterEdge_ratio`
- `primeExponentEdge_character_execution`
- `rankTwelveSource_character_execution`
- `sum_complexCharacterEdge`
- `complexCharacterVariation_neg_one`
- `sum_complexCharacterEdge_neg_one_even`
- `complexCharacter_radial_energy_eq_zero_iff`
- `rankTwelve_fiveShadow_fusion_certificate`
- `geometricRefinementEnergy_eq`
- `summable_geometricRefinementEnergy_iff`
- `bilateral_geometricRefinementEnergy_summable_iff`
- `primeRadial_bilateral_geometricRefinementEnergy_summable_iff`

## Verification

- direct `lake env lean` elaboration: pass;
- final leaf `lake build GaloisForLFunctions.HTGeometry.SourceFormationHarmonicMechanics`: pass,
  9,026 jobs;
- umbrella reaches and builds the module, then fails in unrelated concurrent
  `HTGeometry.ConstitutiveAdversarialLawStress` type errors/timeouts;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- no `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, or computation certificate.

## Exact boundary

Lean proves the source mechanics, critical receiver, and exact bilateral-admission selector. It
does not assert that Xi zeros are bilaterally admitted by one marked source completion, that
cofinal positive variation is admitted in the physical completion, or that any RH endpoint
follows. Those are separate source-descent claims.
