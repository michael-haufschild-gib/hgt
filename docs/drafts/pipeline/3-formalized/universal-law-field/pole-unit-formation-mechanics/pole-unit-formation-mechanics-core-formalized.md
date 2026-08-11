# Pole-unit formation mechanics core — formalized

- **ID:** ULF-PUFM-2-LEAN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper parent:**
  `../../../2-fully-proven/universal-law-field/pole-unit-formation-mechanics/pole-unit-scale-cocycle-correction-jet-reconstruction-and-divisor-memory-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.PoleUnitFormationMechanics`
- **Status:** [LEAN-CERTIFIED ALGEBRAIC CORE] [UMBRELLA WIRED] [NO AXIOMS ADDED]
  [EXACT FORMATION COCYCLE] [FINITE-DEPTH DIVISOR NO-GO] [NOT RH]

## Certified surface

Lean proves:

1. regular-unit response composes by an exact transported scale cocycle;
2. pole-retaining response obeys the same cocycle after universal polar splitting;
3. both responses are invariant under nonzero scalar gauge;
4. the finite logarithmic correction packet satisfies an exact additive ghost law;
5. exponentiating that packet realizes its relative response exactly;
6. one nonresonant scale reconstructs every retained correction coefficient;
7. equality of one correction packet reconstructs the entire retained finite jet;
8. for every finite depth `N`, a polynomial factor agrees with the constant unit through degree
   `N` but has a new zero at an arbitrary nonzero marked point.

Principal declarations:

- `correctedScaleResponse_cocycle`;
- `polarScaleResponse_cocycle`;
- `polar_corrected_split`;
- `correctedScaleResponse_smul`;
- `finiteCorrectionExponent_cocycle`;
- `finiteLogUnit_response`;
- `correctionJetPolynomial_reconstruct`;
- `correctionJetPolynomial_injective`;
- `finiteCorrectionDepth_divisorBlind`.

## Exact boundary

Lean certifies algebraic formation, conservation, finite reconstruction, and finite-depth divisor
blindness. Paper-level holomorphic logarithm, infinite correction tower, Gamma critical-clock
limit, common-domain analytic continuation, and Euler-shell boundary asymptotics remain outside
this module. No RH selection statement is claimed.

## Verification

- direct command:
  `lake env lean GaloisForLFunctions/HTGeometry/PoleUnitFormationMechanics.lean`;
- final umbrella command:
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`;
- axiom audit performed through a temporary `#print axioms` file;
- formal lint forbids `sorry`, `admit`, project `axiom`, `opaque`, and `unsafe` declarations.

## Log

- 2026-08-11 — exact pole/unit splitting, scale cocycle, correction ghost law, one-scale
  reconstruction, exponential realization, and finite-depth divisor blindness elaborated in Lean.
