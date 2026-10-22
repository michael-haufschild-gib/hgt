# Xi Ward edge-energy phase-quantization universality law

- **ID:** `xi-ward-edge-energy-phase-quantization-universality-law`
- **Law:** LAW506
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/XiWardEdgeEnergyPhaseQuantizationUniversalityLaw.lean`

## Theorem

The continued Xi Ward edge quadratic energy has exactly two arithmetic phases:

```text
RH      iff energy = 0,
not RH iff 8*pi < energy.
```

Consequently every state lies in exactly one of `(RH, energy = 0)` or
`(not RH, 8*pi < energy)`; the full interval `(0, 8*pi]` is absent.

## Theorem-generated derivation

Whole-corpus theorem-leaf pairing exposed:

- `riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw_sharp`, valid at every closed budget
  `0 <= c <= 8*pi`;
- `xiWardEdgeQuadEnergy_eq_zero_or_eightPi_lt`, the independent sharp Gram-lattice gap;
- `xiWardEdgeQuadEnergy_eq_tsum_gram`, which supplies the positive ordered-pair interpretation
  used by the gap theorem.

Corpus states the budget classifier and spectral gap separately, but does not identify the
strict upper phase with precisely non-RH.

## Dependency-closed paper proof

Set `c = 0` in the sharp budget theorem.  Since edge energy is extended-nonnegative, being at most
zero is equality to zero; this proves `RH iff energy = 0`.

If RH fails, the gap theorem gives `energy = 0` or `8*pi < energy`.  The first branch would imply
RH by the preceding equivalence, contradiction, so the strict branch holds.  Conversely,
`8*pi < energy` is incompatible with the zero energy forced by RH.  Case splitting on RH gives
the exhaustive two-phase classification.  No numerical computation is used.

## Strict corpus delta

Existing modules leave the high-energy branch merely as an alternative in an unconditional
dichotomy.  New law identifies its exact arithmetic meaning, proving both directions of the
non-RH phase and an exhaustive labeled phase classification.

## Lean result

`formal/GaloisForLFunctions/RHTower/XiWardEdgeEnergyPhaseQuantizationUniversalityLaw.lean`
proves:

- `riemannHypothesis_iff_xiWardEdgeQuadEnergy_eq_zero`;
- `not_riemannHypothesis_iff_eightPi_lt_xiWardEdgeQuadEnergy`;
- `xiWardEdgeQuadEnergy_arithmeticPhaseClassification`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/XiWardEdgeEnergyPhaseQuantizationUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Standard sources discuss Weil
positivity, explicit formulas, spectral interpretations of Xi zeros, and many RH-equivalent
quadratic criteria.  Targeted searches found no Ward-response energy with this exact ordered-pair
Gram representation, no forbidden interval `(0, 8*pi]`, and no matching non-RH iff theorem.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for this specific
continued Ward energy and sharp phase threshold, not for the logical act of labeling the two
branches of an already proved gap.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
