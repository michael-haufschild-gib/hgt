# Formalize the theta likelihood-ordered single-loss transfer

## Scope

Formalize the paper theorem in
`../2-fully-proven/not_new_scientific_knowledge/theta-cusp-likelihood-ordered-tail-single-loss-transfer.md`.
Use only the existing source declarations; do not rebuild the likelihood-ratio proof.

## Existing inputs

From `RHTower/PrimeArchThetaAtomLikelihoodRatio.lean`:

```text
thetaCuspHigherFirst_rawEvenMoment_cross_le
thetaCuspHigherAtomSizeBiasedPowerExpectation_le_first
```

From `RHTower/PrimeArchThetaSourceAtomDomination.lean`,
`RHTower/PrimeArchThetaAtomMoments.lean`, and
`RHTower/PrimeArchThetaThermalSusceptibility.lean`:

```text
thetaCuspRawEvenMoment_eq_one_add_higher
thetaCuspRawEvenMoment_le_first_atom_factor
thetaCuspAtomRawEvenMoment_one_le_raw
thetaCuspAtomRawEvenMoment_pos_of_nat_pos
thetaCuspHigherAtomRawEvenMoment_nonneg
```

## Target declarations

Prove the adjacent relative-tail order in division-free form and the two direct consumers:

```text
thetaCuspHigherFirst_relativeTail_adjacent

thetaCuspUpperAdjacentRatioSeparation_of_first_atom_singleLoss
  (h : 14*(3005/2997)*a_2^2<=9*a_1*a_3) :
  ThetaCuspUpperAdjacentRatioSeparation

thetaCuspRelaxedFourthMomentConcentration_of_first_atom_singleLoss
  (h : 16*(3005/2997)*a_0*a_2<=45*a_1^2) :
  ThetaCuspRelaxedFourthMomentConcentration
```

Then add single-loss variants of the combined linear-Hankel and RH consumers. Update the
two-channel Rayleigh--Ritz and quadratic Stein adapters so their buffered coefficient is

```text
14*(3005/2997)-9
```

rather than `14*(3005/2997)^2-9`. Keep the old theorems for compatibility unless all downstream
uses can be changed without touching concurrent work.

## Verification boundary

Use targeted leaf checks only after explicit build permission. Do not run a full project build.
Wire the verified module through `RHTower.lean`, update the theorem indexes, and move the paper
card to stage 3 only after the declaration and axiom checks pass.
