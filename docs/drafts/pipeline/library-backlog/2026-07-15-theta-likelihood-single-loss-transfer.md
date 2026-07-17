# Finish certificate adapters for the formalized theta likelihood single-loss transfer

## Scope

The direct transfer is formalized in
`../3-formalized/not_new_scientific_knowledge/theta-cusp-likelihood-ordered-tail-single-loss-transfer.md`
and `PrimeArchThetaLikelihoodOrderedTailTransfer.lean`. The remaining work is compatibility
adapters for the existing energy certificates.

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

## Completed declarations

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

The adjacent order, both transfers, the combined linear-Hankel consumer, and the degree-two-tail
RH consumer now pass targeted build and axiom checks. Still update the two-channel Rayleigh--Ritz
and quadratic Stein adapters so their buffered coefficient is

```text
14*(3005/2997)-9
```

rather than `14*(3005/2997)^2-9`. Keep the old theorems for compatibility unless all downstream
uses can be changed without touching concurrent work.

## Verification boundary

Use targeted leaf checks only. Keep the verified direct module and old certificate theorems for
compatibility while adding the sharper variants.
