# Route-P critical information Schur depletion no-go

- **ID:** `P-G73`
- **Stage:** `1-in-progress`
- **Type:** exact first-Schur-channel classification / quantitative no-go / positive survivor
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN DIRECT GREEN] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-critical-mass-no-go.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalInformationSchurDepletion.lean`

## Conjecture P-G73.A: first information coenergy supplies full missing Schur correction

For prime-power label `pk`, define

```text
kappa(pk) = sourceHorizontalPrimeGeometricKLScaleTerm(pk,1/4),
w(pk)     = reflectedStokesWeight(1/2,pk),
d(pk)     = (2-kappa(pk)) w(pk).
```

Here `2w` is P-G71 raw square-carrier mass and `kappa*w` is the coefficient-faithful critical
information channel.

**Verdict: false, retired unconditionally.** The channel is mathematically valid: Lean proves
`0<kappa(pk)<2` for every label, hence `d(pk)>0`, and proves `sum d(pk)<infinity`. But a new cubic
virial estimate gives `kappa<3/10` on the hostile atoms `(2,0),(2,1),(3,0),(3,1)`. Sharpened
source-only Gamma-contraction bounds prove their raw mass exceeds `63/1000`; after depletion those
four atoms still exceed `29/625`, larger than the entire completed seam mass.

## New universal principle

Correct sign and summability do not determine Schur adequacy. Route P has a hierarchy of central
debts: raw reflection creates positive compact mass; first information depletion pays a genuine
negative coenergy but cannot remove the valuation-vacuum overcount. Completion must eliminate a
coherent non-diagonal Gamma/valuation block before prime-power labels are scalar-compressed.

This explains P-G72 as order-of-operations failure, not normalization failure. The exact source
identity `Gamma Schur elimination = valuation translation` is the next live mechanism; it cannot
be replaced by coefficientwise subtraction.

## Lean realization

Headline declarations:

- `sourceHorizontalHolonomyVirial_le_cubic_exp`;
- `gammaSewnMobiusApertureStokesCriticalInformationFactor_lt_two`;
- `gammaSewnMobiusApertureStokesCriticalInformationFactor_le_cubic`;
- `gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos`;
- `summable_gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight`;
- `gammaSewnMobiusApertureStokesCriticalRawFourAtomMass_strongLower`;
- `gammaSewnMobiusApertureStokesCriticalInformationDepletedFourAtomMass_lower`;
- `normalizedPrimeArchMoment_zero_lt_tsum_criticalInformationDepletedWeight`;
- `gammaSewnMobiusApertureStokesCriticalInformationAdditionalDepletion_neg`.

## Next conjecture

Construct the reflected Stokes response as compression of the coherent prime--Gamma valuation
Gram, apply Gamma Schur elimination there, and only then pass to square-coordinate Markov mass.
First hostile test: prove resulting central mass is below P-G73 residual, while positivity follows
from the finite-block Schur theorem rather than atomwise fitted weights.

## Honest boundary

P-G73 classifies and retires first-information depletion. It does not yet construct the required
non-diagonal block compression, identify completed moments, or prove RH.
