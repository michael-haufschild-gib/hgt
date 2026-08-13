# Theta-cusp calibrated power-reciprocal first-moment law

- **ID:** `theta-cusp-calibrated-power-reciprocal-first-moment-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / THETA LIKELIHOOD / POSITIVE MEASURES / MOMENT CALIBRATION
- **Paper proof:**
  `new_scientific_knowledge/other/theta-cusp-calibrated-power-reciprocal-first-moment-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/ThetaCuspCalibratedPowerReciprocalMomentLaw.lean`
- **Status:** unconditional quantitative no-go and unique positive power-reciprocal survivor.

## Formalized theorem

For an arbitrary finite measure `mu` with positive mass and almost-everywhere support in
`[c,∞)`, where `c > 1`, Lean defines

```text
negativePowerKernel alpha t = exp (-alpha * log t),
normalizedNegativePowerProfile mu alpha
  = (integral negativePowerKernel alpha dmu) / mu.real univ.
```

On positive inputs this kernel equals `t ^ (-alpha)`.  Lean proves profile positivity,
normalization at zero, the bound by `c ^ (-alpha)`, continuity on `[0,∞)`, strict decrease there,
and convergence to zero as `alpha → ∞`.  Consequently every positive target below the value at
one is reached at one and only one exponent strictly larger than one.

Specializing to the higher theta likelihood carrier gives the source-only bounds

```text
1/864 < nu.real {3},
37/256 < F(1),
m1 / m0 < F(1).
```

There is therefore a unique `alpha_* > 1` with `F(alpha_*) = m1/m0`.  Lean constructs the
power-reciprocal pushforward and its source calibration and proves

```text
mu_alpha_*(univ) = ENNReal.ofReal m0,
integral x dmu_alpha_*(x) = m1,
0 < x < 1/3  almost everywhere under mu_alpha_*.
```

For `alpha = 1`, the new carrier is proved equal to the existing fixed reciprocal carrier, and
Lean closes the paper's exact quantitative obstruction

```text
m1 + (19413/160000) * m0 < integral x dmu_1(x).
```

## Unconditional declarations

- `negativePowerKernel`
- `negativePowerKernel_eq_rpow`
- `normalizedNegativePowerProfile`
- `continuousOn_normalizedNegativePowerProfile`
- `normalizedNegativePowerProfile_pos`
- `normalizedNegativePowerProfile_zero`
- `normalizedNegativePowerProfile_le_lower_rpow`
- `strictAntiOn_normalizedNegativePowerProfile`
- `tendsto_normalizedNegativePowerProfile_atTop`
- `existsUnique_gt_one_normalizedNegativePowerProfile_eq`
- `thetaCuspNormalizedNegativePowerProfile`
- `thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure`
- `thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure`
- `thirtySeven_div_twoHundredFiftySix_lt_thetaCuspNormalizedNegativePowerProfile_one`
- `normalizedPrimeArchMoment_one_lt_twentyNine_over_oneThousandTwoHundredFifty_mul_zero`
- `existsUnique_thetaCuspSourceSelectedPowerReciprocalExponent`
- `thetaCuspSourceSelectedPowerReciprocalExponent`
- `thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_univ`
- `integral_thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_id`
- `ae_thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_support`
- `thetaCuspSourceSelectedPowerReciprocal_mass_and_firstMoment`
- `thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_one`
- `thirtySeven_div_twoHundredFiftySix_mul_normalizedPrimeArchMoment_zero_lt_calibratedReciprocal_firstMoment`
- `normalizedPrimeArchMoment_one_add_quantitativeGap_lt_calibratedReciprocal_firstMoment`

## Exact boundary

This closes degrees zero and one only.  Degree-two matching for the selected exponent remains the
next falsification/proof target.  The theorem does not assert a complete moment representation,
the Cassini boundary identity, or RH.

## Verification

- Direct `lake env lean` check passes for the module.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspCalibratedPowerReciprocalMomentLaw` passes.
- Capstone `#print axioms` checks report only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in the module.
- Module is imported by `formal/GaloisForLFunctions/RHTower.lean`.
