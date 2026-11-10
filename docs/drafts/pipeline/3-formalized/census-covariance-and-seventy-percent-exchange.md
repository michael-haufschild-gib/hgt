# Census covariance and seventy-percent exchange rates

- **Stage:** 3-formalized
- **Source:** `docs/reports/review-0911/fable.md`, §11.6.

## Statements

1. The canonical source covariance and its source-selected corrected budget
   have asymptotic ceiling `4π(1−67250071/100000000)` times the zero count.
   This is strictly smaller than `4π/3`.
2. The optimal bounded-form-factor certificate at `B=4` is `7/10`, attained
   at bandwidth `10/9`. The Frobenius ceiling for a seventy-percent
   certificate is `13/10`; at bandwidth `4/3` this corresponds to the
   weighted form-factor integral being at most `7/45`.

## Proof

Transport `simple_critical_proportion_ge_67250071` to the completed-Xi
census, enlarge simple critical zeros to all critical zeros, and apply the
exact covariance/density calibration. The corrected-budget transfer
preserves the ceiling. Its improvement follows from `67250071/100000000>2/3`.

For exchange rates, specialize `certValue_at_opt` and `certValue_le_opt`
at `B=4`. At `λ=4/3` the Frobenius functional is `9/8+(9/8)I`; its ceiling
`13/10` is therefore equivalent to `I≤7/45`. These are exact calibration
statements; no bound on the actual form factor is asserted.

## Lean verification

- `SquareRootThreshold/Census/SourceCovarianceBaseline.lean`:
  `criticalFeaturePhaseCovariance_67250071_upper`,
  `criticalFeatureSourcePhaseCorrectedBudget_67250071_upper`,
  `census_covariance_ceiling_lt_four_pi_thirds`.
- `TransThresholdPairCorrelation/SeventyPercentExchangeRates.lean`:
  `certOpt_four`, `certValue_ten_ninths_four`, `certValue_four_le_seven_tenths`,
  `seven_tenths_le_certOpt_iff`,
  `seventy_percent_certificate_of_formFactor_le_four`,
  `seventy_percent_certificate_four_thirds_iff`.

Both modules passed direct `lake --old env lean` checks. Audited declarations
depend only on `propext`, `Classical.choice`, `Quot.sound`; both modules are
imported by their owning umbrellas.
