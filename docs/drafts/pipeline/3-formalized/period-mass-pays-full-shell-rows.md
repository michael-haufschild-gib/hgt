# Complete-period mass pays full shell rows

- **ID:** SSH-PERIOD-MASS-SHELL-ROWS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q1/O1, finite-horizon conductor costs.

## Statement

Let `ψ` have positive period `q`, zero period sum, and period absolute
mass `P=Σ_(r<q)|ψ(r)|`. Every interval sum has absolute value at most `P`.
For a compact `C²` atom profile with positive mass, `0<w≤1/4`, `n≥4`, and `wn≥1/2`,
the full shell row satisfies

`|b_n Σ_ℓ b_ℓ β(log ℓ−log n)ψ(ℓ)|≤Cφ P G/n`.

One may take `Cφ=2+28(1/4+A₁/∫φ²)`, where
`|autocorr(φ)'|≤A₁`. Such `A₁≥0` is supplied by
`exists_abs_deriv_shellAutocorr_le` for every admitted profile.

Multiplying the row by `log ℓ` costs the additional factor
`1+log(2n)`. The sums retain the full support through `ceil(N exp w)`
when `n≤N`. Consequently the normalized Ramanujan mode costs `m`,
and its centered divisor jet costs `2m log m`, rather than period
times pointwise amplitude.

## Paper proof

Remove complete periods from any shifted prefix. Its remainder has
absolute sum at most the full period absolute mass, which is invariant
under translation. Abel summation bounds a smooth weighted row by
`P` times its endpoint value plus total variation. Existing shell-window
geometry and derivative bounds give `Cφ G/n`, including the lattice
endpoints. The logarithmic row uses the same argument with its explicit
derivative. Apply the exact complete-period Plancherel bounds to the two
arithmetic profiles.

## Scope

This controls the actual finite rows in mixed top-band cancellation.
It does not yet bound the full all-vector agreement-shell form.

- [x] Existing Abel inequality and full-window variation bound identified.
- [x] Period-mass interval and shell-row bounds formalized.
- [x] Ramanujan and centered-jet specializations formalized.
- [x] Final direct check, axiom audits, and umbrella import.

## Lean declarations

Module: `SuccessorShellArithmetic/TopBand/PeriodMassShellRows.lean`.

- `abs_sum_Ico_periodic_le_period_mass`: every shifted interval.
- `abs_full_shellPartnerKernel_sum_le_of_interval_bound`: full smooth row.
- `abs_full_rowIntegrand_sum_le_of_interval_bound`: full logarithmic row.
- `abs_fullRamanujanShellRow_le`: normalized Ramanujan row, cost `m`.
- `abs_fullRamanujanLogShellRow_le`: logarithmic Ramanujan row.
- `abs_fullCenteredJetShellRow_le`: centered divisor-jet row, cost `2m log m`.

Final `lake --old env lean` check passed. All audited transitive dependencies
use only `propext`, `Classical.choice`, and `Quot.sound`.
