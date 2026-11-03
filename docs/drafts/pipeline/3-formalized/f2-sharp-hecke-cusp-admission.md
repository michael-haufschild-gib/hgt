# Sharp cusp admission for window Hecke transport

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `MayerScattering/HeckeWindowCuspTransport.lean`.
- **Statement:** Finite Hecke output support is controlled by a one-sided germ at the first prime; the universal smooth-window threshold is strictly below `log 2`.

## Exact tail

Let `f(a)=0` for `a>R≥0`. For every complex `s` and `a>2R`,

`(a+1)^(2s) T₂,s f(a)=f(2a/(a+1))`.

The other three branches vanish. The remaining Möbius branch maps an upper tail onto a left germ at `2`, with inverse `x/(2−x)`. Thus `T₂,s f` has a finite upper cutoff iff `f` vanishes on that germ.

For the actual lift `windowPeriodLift s H`, its positive normalization has no zeros and recovers `H(−log a)` for `a>1`. Therefore finite upper output is equivalent to

`∃ b∈[1,2), ∀ x∈(b,2), H(−log x)=0`.

The lift is fixed by modular inversion, and Hecke commutes with that inversion. An upper cutoff consequently gives a lower cutoff, so this is also the exact criterion for support in some finite multiplicative window `[B⁻¹,B]`.

## Sharp stage boundary

Every smooth stage-`A` test has finite Hecke output iff **`A<log 2`**.

Below the threshold, support forces the required germ to vanish. Above it, a smooth bump centered at `−log 2` with value one has a nonzero germ. At equality, choose a smooth function whose nonzero set is exactly `(−log 2,0)`. Its endpoint value is zero, but its right germ is nonzero. Hence equality is already excluded.

This classifies the positive survivor of finite-window stability: admitting the first prime requires retaining a cusp channel, unless the full germ vanishes. Endpoint evaluation alone cannot decide admission.

## Lean audit

- `lewisHeckeT2_eq_cusp_of_two_mul_lt`, `lewisHeckeT2_normalized_cusp`
- `lewisHeckeT2_upper_cutoff_iff`
- `hecke_windowPeriodLift_upper_cutoff_iff`, `hecke_windowPeriodLift_finite_window_iff`
- `exists_windowTest_hecke_no_cutoff_of_log_two_le`
- `hecke_windowPeriodLift_all_upper_cutoffs_iff`

Final individual check passed without warnings. All six printed endpoint audits contain only `propext`, `Classical.choice`, `Quot.sound`. Imported by `RenormalizedIntersectionTheory.lean`.
