# Theta-boundary flat mass: a Riemann–Siegel-free mean-value engine for Ξ (Lean)

- **ID:** theta-boundary-flat-mass
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** loop rows 690–693 (`rh-route-candidates-loop-2026-10-08.md`); card `3-formalized/xi-lp-maximality-polynomial-symbols-lean.md`
- **Statement:** On the line `Im u = c`, `0 ≤ c < π/4`, Riemann's kernel `Φ(u + ic)` has unit-window mass `≍ (cos 2c)^{−9/2}`, flat in `U` while `y(U) = e^{2U}cos 2c ≤ 1`, and decaying like `e^{−2y(U)}` beyond. Consequently `∫_X^{2X} e^{πy/2}|Ξ(y)|² dy ≤ C X^{9/2} log X`.

## Goal
A mean-value engine for Ξ and its LP-filtered transforms that needs neither the approximate functional equation nor the Riemann–Siegel formula. Plancherel on the shifted line turns weighted mean squares of `kernelPsi m` into `∫|Φ(u+ic) m(u+ic)|²du`. The theta form of `Φ` on that line then evaluates these exactly up to constants.

## Gates
- [x] 0 → 1, 1 → 2 (paper: rows 690–691)
- [x] 2 → 3 formalized. Standard axioms only:
  - `GaloisForLFunctions.HTGeometry.integral_norm_sq_tsum_thetaWave`, `integral_norm_sq_thetaMoment`: Parseval over periods of `Re τ` (module `HTGeometry/ThetaSumPeriodParseval`);
  - `integral_norm_sq_thetaMoment_sub_le`: vertical variation via `∂_y S_k = −πS_{k+2}`;
  - `RHTower.KernelStrip.kernelC_line_eq`: `Φ(u+ic) = e^{z/2}(4π²e^{4z}S₄ − 6πe^{2z}S₂)` at `τ = −e^{2u}sin 2c + i e^{2u}cos 2c` (module `RiemannKernelStripThetaBounds`);
  - `integral_norm_sq_kernelC_line_le` / `exists_integral_norm_sq_kernelC_line_ge`: flat window bounds below height 1;
  - `integral_norm_sq_kernelC_line_le_far`: windows above height 1 are `≲ κ^{−9/2}e^{−2y(U)}`, from `thetaMomentMass_le_exp` (module `XiExponentialMeanSquareThetaBound`);
  - `integral_norm_sq_kernelC_line_whole_le`: `∫_ℝ \|Φ(u+ic)\|² ≤ 2A κ^{−9/2}(log(1/κ)/2 + 3)`;
  - `exists_integral_exp_mul_norm_sq_XiC_le`: the dyadic second moment of Ξ.

## Approach
On the ray `τ = −e^{2u}e^{−2iε}`, both `Re τ` and `Im τ` move. Unit windows in `u` cover `≍ e^{2U}` periods of `Re τ` at almost constant `Im τ`, which gives:
- Parseval: `2Σn^{2k}e^{−2πn²y}` per period;
- `∂_y S_k = −πS_{k+2}`, which controls the drift of `Im τ` across the window;
- `Σn^{2k}e^{−2πn²y} ≍ y^{−k−1/2}` for `y ≤ 1/4` and `≤ e^{−πy}·const` for `y ≥ 1`.

The factor `log(1/κ)` is the number of unit windows between the natural boundary and height 1.

## No-go closure (mandatory when falsified)
Not a no-go card. It is the positive engine behind the LP-maximality no-go (`xi-lp-maximality-polynomial-symbols-lean.md`).
- **Limits of the engine:** it gives densities and mean squares only, so it is zero-blind by design. The constants are two-sided but not asymptotic. An asymptotic version (a theta-Parseval proof of Hardy–Littlewood `∫|ζ|² ~ T log T` through Karamata) is possible but classical in content.

## Log
- 2026-10-09 — created in 3-formalized.
