# Halász's method is assembled in Lean (2026-08-07)

`RHTower/Sieve/HalaszPerronAssembly.lean` — green (9074 jobs), axiom-clean, in the umbrella.

`norm_tsum_mul_smoothWeight_le` :
`2π‖∑' n, f n · w(n)‖ ≤ Wsup·(Halász integral bound) + trivial·∫_{(Icc (-T) T)ᶜ} ‖perronKernel‖`
for `|f| ≤ 1` multiplicative on coprimes, `f 0 = 0`, `σ > 1`, `2 ≤ z`, `0 ≤ δ`, `0 < logSqWeight z`,
`0 < N`, `0 < H`, `0 ≤ T`, and any uniform kernel bound `Wsup`.

Mechanism: corpus `SmoothWeightPerron.tsum_mul_smoothWeight_eq_integral` (arbitrary unit-bounded
coefficients) → `norm_integral_le_integral_norm` → `integral_add_compl` at height T → range piece by
`Wsup` × `integral_norm_tsum_twistedSummand_le`, tail piece by trivial size × kernel tail.
Product integrability via `Integrable.mono'` against `triv·‖W‖`.

## The full chain (all green, axiom-clean, umbrella-wired)

local Euler factor → full-series Euler bound (`MultiplicativeEulerBound`) → trivial size
(`PrimeAbscissaSumBound`) → harmonic-distance bridge (`DistanceAbscissaBridge`) → dichotomy + discrete
large values (`HalaszFullSeriesSum`) → window confinement (`HalaszLargeValueWindow`) → covering measure
(`DiameterCoveringMeasure`) → t-integral (`HalaszIntegralBound`) → Perron (`HalaszPerronAssembly`).

## Still parametric — do NOT claim a decay result yet

The assembled bound takes as inputs (i) a uniform bound `Wsup` on `‖mellin (smoothWeight N H)(σ+iy)‖`
and (ii) the kernel tail `∫_{|y|>T}‖·‖`. Both are bounded by the corpus's
`HTGeometry/SmoothWeightMellin.norm_mellin_smoothWeight_le_pow` and `PerronKernelBound`
(`‖1/(s(s+1))‖ ≤ r⁻²` + `integrable_inv_sq_add_sq`), but they are NOT yet instantiated, and the
parameters `z, δ, T, H` are not yet chosen. A decay statement for a specific `f` (e.g. μ) requires both.

## Traps

- **`smoothWeight` is ambiguous**: `RHTower.Sieve.SmoothSum.smoothWeight (t : ℝ) (s : ℕ)` shadows
  `GaloisForLFunctions.HTGeometry.smoothWeight (N H : ℝ)` inside `namespace RHTower.Sieve`. Fully
  qualify.
- `verticalIntegrable_mellin_smoothWeight` returns `Complex.VerticalIntegrable`, which is *definitionally*
  `Integrable (fun y => f (σ + y*I))` — pass `(σ := σ)` explicitly or the abscissa stays a metavariable.
- After `rw [hid]` the series appears unfolded (`f n * n^(-s)`) while the local `set F` is in terms of
  `twistedSummand`; close the congruence with `simp only [hF, hW, twistedSummand, perronKernel, norm_mul]`.

See `mem:route_e/halasz_integral_bound_2026_08_07`.
