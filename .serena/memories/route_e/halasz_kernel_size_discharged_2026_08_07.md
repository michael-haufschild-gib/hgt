# The Perron kernel size is discharged (2026-08-07)

`RHTower/Sieve/HalaszPerronAssembly.lean`, appended — green (9074 jobs), axiom-clean.

- `norm_perronKernel_le (hN : 0 ≤ N) (hH : 0 < H) (hσ : 0 < σ) (y) :
   ‖perronKernel σ N H y‖ ≤ (N+H)^σ / σ` — uniform in `y`, straight from the corpus's
  `HTGeometry/SmoothWeightMellin.norm_mellin_smoothWeight_le_pow` (which needs only `0 < s.re`).
- `norm_tsum_mul_smoothWeight_le_explicit` — the assembled Halász/Perron bound with `Wsup` replaced by
  `(N+H)^σ/σ`. Only the kernel TAIL `∫_{(Icc (-T) T)ᶜ} ‖perronKernel‖` is still a free quantity.

## The one remaining mechanical step

`HTGeometry/SmoothWeightInversion.exists_bound_mellin_smoothWeight_line hN hH hσ` gives
`∃ C > 0, ∀ y, ‖W(σ+iy)‖ ≤ C·(1+y²)⁻¹` (it is what proves `verticalIntegrable_...`). Hence the tail is
`≤ C·(π − 2 arctan T)`, via `integral_one_div_one_add_sq` (= π on ℝ) and
`intervalIntegral.integral_one_div_one_add_sq` (= arctan b − arctan a) plus
`integral_Icc_eq_integral_Ioc` / `intervalIntegral.integral_of_le` to match the set integral. Doing that
closes the last parameter; after it, choosing `z, δ, T, H, σ` is arithmetic.

**Still no decay claim.** The chain bounds the smoothed sum by explicit quantities; it does not yet
assert that they are small for any particular `f`.

See `mem:route_e/halasz_perron_assembly_2026_08_07`.
