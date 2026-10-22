import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCenteredEnergy

/-!
# Nyman series expansion of the power-damped centered divisor source

For damping `ε > 0`, the divisor remainder `R_ε(x) = A_ε(x) − x/ζ(1+ε)`, with
`A_ε(x) = ∑_{n≤x} ∑_{d|n} μ(d) d^(−ε)`, has the absolutely convergent fractional-part expansion
`R_ε(x) = −∑_d μ(d) d^(−ε) {x/d}`. It follows from `A_ε(x) = ∑_d μ(d) d^(−ε) ⌊x/d⌋` and
`1/ζ(1+ε) = ∑_d μ(d) d^(−1−ε)`. Evaluated at `x = 1/t`, this expresses the centered source
`C_ε(t) = R_ε(1/t)` as the pointwise series of Nyman terms `−μ(d) d^(−ε) {1/(d t)}`, so the
Nyman prefixes converge to `C_ε` at every `t > 0`. The module also records that `1/ζ(1+ε)` is real.

## Main results

- `hasSum_pmPowerDampedDivisor_floor`: `∑_d μ(d) d^(−ε) ⌊x/d⌋ = A_ε(x)` for `x ≥ 0` (finite support).
- `pmPowerDampedDivisorRemainder_eq_fract_series`: for `ε > 0`, `x ≥ 0`, `R_ε(x) = −∑'_d μ(d) d^(−ε) {x/d}`.
- `pmPowerDampedCenteredSource_eq_nyman_tsum`: for `ε > 0`, `t > 0`, `C_ε(t) = ∑'_d −μ(d) d^(−ε) {1/(d t)}`.
- `tendsto_pmPowerDampedNymanPrefix`: the Nyman prefixes converge pointwise to `C_ε(t)`.
- `pmPowerDampedDivisorDensity_eq_ofReal_re`: `1/ζ(1+ε)` is a real number for `ε > 0`.

## Hypotheses

Unconditional apart from `0 < ε` (needed for convergence of `∑ μ(d) d^(−1−ε)`) and `x ≥ 0` or
`t > 0`. All convergence statements are pointwise; no `L²` convergence is claimed here.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open GaloisForLFunctions.NymanMellin
noncomputable section
namespace RHTower

/-- For `x ≥ 0`, `∑_d μ(d) d^(−ε) ⌊x/d⌋` has sum `A_ε(x)` (only `d ≤ x` contribute). -/
theorem hasSum_pmPowerDampedDivisor_floor (ε : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun d : ℕ => pmPowerDampedMobiusCoeff ε d * (⌊x / (d : ℝ)⌋ : ℂ))
      (pmPowerDampedDivisorSum ε x : ℂ) := by
  rw [pmPowerDampedDivisorSum_eq_floor_sum ε hx le_rfl]
  apply hasSum_sum_of_ne_finset_zero
  intro d hd
  by_cases hd0 : d = 0
  · subst d
    simp [pmPowerDampedMobiusCoeff_zero]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hgt : ⌊x⌋₊ < d := by
    have hh := mt Finset.mem_Icc.mpr hd
    omega
  have hxd : x / (d : ℝ) < 1 := (div_lt_one hdpos).mpr ((Nat.floor_lt hx).mp hgt)
  rw [← Int.natCast_floor_eq_floor (div_nonneg hx (Nat.cast_nonneg d)), Nat.floor_eq_zero.mpr hxd]
  simp

/-- For `ε > 0` and `x ≥ 0`, `∑_d μ(d) d^(−ε) {x/d}` has sum `−R_ε(x)`. -/
theorem hasSum_pmPowerDampedDivisor_fract {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun d : ℕ => pmPowerDampedMobiusCoeff ε d * ((Int.fract (x / (d : ℝ)) : ℝ) : ℂ))
      (-pmPowerDampedDivisorRemainder ε x) := by
  have hlin := (summable_pmPowerDampedDivisorDensity_terms hε).hasSum.mul_right (x : ℂ)
  rw [← pmPowerDampedDivisorDensity_eq_tsum hε] at hlin
  have h := hlin.sub (hasSum_pmPowerDampedDivisor_floor ε hx)
  have hval : pmPowerDampedDivisorDensity ε * (x : ℂ) - (pmPowerDampedDivisorSum ε x : ℂ) =
      -pmPowerDampedDivisorRemainder ε x := by
    dsimp only [pmPowerDampedDivisorRemainder]
    ring
  rw [hval] at h
  apply h.congr_fun
  intro d
  dsimp only [Int.fract]
  push_cast
  ring

/-- For `ε > 0` and `x ≥ 0`, `R_ε(x) = −∑'_d μ(d) d^(−ε) {x/d}`. -/
theorem pmPowerDampedDivisorRemainder_eq_fract_series {ε : ℝ} (hε : 0 < ε)
    {x : ℝ} (hx : 0 ≤ x) :
    pmPowerDampedDivisorRemainder ε x =
      -∑' d : ℕ, pmPowerDampedMobiusCoeff ε d * ((Int.fract (x / (d : ℝ)) : ℝ) : ℂ) := by
  rw [(hasSum_pmPowerDampedDivisor_fract hε hx).tsum_eq, neg_neg]

/-- The damped Nyman term `−μ(d) d^(−ε) {1/(d t)}`. -/
def pmPowerDampedNymanTerm (ε : ℝ) (d : ℕ) (t : ℝ) : ℂ :=
  -pmPowerDampedMobiusCoeff ε d * nymanGen (d : ℝ) t

/-- For `ε > 0` and `t > 0`, the damped Nyman terms sum to the centered source `C_ε(t)`. -/
theorem hasSum_pmPowerDampedNymanTerm {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    HasSum (fun d : ℕ => pmPowerDampedNymanTerm ε d t) (pmPowerDampedCenteredSource ε t) := by
  have h := (hasSum_pmPowerDampedDivisor_fract hε (one_div_pos.mpr ht).le).neg
  simp only [neg_neg] at h
  have he (d : ℕ) : 1 / t / (d : ℝ) = 1 / ((d : ℝ) * t) := by
    simp only [div_eq_mul_inv, one_mul, mul_inv]
    ring
  simpa only [pmPowerDampedNymanTerm, nymanGen, pmPowerDampedCenteredSource,
    he, neg_mul] using h

theorem summable_norm_pmPowerDampedNymanTerm {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    Summable (fun d : ℕ => ‖pmPowerDampedNymanTerm ε d t‖) :=
  (hasSum_pmPowerDampedNymanTerm hε ht).summable.norm

/-- For `ε > 0` and `t > 0`, `C_ε(t) = ∑'_d −μ(d) d^(−ε) {1/(d t)}`. -/
theorem pmPowerDampedCenteredSource_eq_nyman_tsum {ε : ℝ} (hε : 0 < ε)
    {t : ℝ} (ht : 0 < t) :
    pmPowerDampedCenteredSource ε t = ∑' d : ℕ, pmPowerDampedNymanTerm ε d t :=
  (hasSum_pmPowerDampedNymanTerm hε ht).tsum_eq.symm

/-- The partial sum over `d < N` of the damped Nyman terms. -/
def pmPowerDampedNymanPrefix (ε : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ d ∈ Finset.range N, pmPowerDampedNymanTerm ε d t

/-- For `ε > 0` and `t > 0`, the Nyman prefixes converge to `C_ε(t)` as `N → ∞`. -/
theorem tendsto_pmPowerDampedNymanPrefix {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => pmPowerDampedNymanPrefix ε N t) atTop
      (𝓝 (pmPowerDampedCenteredSource ε t)) := by
  have h := (hasSum_pmPowerDampedNymanTerm hε ht).summable.tendsto_sum_tsum_nat
  rw [← pmPowerDampedCenteredSource_eq_nyman_tsum hε ht] at h
  exact h

/-- For `ε > 0`, `1/ζ(1+ε)` has zero imaginary part (it is the limit of the real ratios `A_ε(x)/x`). -/
theorem pmPowerDampedDivisorDensity_im {ε : ℝ} (hε : 0 < ε) :
    (pmPowerDampedDivisorDensity ε).im = 0 := by
  have h := (Complex.continuous_im.tendsto _).comp (tendsto_pmPowerDampedDivisorSum_div hε)
  have he (x : ℝ) : ((pmPowerDampedDivisorSum ε x : ℂ) / (x : ℂ)).im = 0 := by
    rw [← Complex.ofReal_div]
    rfl
  simp only [Function.comp_def, he] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- For `ε > 0`, `1/ζ(1+ε)` equals the complex embedding of its real part. -/
theorem pmPowerDampedDivisorDensity_eq_ofReal_re {ε : ℝ} (hε : 0 < ε) :
    pmPowerDampedDivisorDensity ε = ((pmPowerDampedDivisorDensity ε).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [pmPowerDampedDivisorDensity_im hε]

end RHTower
