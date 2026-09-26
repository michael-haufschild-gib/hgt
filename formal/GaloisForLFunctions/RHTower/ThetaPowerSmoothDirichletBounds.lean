import GaloisForLFunctions.RHTower.ThetaPowerDirichletSplit
import GaloisForLFunctions.RHTower.ThetaPowerCoefficientMass
import GaloisForLFunctions.RHTower.ShiftedDirichletTarget

/-!
# Bounds and the vertical-shift decomposition of the smoothed theta-power series

With `α = a/4 ∈ (0, 1]` and `0 ≤ Re z ≤ 2`, `|(n+α)^{-z}| ≤ α^{-2}`.  The weights `|b_n| e^{-λ_n δ}` are
summable, so `D^δ(z) = Σ b_n e^{-λ_n δ} (n+α)^{-z}` is bounded by `α^{-2} Σ |b_n| e^{-λ_n δ}` and continuous
on the strip `0 < Re z < 2`.  A vertical shift multiplies the `n`-th term by `e^{i ω_n t}` with
`ω_n = -log(n+α)`, which gives, for `0 < Re ζ < 2`,

  `D(ζ + it) = Σ_{n<M} β_n(ζ) e^{-λ_n δ} e^{iω_n t} + Σ_{n ≥ M} β_n(ζ+it) e^{-λ_n δ} + E^δ(ζ + it)`,

`β_n(z) = b_n (n+α)^{-z}`.
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

variable {a : ℝ}

/-- `x^{-s} ≤ x^{-s₁} + x^{-s₂}` for `x > 0` and `s ∈ [s₁, s₂]`. -/
theorem rpow_neg_le_add {x s s₁ s₂ : ℝ} (hx : 0 < x) (h₁ : s₁ ≤ s) (h₂ : s ≤ s₂) :
    x ^ (-s) ≤ x ^ (-s₁) + x ^ (-s₂) := by
  rcases le_total 1 x with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h (show -s ≤ -s₁ by linarith)
    linarith [Real.rpow_nonneg hx.le (-s₂)]
  · have := Real.rpow_le_rpow_of_exponent_ge hx h (show -s₂ ≤ -s by linarith)
    linarith [Real.rpow_nonneg hx.le (-s₁)]

/-- `|(n+α)^{-z}| ≤ α^{-2}` for `0 < α ≤ 1` and `0 ≤ Re z ≤ 2`. -/
theorem norm_shift_cpow_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (n : ℕ) {z : ℂ} (hz0 : 0 ≤ z.re)
    (hz2 : z.re ≤ 2) : ‖(((n : ℝ) + α : ℝ) : ℂ) ^ (-z)‖ ≤ α ^ (-2 : ℝ) := by
  have hpos : 0 < (n : ℝ) + α := by positivity
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re]
  calc ((n : ℝ) + α) ^ (-z.re) ≤ α ^ (-z.re) :=
        Real.rpow_le_rpow_of_nonpos hα0 (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)
    _ ≤ α ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by linarith)

/-- `|β_n(z)|² ≤ |b_n|² ((n+α)^{-2s₁} + (n+α)^{-2s₂})` for `s₁ ≤ Re z ≤ s₂`. -/
theorem norm_shiftedTerm_sq_le {α : ℝ} (hα : 0 < α) (b : ℕ → ℂ) (n : ℕ) {z : ℂ} {s₁ s₂ : ℝ}
    (h₁ : s₁ ≤ z.re) (h₂ : z.re ≤ s₂) :
    ‖shiftedTerm α b n z‖ ^ 2 ≤
      ‖b n‖ ^ 2 * (((n : ℝ) + α) ^ (-(2 * s₁)) + ((n : ℝ) + α) ^ (-(2 * s₂))) := by
  have hpos : 0 < (n : ℝ) + α := by positivity
  unfold shiftedTerm
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, mul_pow,
    ← Real.rpow_natCast (((n : ℝ) + α) ^ (-z.re)), ← Real.rpow_mul hpos.le]
  gcongr
  push_cast
  have := rpow_neg_le_add (x := (n : ℝ) + α) hpos (show 2 * s₁ ≤ 2 * z.re by linarith)
    (show 2 * z.re ≤ 2 * s₂ by linarith)
  rwa [show -z.re * 2 = -(2 * z.re) by ring]

/-- The smoothing weights `e^{-λ_n δ}`. -/
def thetaPowerSmoothWeight (a δ : ℝ) (n : ℕ) : ℝ := Real.exp (-(thetaPowerFreq a n * δ))

theorem thetaPowerSmoothWeight_pos (a δ : ℝ) (n : ℕ) : 0 < thetaPowerSmoothWeight a δ n :=
  Real.exp_pos _

theorem thetaPowerSmoothWeight_le_one (ha : 0 < a) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    thetaPowerSmoothWeight a δ n ≤ 1 := by
  unfold thetaPowerSmoothWeight
  rw [Real.exp_le_one_iff]
  have := thetaPowerFreq_pos ha n
  nlinarith

/-- `e^{-λ_n δ} → 1` as `δ → 0⁺`. -/
theorem tendsto_thetaPowerSmoothWeight (a : ℝ) (n : ℕ) :
    Tendsto (fun δ => thetaPowerSmoothWeight a δ n) (𝓝 0) (𝓝 1) := by
  unfold thetaPowerSmoothWeight
  have : Continuous fun δ : ℝ => Real.exp (-(thetaPowerFreq a n * δ)) := by fun_prop
  simpa using this.tendsto 0

/-- The weights `|b_n| e^{-λ_n δ}` are summable. -/
theorem summable_thetaPowerSmoothWeight (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    Summable fun n : ℕ => ‖thetaPowerCoeff a n‖ * thetaPowerSmoothWeight a δ n := by
  refine ((summable_norm_coeff_exp ha hδ).mul_left (Real.exp (-(π * (a / 4) * δ)))).congr fun n => ?_
  simp only [thetaPowerSmoothWeight, thetaPowerFreq]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- `D^δ` in terms of the shifted terms `β_n`. -/
theorem thetaPowerSmoothDirichlet_eq (a δ : ℝ) (z : ℂ) :
    thetaPowerSmoothDirichlet a δ z =
      ∑' n, shiftedTerm (a / 4) (thetaPowerCoeff a) n z * (thetaPowerSmoothWeight a δ n : ℂ) := by
  unfold thetaPowerSmoothDirichlet shiftedTerm thetaPowerSmoothWeight
  exact tsum_congr fun n => by ring

/-- Termwise bound on the strip `0 ≤ Re z ≤ 2`. -/
theorem norm_shiftedTerm_mul_weight_le (ha0 : 0 < a) (ha4 : a ≤ 4) (δ : ℝ) (n : ℕ) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz2 : z.re ≤ 2) :
    ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n z * (thetaPowerSmoothWeight a δ n : ℂ)‖ ≤
      ‖thetaPowerCoeff a n‖ * thetaPowerSmoothWeight a δ n * (a / 4) ^ (-2 : ℝ) := by
  unfold shiftedTerm
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (thetaPowerSmoothWeight_pos a δ n).le]
  have h := norm_shift_cpow_le (α := a / 4) (by positivity) (by linarith) n hz0 hz2
  have hw := (thetaPowerSmoothWeight_pos a δ n).le
  calc ‖thetaPowerCoeff a n‖ * ‖(((n : ℝ) + a / 4 : ℝ) : ℂ) ^ (-z)‖ * thetaPowerSmoothWeight a δ n
      ≤ ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) * thetaPowerSmoothWeight a δ n := by gcongr
    _ = _ := by ring

theorem summable_shiftedTerm_mul_weight (ha0 : 0 < a) (ha4 : a ≤ 4) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz2 : z.re ≤ 2) :
    Summable fun n => shiftedTerm (a / 4) (thetaPowerCoeff a) n z * (thetaPowerSmoothWeight a δ n : ℂ) :=
  Summable.of_norm_bounded ((summable_thetaPowerSmoothWeight ha0.le hδ).mul_right _)
    fun n => norm_shiftedTerm_mul_weight_le ha0 ha4 δ n hz0 hz2

/-- **Uniform bound** `|D^δ(z)| ≤ α^{-2} Σ |b_n| e^{-λ_n δ}` on `0 ≤ Re z ≤ 2`. -/
theorem norm_thetaPowerSmoothDirichlet_le (ha0 : 0 < a) (ha4 : a ≤ 4) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz2 : z.re ≤ 2) :
    ‖thetaPowerSmoothDirichlet a δ z‖ ≤
      (∑' n, ‖thetaPowerCoeff a n‖ * thetaPowerSmoothWeight a δ n) * (a / 4) ^ (-2 : ℝ) := by
  rw [thetaPowerSmoothDirichlet_eq, ← tsum_mul_right]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact (summable_shiftedTerm_mul_weight ha0 ha4 hδ hz0 hz2).norm
  · exact (summable_shiftedTerm_mul_weight ha0 ha4 hδ hz0 hz2).norm.tsum_le_tsum
      (fun n => norm_shiftedTerm_mul_weight_le ha0 ha4 δ n hz0 hz2)
      ((summable_thetaPowerSmoothWeight ha0.le hδ).mul_right _)

/-- **Tail bound** `|Σ_{n ≥ M} β_n(z) e^{-λ_n δ}| ≤ α^{-2} Σ_{n ≥ M} |b_n| e^{-λ_n δ}`. -/
theorem norm_smoothTail_le (ha0 : 0 < a) (ha4 : a ≤ 4) {δ : ℝ} (hδ : 0 < δ) (M : ℕ) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz2 : z.re ≤ 2) :
    ‖∑' k, shiftedTerm (a / 4) (thetaPowerCoeff a) (k + M) z * (thetaPowerSmoothWeight a δ (k + M) : ℂ)‖ ≤
      (∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) * (a / 4) ^ (-2 : ℝ) := by
  have hs := (summable_nat_add_iff M).mpr (summable_thetaPowerSmoothWeight ha0.le hδ)
  have ht := (summable_nat_add_iff M).mpr (summable_shiftedTerm_mul_weight ha0 ha4 hδ hz0 hz2)
  rw [← tsum_mul_right]
  refine (norm_tsum_le_tsum_norm ht.norm).trans ?_
  exact ht.norm.tsum_le_tsum (fun k => norm_shiftedTerm_mul_weight_le ha0 ha4 δ (k + M) hz0 hz2)
    (hs.mul_right _)

/-- `D^δ` is continuous on the strip `0 < Re z < 2`. -/
theorem continuousOn_thetaPowerSmoothDirichlet (ha0 : 0 < a) (ha4 : a ≤ 4) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (thetaPowerSmoothDirichlet a δ) {z : ℂ | 0 < z.re ∧ z.re < 2} := by
  have heq : thetaPowerSmoothDirichlet a δ =
      fun z => ∑' n, shiftedTerm (a / 4) (thetaPowerCoeff a) n z * (thetaPowerSmoothWeight a δ n : ℂ) :=
    funext (thetaPowerSmoothDirichlet_eq a δ)
  rw [heq]
  refine continuousOn_tsum (fun n => ?_) ((summable_thetaPowerSmoothWeight ha0.le hδ).mul_right _)
    fun n z hz => norm_shiftedTerm_mul_weight_le ha0 ha4 δ n hz.1.le hz.2.le
  exact ((differentiable_shiftedTerm (by positivity) _ n).continuous.mul continuous_const).continuousOn

/-- **Vertical shift.** `β_n(z + it) = β_n(z) e^{iω_n t}`, `ω_n = -log(n+α)`. -/
theorem shiftedTerm_add_mul_I {α : ℝ} (hα : 0 < α) (b : ℕ → ℂ) (n : ℕ) (z : ℂ) (t : ℝ) :
    shiftedTerm α b n (z + t * I) =
      shiftedTerm α b n z * Complex.exp ((-Real.log ((n : ℝ) + α) * t : ℝ) * I) := by
  unfold shiftedTerm
  have hpos : 0 < (n : ℝ) + α := by positivity
  have hne : (((n : ℝ) + α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne, mul_assoc, ← Complex.exp_add,
    ← Complex.ofReal_log hpos.le]
  congr 2
  push_cast
  ring

/-- **Decomposition along a vertical shift.** For `0 < Re ζ < 2`, `t ∈ ℝ` and `M ∈ ℕ`. -/
theorem thetaPowerDirichlet_shift_decomp (ha0 : 0 < a) (ha4 : a ≤ 4) {δ : ℝ} (hδ : 0 < δ) {ζ : ℂ}
    (hζ0 : 0 < ζ.re) (hζ2 : ζ.re < 2) (t : ℝ) (M : ℕ) :
    thetaPowerDirichlet a (ζ + t * I) =
      ∑ n ∈ Finset.range M, shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ *
          (thetaPowerSmoothWeight a δ n : ℂ) *
          Complex.exp ((-Real.log ((n : ℝ) + a / 4) * t : ℝ) * I) +
        ∑' k, shiftedTerm (a / 4) (thetaPowerCoeff a) (k + M) (ζ + t * I) *
          (thetaPowerSmoothWeight a δ (k + M) : ℂ) +
        thetaPowerDirichletError a δ (ζ + t * I) := by
  have hre : (ζ + t * I).re = ζ.re := by simp
  rw [thetaPowerDirichlet_split ha0 hδ (by rw [hre]; exact hζ0), thetaPowerSmoothDirichlet_eq]
  congr 1
  rw [← (summable_shiftedTerm_mul_weight ha0 ha4 hδ (by rw [hre]; exact hζ0.le)
    (by rw [hre]; exact hζ2.le)).sum_add_tsum_nat_add M]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [shiftedTerm_add_mul_I (by positivity)]
  ring

end

end RHTower
