import GaloisForLFunctions.HTGeometry.HausdorffStrictCddCone

/-!
# The phase kernel as an odd-spin sinh series

Inside the disc `√y·e^{|θ|} < 1` both arctangents in the phase kernel are given by their Maclaurin
series, and subtracting them pairs each exponential with its reciprocal:

`K(y,θ) = 8 ∑_m (−1)^m y^m sinh((2m+1)θ)/(2m+1)`.

This is equation `(4)` of the CDD cone card in its measure-theoretic form: the coefficient of
`sinh((2m+1)θ)` is `8(−1)^m y^m/(2m+1)`, so integrating against a source measure turns the
coefficients into its moments.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **The odd-spin expansion of the phase kernel.** -/
theorem hasSum_cddPhaseKernel {y θ : ℝ} (hy : 0 ≤ y)
    (hyt : Real.sqrt y * Real.exp |θ| < 1) :
    HasSum (fun m : ℕ =>
        8 * ((-1 : ℝ) ^ m * y ^ m * Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) /
          ((2 * m + 1 : ℕ) : ℝ)))
      (cddPhaseKernel y θ) := by
  rcases eq_or_lt_of_le hy with hzero | hpos
  · -- the zero shell: only the constant term survives
    have hy0 : y = 0 := hzero.symm
    subst hy0
    have hsingle : ∀ m : ℕ, m ≠ 0 →
        8 * ((-1 : ℝ) ^ m * (0 : ℝ) ^ m * Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) /
          ((2 * m + 1 : ℕ) : ℝ)) = 0 := by
      intro m hm
      rw [zero_pow hm]
      ring
    have h := hasSum_single (f := fun m : ℕ =>
      8 * ((-1 : ℝ) ^ m * (0 : ℝ) ^ m * Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) /
        ((2 * m + 1 : ℕ) : ℝ))) 0 hsingle
    have hval : 8 * ((-1 : ℝ) ^ (0 : ℕ) * (0 : ℝ) ^ (0 : ℕ) *
        Real.sinh (((2 * 0 + 1 : ℕ) : ℝ) * θ) / ((2 * 0 + 1 : ℕ) : ℝ))
        = cddPhaseKernel 0 θ := by
      rw [cddPhaseKernel_zero]
      norm_num
    rwa [hval] at h
  · -- a positive shell: subtract the two arctangent series
    set u : ℝ := Real.sqrt y with hu
    have hu0 : 0 < u := Real.sqrt_pos.mpr hpos
    have husq : u ^ (2 : ℕ) = y := Real.sq_sqrt hy
    have hexp_le : ∀ t : ℝ, Real.exp t ≤ Real.exp |t| :=
      fun t => Real.exp_le_exp.mpr (le_abs_self t)
    have h1 : ‖u * Real.exp θ‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hexp_le θ) hu0.le) hyt
    have h2 : ‖u * Real.exp (-θ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ hu0.le) hyt
      exact Real.exp_le_exp.mpr (neg_le_abs θ)
    have s3 := (Real.hasSum_arctan h1).sub (Real.hasSum_arctan h2)
    have s4 := s3.mul_left (4 / u)
    have hterm : ∀ m : ℕ,
        4 / u * ((-1 : ℝ) ^ m * (u * Real.exp θ) ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ)
            - (-1 : ℝ) ^ m * (u * Real.exp (-θ)) ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ))
          = 8 * ((-1 : ℝ) ^ m * y ^ m * Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) /
            ((2 * m + 1 : ℕ) : ℝ)) := by
      intro m
      have hpow : ∀ t : ℝ, (u * Real.exp t) ^ (2 * m + 1)
          = y ^ m * u * Real.exp (((2 * m + 1 : ℕ) : ℝ) * t) := by
        intro t
        rw [mul_pow, ← Real.exp_nat_mul]
        have : u ^ (2 * m + 1) = y ^ m * u := by
          rw [pow_succ, pow_mul, husq]
        rw [this]
      rw [hpow θ, hpow (-θ), Real.sinh_eq]
      have hune : u ≠ 0 := ne_of_gt hu0
      have hneg : ((2 * m + 1 : ℕ) : ℝ) * -θ = -(((2 * m + 1 : ℕ) : ℝ) * θ) := by ring
      rw [hneg]
      field_simp
      ring
    have hval : 4 / u * (Real.arctan (u * Real.exp θ) - Real.arctan (u * Real.exp (-θ)))
        = cddPhaseKernel y θ := by
      rw [cddPhaseKernel, if_pos hpos, ← hu]
      field_simp
    rw [hval] at s4
    exact s4.congr_fun fun m => (hterm m).symm

/-- The `tsum` form of the expansion. -/
theorem cddPhaseKernel_eq_tsum {y θ : ℝ} (hy : 0 ≤ y)
    (hyt : Real.sqrt y * Real.exp |θ| < 1) :
    cddPhaseKernel y θ
      = ∑' m : ℕ, 8 * ((-1 : ℝ) ^ m * y ^ m * Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) /
          ((2 * m + 1 : ℕ) : ℝ)) :=
  (hasSum_cddPhaseKernel hy hyt).tsum_eq.symm

/-! ## Termwise integration against a source measure -/

open MeasureTheory

/-- `|sinh t| ≤ exp |t|`. -/
theorem abs_sinh_le_exp_abs (t : ℝ) : |Real.sinh t| ≤ Real.exp |t| := by
  rw [Real.sinh_eq]
  have h1 : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.mpr (le_abs_self t)
  have h2 : Real.exp (-t) ≤ Real.exp |t| := Real.exp_le_exp.mpr (neg_le_abs t)
  have h3 : 0 < Real.exp t := Real.exp_pos t
  have h4 : 0 < Real.exp (-t) := Real.exp_pos (-t)
  rw [abs_le]
  constructor <;> linarith

/-- **Equation `(11) = (13)`.**  For a source almost everywhere carried by `[0,R²]` and a rapidity
inside the strip `R·exp|θ| < 1`, the phase is the odd-spin series in the moments. -/
theorem hasSum_hausdorffCDDPhase (ν : Measure HausdorffSourceSpace) [IsFiniteMeasure ν]
    {R θ : ℝ} (hR0 : 0 ≤ R)
    (hcar : ∀ᵐ y : HausdorffSourceSpace ∂ν, (y : ℝ) ≤ R ^ (2 : ℕ))
    (hθ : R * Real.exp |θ| < 1) :
    HasSum (fun m : ℕ =>
        8 * ((-1 : ℝ) ^ m * hausdorffMoment ν m *
          Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) / ((2 * m + 1 : ℕ) : ℝ)))
      (hausdorffCDDPhase ν θ) := by
  classical
  set F : ℕ → HausdorffSourceSpace → ℝ := fun m y =>
    8 * ((-1 : ℝ) ^ m * (y : ℝ) ^ m * Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) /
      ((2 * m + 1 : ℕ) : ℝ)) with hF
  have hint : ∀ m : ℕ, Integrable (F m) ν := by
    intro m
    exact integrable_of_continuous ν (by fun_prop)
  set q : ℝ := R ^ (2 : ℕ) * Real.exp (2 * |θ|) with hq
  have hq0 : 0 ≤ q := by positivity
  have hexp2 : Real.exp |θ| ^ (2 : ℕ) = Real.exp (2 * |θ|) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hq1 : q < 1 := by
    have hnn : 0 ≤ R * Real.exp |θ| := by positivity
    have hprod : (R * Real.exp |θ|) ^ (2 : ℕ) < 1 := by nlinarith
    have heq : (R * Real.exp |θ|) ^ (2 : ℕ) = q := by rw [hq, mul_pow, hexp2]
    linarith [heq ▸ hprod]
  have hbound : ∀ m : ℕ, ∀ᵐ y : HausdorffSourceSpace ∂ν,
      ‖F m y‖ ≤ 8 * Real.exp |θ| * q ^ m := by
    intro m
    filter_upwards [hcar] with y hy
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := y.2.1
    have hden : (1 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℕ) ≤ 2 * m + 1 := by omega
      exact_mod_cast h1
    have hdenpos : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by linarith
    have hypow : (y : ℝ) ^ m ≤ (R ^ (2 : ℕ)) ^ m := pow_le_pow_left₀ hy0 hy m
    have hsinh : |Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ)|
        ≤ Real.exp |θ| * Real.exp (2 * |θ|) ^ m := by
      refine le_trans (abs_sinh_le_exp_abs _) (le_of_eq ?_)
      rw [abs_mul, Nat.abs_cast, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have hnorm : ‖F m y‖
        = 8 * ((y : ℝ) ^ m * |Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ)|) /
            ((2 * m + 1 : ℕ) : ℝ) := by
      simp only [hF, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg hy0, abs_of_pos hdenpos]
      norm_num
      ring
    rw [hnorm]
    have hnum : (y : ℝ) ^ m * |Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ)|
        ≤ (R ^ (2 : ℕ)) ^ m * (Real.exp |θ| * Real.exp (2 * |θ|) ^ m) :=
      mul_le_mul hypow hsinh (abs_nonneg _) (pow_nonneg (by positivity) m)
    have hqm : (R ^ (2 : ℕ)) ^ m * (Real.exp |θ| * Real.exp (2 * |θ|) ^ m)
        = Real.exp |θ| * q ^ m := by
      rw [hq, mul_pow]
      ring
    rw [hqm] at hnum
    have hnn8 : (0 : ℝ) ≤ 8 * ((y : ℝ) ^ m * |Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ)|) :=
      mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hy0 m) (abs_nonneg _))
    refine le_trans (div_le_self hnn8 hden) ?_
    linarith
  have hsummable : Summable fun m : ℕ => ∫ y, ‖F m y‖ ∂ν := by
    have hmaj : Summable fun m : ℕ =>
        (ν Set.univ).toReal * (8 * Real.exp |θ| * q ^ m) := by
      have hgeo : Summable fun m : ℕ => q ^ m := summable_geometric_of_lt_one hq0 hq1
      simpa [mul_assoc] using (hgeo.mul_left ((ν Set.univ).toReal * (8 * Real.exp |θ|)))
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun y => norm_nonneg _)
      (fun m => ?_) hmaj
    have hle := integral_mono_ae ((hint m).norm) (integrable_const (8 * Real.exp |θ| * q ^ m))
      (hbound m)
    refine le_trans hle (le_of_eq ?_)
    rw [integral_const, smul_eq_mul, MeasureTheory.measureReal_def]
  have hmain := hasSum_integral_of_summable_integral_norm hint hsummable
  have hterm : ∀ m : ℕ, ∫ y, F m y ∂ν
      = 8 * ((-1 : ℝ) ^ m * hausdorffMoment ν m *
          Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) / ((2 * m + 1 : ℕ) : ℝ)) := by
    intro m
    have hrw : ∀ y : HausdorffSourceSpace, F m y
        = (8 * ((-1 : ℝ) ^ m * Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) /
            ((2 * m + 1 : ℕ) : ℝ))) * (y : ℝ) ^ m := by
      intro y
      rw [hF]
      ring
    calc ∫ y, F m y ∂ν
        = ∫ y, (8 * ((-1 : ℝ) ^ m * Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) /
            ((2 * m + 1 : ℕ) : ℝ))) * (y : ℝ) ^ m ∂ν := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun y => hrw y)
      _ = (8 * ((-1 : ℝ) ^ m * Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) /
            ((2 * m + 1 : ℕ) : ℝ))) * hausdorffMoment ν m := by
          rw [integral_const_mul, hausdorffMoment]
      _ = 8 * ((-1 : ℝ) ^ m * hausdorffMoment ν m *
            Real.sinh (((2 * m + 1 : ℕ) : ℝ) * θ) / ((2 * m + 1 : ℕ) : ℝ)) := by ring
  have hlimit : ∫ y, ∑' m : ℕ, F m y ∂ν = hausdorffCDDPhase ν θ := by
    rw [hausdorffCDDPhase]
    refine integral_congr_ae ?_
    filter_upwards [hcar] with y hy
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := y.2.1
    have hsq : Real.sqrt (y : ℝ) ≤ R := by
      rw [show R = Real.sqrt (R ^ (2 : ℕ)) from (Real.sqrt_sq hR0).symm]
      exact Real.sqrt_le_sqrt hy
    have hlt : Real.sqrt (y : ℝ) * Real.exp |θ| < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le) hθ
    exact (cddPhaseKernel_eq_tsum hy0 hlt).symm
  rw [hlimit] at hmain
  exact hmain.congr_fun fun m => (hterm m).symm

end GaloisForLFunctions.HTGeometry
