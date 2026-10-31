import GaloisForLFunctions.AdelicKreinGeometry.TheArchimedeanGluingFormula
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TemperedConfigurationPontryaginLaw
import GaloisForLFunctions.SquareRootThreshold.ZetaSmallApertureHeightWindowPositivity
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Weil's archimedean state counts the zeros

On the zero side Weil's correlation of the cubic spline is the exponential sum
`ratCorr(u) = Σ_ρ u^{1/2−ρ} w_ρ` over the nontrivial zeros (`ratCorr_eq_tsum`), with summable
weights `w_ρ`. Against the boost, `u^{−1/2}|u^{1/2−ρ}| = u^{−Re ρ}`, and every nontrivial zero has
`Re ρ > 0`; by dominated convergence Weil's correlation grows slower than the boost along `2^N`
(`ratCorr_subBoost`).

* **Weil's archimedean state counts the zeros** (`negIndex_weilArchState_eq_add_one`,
  `negIndex_weilArchState_eq_rightZeros`): for every `c > 0`,
  `κ(ratCorr(|a|) − c|a|^{−1/2}|b|) = κ(K_ζ) + 1 = #{zeros right of the critical line} + 1`.

So the affine state that glues Weil's dilation data to the archimedean successor `−c|b|` has one
negative square more than the zeros right of the line: it has exactly one iff RH holds. The extra
square is the successor's; the boost hyperplane costs nothing because the zeros stay off the line
`Re ρ = 0`.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx cx_contDiff cx_hasCompactSupport)
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The zero-side weights of Weil's correlation of the cubic spline. -/
abbrev weilWeight (ρ : zetaZeroConfig.carrier) : ℂ :=
  zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ

theorem summable_norm_weilWeight : Summable fun ρ : zetaZeroConfig.carrier => ‖weilWeight ρ‖ :=
  ArithmeticCastelnuovoSeveri.summable_norm_Wsummand _ temperedConfig_zetaZeroConfig
    (cx_contDiff contDiff_cubicSpline) (cx_hasCompactSupport hasCompactSupport_cubicSpline)
    (cx_contDiff contDiff_cubicSpline) (cx_hasCompactSupport hasCompactSupport_cubicSpline)

/-- **The zero side of Weil's correlation**: `ratCorr(u) = Σ_ρ e^{−(log u)(ρ − 1/2)} w_ρ`. -/
theorem ratCorr_eq_tsum (v : posUnits) :
    ratCorr v = ∑' ρ : zetaZeroConfig.carrier,
      cexp (-((Real.log (((v : ℚˣ) : ℚ) : ℝ) : ℝ) : ℂ) * ((ρ : ℂ) - 1 / 2)) * weilWeight ρ := by
  rw [ratCorr_eq_zetaKernel, zetaKernel, orbitKernel_eq, W_shiftTest_shiftTest]
  refine tsum_congr fun ρ => ?_
  rw [scale_heckeLogScale]
  congr 2
  push_cast
  ring

theorem re_pos_of_mem_zetaZeroConfig (ρ : zetaZeroConfig.carrier) : 0 < (ρ : ℂ).re :=
  ρ.2.2.1

theorem re_lt_one_of_mem_zetaZeroConfig (ρ : zetaZeroConfig.carrier) : (ρ : ℂ).re < 1 :=
  ρ.2.2.2

/-- The slope `2 ∈ ℚ_{>0}`. -/
def twoPos : posUnits := ⟨Units.mk0 2 two_ne_zero, by show (0 : ℚ) < 2; norm_num⟩

theorem twoPos_pow_val (N : ℕ) : ((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ) = 2 ^ N := by
  simp [twoPos]

theorem tendsto_twoPos_pow_rpow :
    Tendsto (fun N : ℕ => ((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ))) atTop
      (𝓝 0) := by
  have e : ∀ N : ℕ, ((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) =
      ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ N := fun N => by
    rw [twoPos_pow_val, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  simp_rw [e]
  refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- **Weil's correlation grows slower than the boost**: `ratCorr(2^N u) 2^{−N/2} → 0`. -/
theorem ratCorr_subBoost (u : posUnits) :
    Tendsto (fun N : ℕ => ratCorr (twoPos ^ N * u) *
      (((((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) atTop (𝓝 0) := by
  set a : ℝ := Real.log (((u : ℚˣ) : ℚ) : ℝ)
  have hu : (0 : ℝ) < (((u : ℚˣ) : ℚ) : ℝ) := posUnits_val_pos u
  -- the terms of the series
  set f : ℕ → zetaZeroConfig.carrier → ℂ := fun N ρ =>
    cexp (-(((N : ℝ) * Real.log 2 + a : ℝ) : ℂ) * ((ρ : ℂ) - 1 / 2)) * weilWeight ρ *
      ((Real.exp (-((N : ℝ) * Real.log 2) / 2) : ℝ) : ℂ)
  have hterm : ∀ N, ratCorr (twoPos ^ N * u) *
      (((((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      ∑' ρ, f N ρ := by
    intro N
    have hlog : Real.log (((((twoPos ^ N * u : posUnits) : ℚˣ) : ℚ) : ℝ)) =
        (N : ℝ) * Real.log 2 + a := by
      have : ((((twoPos ^ N * u : posUnits) : ℚˣ) : ℚ) : ℝ) =
          (2 : ℝ) ^ N * (((u : ℚˣ) : ℚ) : ℝ) := by
        rw [← twoPos_pow_val]; push_cast; rfl
      rw [this, Real.log_mul (by positivity) hu.ne', Real.log_pow]
    have hpow : ((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) =
        Real.exp (-((N : ℝ) * Real.log 2) / 2) := by
      rw [twoPos_pow_val, Real.rpow_def_of_pos (by positivity), Real.log_pow]
      congr 1; ring
    rw [ratCorr_eq_tsum, hlog, hpow, ← tsum_mul_right]
  -- the norms
  have hnorm : ∀ N ρ, ‖f N ρ‖ =
      Real.exp (-((N : ℝ) * Real.log 2) * (ρ : ℂ).re - a * ((ρ : ℂ).re - 1 / 2)) *
        ‖weilWeight ρ‖ := by
    intro N ρ
    simp only [f, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rw [mul_right_comm, ← Real.exp_add]
    congr 2
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.one_im]
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : ∀ N ρ, ‖f N ρ‖ ≤ Real.exp (|a| / 2) * ‖weilWeight ρ‖ := by
    intro N ρ
    rw [hnorm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h0 := re_pos_of_mem_zetaZeroConfig ρ
    have h1 := re_lt_one_of_mem_zetaZeroConfig ρ
    have hN : 0 ≤ (N : ℝ) * Real.log 2 := by positivity
    have : -(a * ((ρ : ℂ).re - 1 / 2)) ≤ |a| / 2 := by
      have habs : |a * ((ρ : ℂ).re - 1 / 2)| ≤ |a| * (1 / 2) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _)
      linarith [neg_abs_le (a * ((ρ : ℂ).re - 1 / 2))]
    nlinarith
  have hlim : ∀ ρ, Tendsto (fun N => f N ρ) atTop (𝓝 0) := by
    intro ρ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [hnorm]
    have h0 := re_pos_of_mem_zetaZeroConfig ρ
    have : Tendsto (fun N : ℕ => -((N : ℝ) * Real.log 2) * (ρ : ℂ).re - a * ((ρ : ℂ).re - 1 / 2))
        atTop atBot := by
      refine tendsto_atBot_add_const_right _ _ ?_
      have : Tendsto (fun N : ℕ => (N : ℝ) * (Real.log 2 * (ρ : ℂ).re)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
      refine (tendsto_neg_atTop_atBot.comp this).congr fun N => ?_
      simp only [Function.comp_apply]; ring
    simpa using (Real.tendsto_exp_atBot.comp this).mul_const ‖weilWeight ρ‖
  simp_rw [hterm]
  have := tendsto_tsum_of_dominated_convergence (summable_norm_weilWeight.mul_left (Real.exp (|a| / 2)))
    hlim (Eventually.of_forall hbound)
  simpa using this

/-- **Weil's archimedean state counts the zeros**: `κ = κ(K_ζ) + 1`. -/
theorem negIndex_weilArchState_eq_add_one {c : ℝ} (hc : 0 < c) :
    negIndex (weilArchState c) = negIndex zetaKernel + 1 := by
  rw [negIndex_weilArchState_eq hc,
    boostPolarIndex_eq_negIndex_of_subBoost isHermKernel_ratCorr (fun N => twoPos ^ N)
      tendsto_twoPos_pow_rpow ratCorr_subBoost, negIndex_ratCorr]

/-- In terms of the zeros: `κ = #{zeros right of the critical line} + 1`. -/
theorem negIndex_weilArchState_eq_rightZeros {c : ℝ} (hc : 0 < c) :
    negIndex (weilArchState c) =
      (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard + 1 := by
  rw [negIndex_weilArchState_eq_add_one hc, negIndex_zetaKernel]

end GaloisForLFunctions.AdelicKreinGeometry
