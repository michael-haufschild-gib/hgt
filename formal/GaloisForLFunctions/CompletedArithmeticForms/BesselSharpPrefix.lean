import GaloisForLFunctions.CompletedArithmeticForms.BesselCompleteGammaMass
import GaloisForLFunctions.BlackHoleRingdown.TheSharpDecayOfTheBesselKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Gamma-scale costs of finite radial prefixes

The sharp contour envelope costs one inverse radial power and only one
frequency power. Integrating a finite radial prefix therefore preserves
the exact exponential Gamma scale with an explicit algebraic cost.
-/

open Complex Set MeasureTheory Filter
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms
open GaloisForLFunctions.HTGeometry

/-- The sharp imaginary-order envelope is integrable against every positive radial power. -/
theorem abs_besselRadialValue_sharp {u τ : ℝ} (hu : 0 < u) (hτ : 0 ≤ τ) :
    |besselRadialValue τ u| ≤
      Real.exp 1 * Real.pi * (1 + 2 * τ) / u * Real.exp (-Real.pi * τ) := by
  let ν : ℂ := ((2 * τ : ℝ) : ℂ) * I
  have hνre : ν.re = 0 := by simp [ν]
  have hνim : ν.im = 2 * τ := by simp [ν]
  have hh := GaloisForLFunctions.BlackHoleRingdown.norm_modifiedBesselKOrder_sharp_of_nonneg
    (x := 2 * u) (by positivity) (ν := ν) (by rw [hνim]; positivity)
    (R := 0) (by rw [hνre]; simp) (B := 1) (by norm_num)
  rw [hνim] at hh
  norm_num only [Nat.factorial_one, Nat.cast_one, one_mul, mul_one, pow_one] at hh
  rw [show Real.pi * (2 * τ) / 2 = Real.pi * τ by ring] at hh
  have he : Real.exp (-(2 * u / (Real.pi * (1 + 2 * τ)))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hpay := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he
      (by positivity : 0 ≤ Real.exp 1 * (2 * Real.pi) * ((1 + 2 * τ) / (2 * u))))
    (Real.exp_pos (-(Real.pi * τ))).le
  calc
    _ ≤ ‖modifiedBesselKOrder (2 * u) ν‖ := Complex.abs_re_le_norm _
    _ ≤ _ := hh
    _ ≤ _ := hpay
    _ = _ := by ring

/-- A finite prefix costs only one frequency power on the exact Gamma exponential scale. -/
theorem abs_besselPowerTail_prefix_le {q p τ : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hτ : 0 ≤ τ) :
    |besselPowerTail p τ 0 - besselPowerTail p τ q| ≤
      (Real.exp 1 * Real.pi * (q ^ p / p)) * (1 + 2 * τ) * Real.exp (-Real.pi * τ) := by
  let C : ℝ := Real.exp 1 * Real.pi * (1 + 2 * τ) * Real.exp (-Real.pi * τ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hi := integrableOn_besselPowerIntegrand_zero (by linarith only [hp] : -1 < p) τ
  have hcut : besselPowerTail p τ 0 - besselPowerTail p τ q =
      ∫ u in (0 : ℝ)..q, u ^ p * besselRadialValue τ u :=
    intervalIntegral.integral_Ioi_sub_Ioi' hi (hi.mono_set (Ioi_subset_Ioi hq.le))
  rw [hcut, intervalIntegral.integral_of_le hq.le]
  have hpI : IntegrableOn (fun u : ℝ => u ^ (p - 1)) (Ioc 0 q) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hq.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith only [hp] : -1 < p - 1))
  have hbound (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) q) :
      ‖u ^ p * besselRadialValue τ u‖ ≤ C * u ^ (p - 1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu.1.le p)]
    calc
      _ ≤ u ^ p * (Real.exp 1 * Real.pi * (1 + 2 * τ) / u * Real.exp (-Real.pi * τ)) :=
        mul_le_mul_of_nonneg_left (abs_besselRadialValue_sharp hu.1 hτ)
          (Real.rpow_nonneg hu.1.le p)
      _ = _ := by
        rw [Real.rpow_sub hu.1, Real.rpow_one]
        dsimp only [C]
        ring
  have hm := setIntegral_mono_on (hi.mono_set Ioc_subset_Ioi_self).norm
    (hpI.const_mul C) measurableSet_Ioc hbound
  have hpow : (∫ u in Ioc (0 : ℝ) q, u ^ (p - 1)) = q ^ p / p := by
    rw [← intervalIntegral.integral_of_le hq.le,
      integral_rpow (Or.inl (by linarith only [hp] : -1 < p - 1)), sub_add_cancel,
      Real.zero_rpow hp.ne', sub_zero]
  calc
    _ ≤ ∫ u in Ioc (0 : ℝ) q, ‖u ^ p * besselRadialValue τ u‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Ioc 0 q)) (fun u : ℝ => u ^ p * besselRadialValue τ u)
    _ ≤ _ := hm
    _ = _ := by rw [integral_const_mul, hpow]; dsimp only [C]; ring

/-- The complete signed density has an exact Gamma difference at cutoff zero. -/
theorem besselFirstAtomTailDensity_zero_eq (τ : ℝ) :
    besselFirstAtomTailDensity τ 0 =
      ‖Complex.Gamma ((9 / 4 : ℂ) + (τ : ℂ) * I)‖ ^ 2 -
        (3 / 2 : ℝ) * ‖Complex.Gamma ((5 / 4 : ℂ) + (τ : ℂ) * I)‖ ^ 2 := by
  rw [besselFirstAtomTailDensity, Real.zero_rpow (by norm_num : (5 / 2 : ℝ) ≠ 0)]
  simp only [mul_zero, zero_mul, sub_zero]
  rw [besselPowerTail_zero_eq_gamma (by norm_num : (-1 : ℝ) < 7 / 2),
    besselPowerTail_zero_eq_gamma (by norm_num : (-1 : ℝ) < 3 / 2)]
  norm_num
  <;> ring

/-- The finite-cutoff error retains an explicit radial cost on the exact Gamma exponential scale. -/
def besselDensityPrefixCost (q : ℝ) : ℝ :=
  Real.exp 1 * Real.pi * ((8 / 7 : ℝ) * q ^ (7 / 2 : ℝ) + 10 * q ^ (3 / 2 : ℝ))

theorem besselDensityPrefixCost_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ besselDensityPrefixCost q := by
  unfold besselDensityPrefixCost
  positivity

/-- The complete signed density differs from its Gamma mass by a paid finite prefix. -/
theorem abs_besselFirstAtomTailDensity_sub_zero_le {q τ : ℝ} (hq : 0 < q) (hτ : 0 ≤ τ) :
    |besselFirstAtomTailDensity τ q - besselFirstAtomTailDensity τ 0| ≤
      besselDensityPrefixCost q * (1 + 2 * τ) * Real.exp (-Real.pi * τ) := by
  have h7 := abs_besselPowerTail_prefix_le hq (by norm_num : (0 : ℝ) < 7 / 2) hτ
  have h3 := abs_besselPowerTail_prefix_le hq (by norm_num : (0 : ℝ) < 3 / 2) hτ
  have hK := abs_besselRadialValue_sharp hq hτ
  have h7' := mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ 4)
  have h3' := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 6)
  have hK' := mul_le_mul_of_nonneg_left hK
    (by positivity : 0 ≤ 6 * q ^ (5 / 2 : ℝ))
  have he : besselFirstAtomTailDensity τ q - besselFirstAtomTailDensity τ 0 =
      4 * (besselPowerTail (7 / 2) τ q - besselPowerTail (7 / 2) τ 0) -
        6 * (besselPowerTail (3 / 2) τ q - besselPowerTail (3 / 2) τ 0) -
          6 * q ^ (5 / 2 : ℝ) * besselRadialValue τ q := by
    rw [besselFirstAtomTailDensity, besselFirstAtomTailDensity,
      Real.zero_rpow (by norm_num : (5 / 2 : ℝ) ≠ 0)]
    ring
  have htri : |besselFirstAtomTailDensity τ q - besselFirstAtomTailDensity τ 0| ≤
      4 * |besselPowerTail (7 / 2) τ 0 - besselPowerTail (7 / 2) τ q| +
        6 * |besselPowerTail (3 / 2) τ 0 - besselPowerTail (3 / 2) τ q| +
          (6 * q ^ (5 / 2 : ℝ)) * |besselRadialValue τ q| := by
    rw [he]
    have hh := (abs_sub
      (4 * (besselPowerTail (7 / 2) τ q - besselPowerTail (7 / 2) τ 0) -
        6 * (besselPowerTail (3 / 2) τ q - besselPowerTail (3 / 2) τ 0))
      (6 * q ^ (5 / 2 : ℝ) * besselRadialValue τ q)).trans
        (add_le_add_right (abs_sub _ _) _)
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
      abs_of_nonneg (Real.rpow_nonneg hq.le (5 / 2)), abs_sub_comm] using hh
  have hpow : q ^ (5 / 2 : ℝ) = q ^ (3 / 2 : ℝ) * q := by
    calc
      _ = q ^ ((3 / 2 : ℝ) + 1) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hq, Real.rpow_one]
  refine htri.trans ((add_le_add (add_le_add h7' h3') hK').trans_eq ?_)
  rw [hpow]
  unfold besselDensityPrefixCost
  field_simp [hq.ne']
  <;> ring

#print axioms abs_besselRadialValue_sharp
#print axioms abs_besselPowerTail_prefix_le
#print axioms abs_besselFirstAtomTailDensity_sub_zero_le

end GaloisForLFunctions.CompletedArithmeticForms
