import GaloisForLFunctions.BiScaleUncertainty.CompactProfileLipschitz
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceParameters

/-! Numeric regularity bounds for the actual narrow source. -/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem exponentialTentSource_eq (δ x : ℝ) :
    exponentialTentSource δ x = Real.exp (3*x/2)*causalTent δ x/(Real.exp δ-1)^2 := by
  unfold exponentialTentSource exponentialTentDensity
  rw [← mul_div_assoc, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem sourceFactorialWidth_le_one {N : ℕ} (hN : 1 ≤ N) : sourceFactorialWidth N ≤ 1 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (sourceFactorialWidth_bounds hN).2.trans
    ((div_le_iff₀ (by positivity : 0 < 12*(N : ℝ))).2 (by nlinarith))

theorem sourceFactorialCollar_inv_le {N : ℕ} (hN : 1 ≤ N) :
    1/sourceFactorialCollar N ≤ 15*(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := (sourceFactorialWidth_bounds hN).1.trans (sourceFactorialWidth_le_collar N)
  apply (div_le_iff₀ (sourceFactorialCollar_pos hN)).2
  have hh := (div_le_iff₀ (by positivity : 0 < 15*(N : ℝ))).1 h
  nlinarith

theorem exponentialTentSource_factorial_abs_sub_le {N : ℕ} (hN : 1 ≤ N) (x y : ℝ) :
    |exponentialTentSource (sourceFactorialWidth N) x-
      exponentialTentSource (sourceFactorialWidth N) y| ≤ 2000*(N : ℝ)^2*|x-y| := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := sourceFactorialWidth_pos hN
  have hd1 := sourceFactorialWidth_le_one hN
  have he := sourceFactorialCollar_pos hN
  have he3 : Real.exp (3*sourceFactorialWidth N) ≤ 2 :=
    (Real.exp_le_exp.mpr (by linarith)).trans (exp_four_sourceFactorialWidth_le_two hN)
  apply compact_interval_abs_sub_le (a := 0) (b := 2*sourceFactorialWidth N)
    (by positivity) (by positivity)
  · intro t ht
    simp [exponentialTentSource_eq, causalTent_zero_left _ ht]
  · intro t ht
    simp [exponentialTentSource_eq, causalTent_zero_right _ ht]
  intro u hu v hv
  have hxv : Real.exp (3*v/2) ≤ 2 :=
    (Real.exp_le_exp.mpr (by linarith [hv.2])).trans he3
  have hediff : |Real.exp (3*u/2)-Real.exp (3*v/2)| ≤ 3*|u-v| := by
    calc
      _ ≤ Real.exp (3*sourceFactorialWidth N)*|3*u/2-3*v/2| :=
        exp_abs_sub_le_of_le (by linarith [hu.2]) (by linarith [hv.2])
      _ ≤ 2*|3*u/2-3*v/2| := mul_le_mul_of_nonneg_right he3 (abs_nonneg _)
      _ = 3*|u-v| := by
        rw [show 3*u/2-3*v/2 = (3/2)*(u-v) by ring, abs_mul]
        norm_num
        ring
  have htud : |causalTent (sourceFactorialWidth N) u| ≤ sourceFactorialWidth N := by
    rw [abs_of_nonneg (causalTent_nonneg _ _)]
    exact causalTent_le hd.le u
  have hnum : |Real.exp (3*u/2)*causalTent (sourceFactorialWidth N) u-
      Real.exp (3*v/2)*causalTent (sourceFactorialWidth N) v| ≤ 5*|u-v| := by
    calc
      _ ≤ |Real.exp (3*u/2)-Real.exp (3*v/2)| * |causalTent (sourceFactorialWidth N) u|+
        |Real.exp (3*v/2)| * |causalTent (sourceFactorialWidth N) u-causalTent (sourceFactorialWidth N) v| :=
        abs_mul_sub_mul_le _ _ _ _
      _ ≤ (3*|u-v|)*sourceFactorialWidth N+2*|u-v| := by
        apply add_le_add
        · exact mul_le_mul hediff htud (abs_nonneg _) (by positivity)
        · rw [abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul hxv (causalTent_abs_sub_le _ _ _) (abs_nonneg _) (by norm_num)
      _ ≤ 5*|u-v| := by nlinarith [mul_le_mul_of_nonneg_left hd1 (abs_nonneg (u-v))]
  have hsq : 1/(sourceFactorialCollar N)^2 ≤ 225*(N : ℝ)^2 := by
    have hh := sourceFactorialCollar_inv_le hN
    have hs : (1/sourceFactorialCollar N)^2 ≤ (15*(N : ℝ))^2 := by
      gcongr
    simpa only [div_pow, one_pow, mul_pow, show (15 : ℝ)^2 = 225 by norm_num] using hs
  rw [exponentialTentSource_eq, exponentialTentSource_eq, ← sub_div, abs_div,
    abs_of_nonneg (sq_nonneg (Real.exp (sourceFactorialWidth N)-1))]
  change _/(sourceFactorialCollar N)^2 ≤ _
  calc
    _ ≤ (5*|u-v|)/(sourceFactorialCollar N)^2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = (5*|u-v|)*(1/(sourceFactorialCollar N)^2) := by ring
    _ ≤ (5*|u-v|)*(225*(N : ℝ)^2) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg (N : ℝ), abs_nonneg (u-v)]

theorem integral_abs_exponentialTentSource_factorial_le {N : ℕ} (hN : 1 ≤ N) :
    (∫ x : ℝ, |exponentialTentSource (sourceFactorialWidth N) x|) ≤ 2 := by
  have hd := sourceFactorialWidth_pos hN
  have he : Real.exp (sourceFactorialWidth N) ≤ 2 :=
    (Real.exp_le_exp.mpr (by linarith)).trans (exp_four_sourceFactorialWidth_le_two hN)
  have hrestrict : (∫ x : ℝ, |exponentialTentSource (sourceFactorialWidth N) x|) =
      ∫ x in Icc 0 (2*sourceFactorialWidth N), |exponentialTentSource (sourceFactorialWidth N) x| := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [exponentialTentSource, exponentialTentDensity_zero_of_not_mem _ hx]
  rw [hrestrict]
  calc
    _ ≤ ∫ x in Icc 0 (2*sourceFactorialWidth N), 2*exponentialTentDensity (sourceFactorialWidth N) x := by
      apply setIntegral_mono_on
        ((continuous_exponentialTentSource _).abs.integrableOn_Icc)
        ((continuous_const.mul (continuous_exponentialTentDensity _)).integrableOn_Icc) measurableSet_Icc
      intro x hx
      have hex : Real.exp (x/2) ≤ 2 := (Real.exp_le_exp.mpr (by linarith [hx.2])).trans he
      unfold exponentialTentSource
      rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (exponentialTentDensity_nonneg _ _))]
      exact mul_le_mul_of_nonneg_right hex (exponentialTentDensity_nonneg _ _)
    _ = 2 := by rw [integral_const_mul, integral_Icc_exponentialTentDensity hd, mul_one]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
