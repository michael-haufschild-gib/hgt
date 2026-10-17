import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceJumpDomain

/-! Explicit logarithmic upper costs of the actual factorial-source family. -/

open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def factorialJumpScale (N : ℕ) : ℝ := 1000000*(N : ℝ)^5

theorem factorialJumpScale_one_le {N : ℕ} (hN : 1 ≤ N) : 1 ≤ factorialJumpScale N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : (1 : ℝ)^5 ≤ (N : ℝ)^5 := by gcongr
  unfold factorialJumpScale
  norm_num at hh
  linarith

theorem factorialSourceLeft_increment_le (n : ℕ) (x : ℝ) :
    autocorr (factorialSourceLeft n) 0-autocorr (factorialSourceLeft n) x ≤
      factorialJumpScale (n+1)*|x| := by
  have hL : (∫ u : ℝ, |factorialSourceLeft n u|) ≤ 20*((n+1 : ℕ) : ℝ) := by
    change (∫ u : ℝ, |sourceFactorialRamp (n+1) (-u)|) ≤ _
    rw [integral_neg_eq_self (fun u => |sourceFactorialRamp (n+1) u|)]
    exact integral_abs_sourceFactorialRamp_le (by omega)
  have hprod : 10000*((n+1 : ℕ) : ℝ)^4*(∫ u : ℝ, |factorialSourceLeft n u|) ≤
      factorialJumpScale (n+1) := by
    calc
      _ ≤ 10000*((n+1 : ℕ) : ℝ)^4*(20*((n+1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 200000*((n+1 : ℕ) : ℝ)^5 := by ring
      _ ≤ _ := by
        unfold factorialJumpScale
        nlinarith [show 0 ≤ ((n+1 : ℕ) : ℝ)^5 by positivity]
  exact (autocorr_increment_le_lipschitz _ (factorialSourceLeft_abs_sub_le n) x).trans
    (mul_le_mul_of_nonneg_right hprod (abs_nonneg _))

theorem factorialSourceRight_increment_le (n : ℕ) (x : ℝ) :
    autocorr (factorialSourceRight n) 0-autocorr (factorialSourceRight n) x ≤
      4000*((n+1 : ℕ) : ℝ)^2*|x| := by
  have hL : (∫ u : ℝ, |factorialSourceRight n u|) ≤ 2 :=
    integral_abs_exponentialTentSource_factorial_le (by omega)
  have hprod : 2000*((n+1 : ℕ) : ℝ)^2*(∫ u : ℝ, |factorialSourceRight n u|) ≤
      4000*((n+1 : ℕ) : ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL (show 0 ≤ 2000*((n+1 : ℕ) : ℝ)^2 by positivity)]
  exact (autocorr_increment_le_lipschitz _ (factorialSourceRight_abs_sub_le n) x).trans
    (mul_le_mul_of_nonneg_right hprod (abs_nonneg _))

theorem factorialSourceLeft_jump_energy_upper (n : ℕ) :
    biScaleLevyEnergy (factorialSourceLeft n) ≤ 3+32*(Real.log (6*factorialJumpScale (n+1))+Real.pi) := by
  have hQ := factorialJumpScale_one_le (by omega : 1 ≤ n+1)
  have hQp : 0 < factorialJumpScale (n+1) := by linarith
  have hzero : autocorr (factorialSourceLeft n) 0 ≤ 16 := by
    rw [← integral_sq_eq_autocorr_zero]
    exact factorialSourceLeft_energy_le n
  have h := levyEnergy_le_linear_log_tail (factorialSourceLeft n) hQp.le
    (factorialSourceLeft_increment_le n) (show 0 < 1/factorialJumpScale (n+1) by positivity)
    ((div_le_iff₀ hQp).2 (by linarith)) (show (0 : ℝ) ≤ 32 by norm_num)
    (fun x _ => by
      have hh := autocorr_add_nonneg (factorialSourceLeft n).hasCompactSupport (factorialSourceLeft n).continuous x
      linarith)
  have hnear : 3*factorialJumpScale (n+1)*(1/factorialJumpScale (n+1)) = 3 := by field_simp [hQp.ne']
  have hlog : 6/(1/factorialJumpScale (n+1)) = 6*factorialJumpScale (n+1) := by field_simp
  simpa only [hnear,hlog] using h

theorem factorialSourceRight_jump_energy_upper (n : ℕ) :
    biScaleLevyEnergy (factorialSourceRight n) ≤
      ((n+1 : ℕ) : ℝ)*(3+60*(Real.log (24000*((n+1 : ℕ) : ℝ))+Real.pi)) := by
  have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  have hnp : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hzero : autocorr (factorialSourceRight n) 0 ≤ 30*((n+1 : ℕ) : ℝ) := by
    rw [← integral_sq_eq_autocorr_zero]
    exact (factorialSourceRight_energy_bounds n).2
  have h := levyEnergy_le_linear_log_tail (factorialSourceRight n) (by positivity)
    (factorialSourceRight_increment_le n) (show 0 < 1/(4000*((n+1 : ℕ) : ℝ)) by positivity)
    ((div_le_iff₀ (by positivity : 0 < 4000*((n+1 : ℕ) : ℝ))).2 (by nlinarith))
    (show 0 ≤ 60*((n+1 : ℕ) : ℝ) by positivity)
    (fun x _ => by
      have hh := autocorr_add_nonneg (factorialSourceRight n).hasCompactSupport (factorialSourceRight n).continuous x
      linarith)
  have hnear : 3*(4000*((n+1 : ℕ) : ℝ)^2)*(1/(4000*((n+1 : ℕ) : ℝ))) = 3*((n+1 : ℕ) : ℝ) := by
    field_simp [hnp.ne']
  have hlog : 6/(1/(4000*((n+1 : ℕ) : ℝ))) = 24000*((n+1 : ℕ) : ℝ) := by field_simp; ring
  rw [hnear,hlog] at h
  nlinarith

def factorialSourceJumpUpper (n : ℕ) : ℝ :=
  2*Real.sqrt (n+1 : ℕ)*(6+32*(Real.log (6*factorialJumpScale (n+1))+Real.pi)+
    60*(Real.log (24000*((n+1 : ℕ) : ℝ))+Real.pi))

theorem factorialSource_jump_energy_upper (n : ℕ) :
    biScaleLevyEnergy (factorialSourcePlus n) ≤ factorialSourceJumpUpper n ∧
      biScaleLevyEnergy (factorialSourceMinus n) ≤ factorialSourceJumpUpper n := by
  have hr : 0 < Real.sqrt (n+1 : ℕ) := by positivity
  have hs : (Real.sqrt (n+1 : ℕ))^2 = ((n+1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hleft := mul_le_mul_of_nonneg_left (factorialSourceLeft_jump_energy_upper n) hr.le
  have hright := div_le_div_of_nonneg_right (factorialSourceRight_jump_energy_upper n) hr.le
  have hcancel (z : ℝ) : ((n+1 : ℕ) : ℝ)*z/Real.sqrt (n+1 : ℕ) = Real.sqrt (n+1 : ℕ)*z := by
    calc
      _ = (Real.sqrt (n+1 : ℕ))^2*z/Real.sqrt (n+1 : ℕ) := by rw [hs]
      _ = _ := by field_simp [hr.ne']
  rw [hcancel] at hright
  have hsum := factorialSource_jump_energy_sum n
  have hp := biScaleLevyEnergy_nonneg (factorialSourcePlus n).hasCompactSupport (factorialSourcePlus n).continuous
  have hm := biScaleLevyEnergy_nonneg (factorialSourceMinus n).hasCompactSupport (factorialSourceMinus n).continuous
  unfold factorialSourceJumpUpper
  constructor <;> nlinarith

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
