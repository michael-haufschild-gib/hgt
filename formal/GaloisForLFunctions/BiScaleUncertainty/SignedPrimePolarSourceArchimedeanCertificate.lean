import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalJumpBounds
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarTentJumpLower

/-! Numeric-index-only jump-energy certificate for the balanced factorial sources. -/

open MeasureTheory Set
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def factorialSourceJumpLower (n : ℕ) : ℝ :=
  6*Real.exp (-(1/2 : ℝ))*Real.sqrt (n+1 : ℕ)*Real.log ((n+1 : ℕ) : ℝ)-factorialSourceJumpError n

def factorialSourceNormalizedJumpLower (n : ℕ) : ℝ :=
  (3/23 : ℝ)*Real.exp (-(1/2 : ℝ))*Real.log ((n+1 : ℕ) : ℝ)-(41+2*Real.log (1000000 : ℝ))/6

theorem factorialSource_jump_energy_lower (n : ℕ) :
    factorialSourceJumpLower n ≤ biScaleLevyEnergy (factorialSourcePlus n) ∧
      factorialSourceJumpLower n ≤ biScaleLevyEnergy (factorialSourceMinus n) := by
  have hr : 0 < Real.sqrt (n+1 : ℕ) := by positivity
  have hs : (Real.sqrt (n+1 : ℕ))^2 = ((n+1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hscaled := div_le_div_of_nonneg_right (factorialSourceRight_jump_energy_lower n) hr.le
  have hcancel : (6*Real.exp (-(1/2 : ℝ))*((n+1 : ℕ) : ℝ)*Real.log ((n+1 : ℕ) : ℝ))/Real.sqrt (n+1 : ℕ) =
      6*Real.exp (-(1/2 : ℝ))*Real.sqrt (n+1 : ℕ)*Real.log ((n+1 : ℕ) : ℝ) := by
    calc
      _ = (6*Real.exp (-(1/2 : ℝ))*(Real.sqrt (n+1 : ℕ))^2*Real.log ((n+1 : ℕ) : ℝ))/Real.sqrt (n+1 : ℕ) := by rw [hs]
      _ = _ := by field_simp [hr.ne']
  rw [hcancel] at hscaled
  have hsum := factorialSource_jump_energy_sum n
  have hdiff := factorialSource_jump_energy_difference n
  obtain ⟨hblo,hbhi⟩ := abs_le.mp (abs_integral_sourceFactorialCausal_archWeight_le n)
  have hleft := mul_nonneg hr.le
    (biScaleLevyEnergy_nonneg (factorialSourceLeft n).hasCompactSupport (factorialSourceLeft n).continuous)
  unfold factorialSourceJumpLower
  constructor <;> linarith

theorem factorialSourceJumpError_scaled_le (n : ℕ) :
    factorialSourceJumpError n/(6*Real.sqrt (n+1 : ℕ)) ≤ (41+2*Real.log (1000000 : ℝ))/6 := by
  have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  have hnp : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hs : (Real.sqrt (n+1 : ℕ))^2 = ((n+1 : ℕ) : ℝ) := Real.sq_sqrt hnp.le
  have hden : Real.sqrt (n+1 : ℕ)*(6*Real.sqrt (n+1 : ℕ)) = 6*((n+1 : ℕ) : ℝ) := by nlinarith
  have hlogQ : Real.log (factorialJumpScale (n+1)) = Real.log (1000000 : ℝ)+5*Real.log ((n+1 : ℕ) : ℝ) := by
    unfold factorialJumpScale
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hlogN := Real.log_le_sub_one_of_pos hnp
  have hL := Real.log_le_sub_one_of_pos (show 0 < 4*((n+1 : ℕ) : ℝ)+1 by positivity)
  have hc : 0 ≤ Real.log (1000000 : ℝ) := Real.log_nonneg (by norm_num)
  have hcn := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*Real.log (1000000 : ℝ) by positivity)
  unfold factorialSourceJumpError
  rw [div_div, hden, hlogQ]
  apply (div_le_iff₀ (by positivity : 0 < 6*((n+1 : ℕ) : ℝ))).2
  nlinarith

private theorem factorialSource_normalized_lower (n : ℕ) {E e : ℝ}
    (hE : factorialSourceJumpLower n ≤ E)
    (hel : 6*Real.sqrt (n+1 : ℕ) ≤ e) (heu : e ≤ 46*Real.sqrt (n+1 : ℕ)) :
    factorialSourceNormalizedJumpLower n ≤ E/e := by
  let A := 6*Real.exp (-(1/2 : ℝ))*Real.sqrt (n+1 : ℕ)*Real.log ((n+1 : ℕ) : ℝ)
  let B := factorialSourceJumpError n
  have hr : 0 < Real.sqrt (n+1 : ℕ) := by positivity
  have he : 0 < e := by linarith
  have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  have hA : 0 ≤ A := by dsimp [A]; exact mul_nonneg (by positivity) (Real.log_nonneg hn)
  have hB : 0 ≤ B := by
    dsimp [B,factorialSourceJumpError]
    have hL : 0 ≤ Real.log (4*((n+1 : ℕ) : ℝ)+1) := Real.log_nonneg (by linarith)
    have hQ : 0 ≤ Real.log (factorialJumpScale (n+1)) := Real.log_nonneg (factorialJumpScale_one_le (by omega))
    positivity
  have hAd := div_le_div_of_nonneg_left hA he heu
  have hBd := div_le_div_of_nonneg_left hB (show 0 < 6*Real.sqrt (n+1 : ℕ) by positivity) hel
  have hEd := div_le_div_of_nonneg_right hE he.le
  change (A-B)/e ≤ E/e at hEd
  rw [sub_div] at hEd
  have hconst := factorialSourceJumpError_scaled_le n
  have hAeq : A/(46*Real.sqrt (n+1 : ℕ)) = (3/23 : ℝ)*Real.exp (-(1/2 : ℝ))*Real.log ((n+1 : ℕ) : ℝ) := by
    dsimp [A]
    field_simp [hr.ne']; ring
  rw [hAeq] at hAd
  unfold factorialSourceNormalizedJumpLower
  dsimp only [B] at hBd hEd
  linarith

theorem factorialSource_normalized_jump_energy_lower (n : ℕ) :
    factorialSourceNormalizedJumpLower n ≤ biScaleLevyEnergy (factorialSourcePlus n)/autocorr (factorialSourcePlus n) 0 ∧
      factorialSourceNormalizedJumpLower n ≤ biScaleLevyEnergy (factorialSourceMinus n)/autocorr (factorialSourceMinus n) 0 := by
  obtain ⟨he,hl,hu⟩ := factorialSource_energy_certificate n
  obtain ⟨hp,hm⟩ := factorialSource_jump_energy_lower n
  constructor
  · exact factorialSource_normalized_lower n hp hl hu
  · rw [he] at hl hu
    exact factorialSource_normalized_lower n hm hl hu

/-- All domains, growth bounds and signed cancellation refer to the constructed sources. -/
theorem factorialSourceArchimedean_certificate (n : ℕ) :
    IntegrableOn (fun x => (autocorr (factorialSourcePlus n) 0-autocorr (factorialSourcePlus n) x)*archLevySinhWeight x) (Ioi 0) ∧
    IntegrableOn (fun x => (autocorr (factorialSourceMinus n) 0-autocorr (factorialSourceMinus n) x)*archLevySinhWeight x) (Ioi 0) ∧
    factorialSourceJumpLower n ≤ biScaleLevyEnergy (factorialSourcePlus n) ∧
    biScaleLevyEnergy (factorialSourcePlus n) ≤ factorialSourceJumpUpper n ∧
    factorialSourceJumpLower n ≤ biScaleLevyEnergy (factorialSourceMinus n) ∧
    biScaleLevyEnergy (factorialSourceMinus n) ≤ factorialSourceJumpUpper n ∧
    biScaleLevyEnergy (factorialSourcePlus n)-biScaleLevyEnergy (factorialSourceMinus n) =
      -2*(∫ x in Ioi 0, sourceFactorialCausal (n+1) x*archLevySinhWeight x) ∧
    |biScaleLevyEnergy (factorialSourcePlus n)-biScaleLevyEnergy (factorialSourceMinus n)| ≤ 2*factorialSourceJumpError n ∧
    factorialSourceNormalizedJumpLower n ≤ biScaleLevyEnergy (factorialSourcePlus n)/autocorr (factorialSourcePlus n) 0 ∧
    factorialSourceNormalizedJumpLower n ≤ biScaleLevyEnergy (factorialSourceMinus n)/autocorr (factorialSourceMinus n) 0 := by
  obtain ⟨hpl,hml⟩ := factorialSource_jump_energy_lower n
  obtain ⟨hpu,hmu⟩ := factorialSource_jump_energy_upper n
  exact ⟨factorialSourcePlus_jump_integrable n,factorialSourceMinus_jump_integrable n,
    hpl,hpu,hml,hmu,factorialSource_jump_energy_difference n,factorialSource_jump_energy_difference_bound n,
    (factorialSource_normalized_jump_energy_lower n).1,(factorialSource_normalized_jump_energy_lower n).2⟩

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
