import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarRampRegularity
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceEnergy
import GaloisForLFunctions.BiScaleUncertainty.CompactLipschitzLevyEnergy

/-! Literal jump-domain admission and quadratic identities for the balanced sources. -/

open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem factorialSourceLeft_abs_sub_le (n : ℕ) (u v : ℝ) :
    |factorialSourceLeft n u-factorialSourceLeft n v| ≤ 10000*((n+1 : ℕ) : ℝ)^4*|u-v| := by
  have h := sourceFactorialRamp_abs_sub_le (by omega : 1 ≤ n+1) (-u) (-v)
  rw [show -u-(-v) = -(u-v) by ring, abs_neg] at h
  exact h

theorem factorialSourceRight_abs_sub_le (n : ℕ) (u v : ℝ) :
    |factorialSourceRight n u-factorialSourceRight n v| ≤ 2000*((n+1 : ℕ) : ℝ)^2*|u-v| :=
  exponentialTentSource_factorial_abs_sub_le (by omega) u v

private theorem source_combination_abs_sub_le (f g : C_c(ℝ, ℝ)) {K L : ℝ}
    (hf : ∀ u v, |f u-f v| ≤ K*|u-v|) (hg : ∀ u v, |g u-g v| ≤ L*|u-v|)
    (c d u v : ℝ) :
    |(c • f+d • g) u-(c • f+d • g) v| ≤ (|c| * K+|d| * L)*|u-v| := by
  change |(c*f u+d*g u)-(c*f v+d*g v)| ≤ _
  calc
    _ = |c*(f u-f v)+d*(g u-g v)| := by congr 1; ring
    _ ≤ |c*(f u-f v)|+|d*(g u-g v)| := abs_add_le _ _
    _ = |c| * |f u-f v|+|d| * |g u-g v| := by rw [abs_mul, abs_mul]
    _ ≤ |c| * (K*|u-v|)+|d| * (L*|u-v|) :=
      add_le_add (mul_le_mul_of_nonneg_left (hf u v) (abs_nonneg c))
        (mul_le_mul_of_nonneg_left (hg u v) (abs_nonneg d))
    _ = _ := by ring

theorem factorialSource_combination_jump_integrable (n : ℕ) (c d : ℝ) :
    IntegrableOn (fun x =>
      (autocorr (c • factorialSourceLeft n+d • factorialSourceRight n) 0-
        autocorr (c • factorialSourceLeft n+d • factorialSourceRight n) x)*archLevySinhWeight x) (Ioi 0) :=
  integrableOn_levy_of_lipschitz _
    (source_combination_abs_sub_le _ _ (factorialSourceLeft_abs_sub_le n)
      (factorialSourceRight_abs_sub_le n) c d)

theorem factorialSourceLeft_jump_integrable (n : ℕ) :
    IntegrableOn (fun x => (autocorr (factorialSourceLeft n) 0-
      autocorr (factorialSourceLeft n) x)*archLevySinhWeight x) (Ioi 0) :=
  integrableOn_levy_of_lipschitz _ (factorialSourceLeft_abs_sub_le n)

theorem factorialSourceRight_jump_integrable (n : ℕ) :
    IntegrableOn (fun x => (autocorr (factorialSourceRight n) 0-
      autocorr (factorialSourceRight n) x)*archLevySinhWeight x) (Ioi 0) :=
  integrableOn_levy_of_lipschitz _ (factorialSourceRight_abs_sub_le n)

theorem factorialSourcePlus_jump_integrable (n : ℕ) :
    IntegrableOn (fun x => (autocorr (factorialSourcePlus n) 0-
      autocorr (factorialSourcePlus n) x)*archLevySinhWeight x) (Ioi 0) :=
  factorialSource_combination_jump_integrable n _ _

theorem factorialSourceMinus_jump_integrable (n : ℕ) :
    IntegrableOn (fun x => (autocorr (factorialSourceMinus n) 0-
      autocorr (factorialSourceMinus n) x)*archLevySinhWeight x) (Ioi 0) := by
  have hi := factorialSource_combination_jump_integrable n (factorialSourceScale n) (-(factorialSourceScale n)⁻¹)
  have he : (fun u => factorialSourceScale n*factorialSourceLeft n u+
      (-(factorialSourceScale n)⁻¹)*factorialSourceRight n u) = (factorialSourceMinus n : ℝ → ℝ) := by
    funext u
    change factorialSourceScale n*factorialSourceLeft n u+
      (-(factorialSourceScale n)⁻¹)*factorialSourceRight n u =
        factorialSourceScale n*factorialSourceLeft n u-(factorialSourceScale n)⁻¹*factorialSourceRight n u
    ring
  change IntegrableOn (fun x =>
    (autocorr (fun u => factorialSourceScale n*factorialSourceLeft n u+
      (-(factorialSourceScale n)⁻¹)*factorialSourceRight n u) 0-
    autocorr (fun u => factorialSourceScale n*factorialSourceLeft n u+
      (-(factorialSourceScale n)⁻¹)*factorialSourceRight n u) x)*archLevySinhWeight x) (Ioi 0) at hi
  rw [he] at hi
  exact hi

theorem factorialSource_jump_energy_sum (n : ℕ) :
    biScaleLevyEnergy (factorialSourcePlus n)+biScaleLevyEnergy (factorialSourceMinus n) =
      2*(Real.sqrt (n+1 : ℕ)*biScaleLevyEnergy (factorialSourceLeft n)+
        biScaleLevyEnergy (factorialSourceRight n)/Real.sqrt (n+1 : ℕ)) := by
  have hiL : IntegrableOn (fun x =>
      (autocorr (factorialSourceScale n • factorialSourceLeft n) 0-
        autocorr (factorialSourceScale n • factorialSourceLeft n) x)*archLevySinhWeight x) (Ioi 0) := by
    simpa only [zero_smul, add_zero] using factorialSource_combination_jump_integrable n (factorialSourceScale n) 0
  have hiR : IntegrableOn (fun x =>
      (autocorr ((factorialSourceScale n)⁻¹ • factorialSourceRight n) 0-
        autocorr ((factorialSourceScale n)⁻¹ • factorialSourceRight n) x)*archLevySinhWeight x) (Ioi 0) := by
    simpa only [zero_smul, zero_add] using factorialSource_combination_jump_integrable n 0 (factorialSourceScale n)⁻¹
  have hp := levyEnergy_parallelogram_admitted
    (factorialSourceScale n • factorialSourceLeft n) ((factorialSourceScale n)⁻¹ • factorialSourceRight n)
    hiL hiR (factorialSourcePlus_jump_integrable n) (factorialSourceMinus_jump_integrable n)
  change biScaleLevyEnergy (factorialSourcePlus n)+biScaleLevyEnergy (factorialSourceMinus n) = _ at hp
  rw [hp]
  change 2*(biScaleLevyEnergy (fun u => factorialSourceScale n*factorialSourceLeft n u)+
    biScaleLevyEnergy (fun u => (factorialSourceScale n)⁻¹*factorialSourceRight n u)) = _
  simp only [biScaleLevyEnergy_source_const_mul, inv_pow, factorialSourceScale_sq]
  ring

theorem factorialSource_signed_jump_integrand (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (autocorr (factorialSourcePlus n) 0-autocorr (factorialSourcePlus n) x)*archLevySinhWeight x-
      (autocorr (factorialSourceMinus n) 0-autocorr (factorialSourceMinus n) x)*archLevySinhWeight x =
        -2*(sourceFactorialCausal (n+1) x*archLevySinhWeight x) := by
  have hz := (factorialSource_energy_certificate n).1
  have hc := factorialSourceContrast_eq_of_nonneg n hx
  unfold factorialSourceContrast at hc
  rw [hz]
  linear_combination -2*(archLevySinhWeight x)*hc

theorem integrableOn_sourceFactorialCausal_archWeight (n : ℕ) :
    IntegrableOn (fun x => sourceFactorialCausal (n+1) x*archLevySinhWeight x) (Ioi 0) := by
  refine (((factorialSourcePlus_jump_integrable n).sub (factorialSourceMinus_jump_integrable n)).div_const (-2)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  dsimp only [Pi.sub_apply]
  rw [factorialSource_signed_jump_integrand n hx.le]
  ring

theorem factorialSource_jump_energy_difference (n : ℕ) :
    biScaleLevyEnergy (factorialSourcePlus n)-biScaleLevyEnergy (factorialSourceMinus n) =
      -2*∫ x in Ioi 0, sourceFactorialCausal (n+1) x*archLevySinhWeight x := by
  unfold biScaleLevyEnergy
  rw [← integral_sub (factorialSourcePlus_jump_integrable n) (factorialSourceMinus_jump_integrable n),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact factorialSource_signed_jump_integrand n hx.le

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
