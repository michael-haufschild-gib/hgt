import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernelLimits

/-!
# Positive weighted moments and exact recurrence of the coexistence kernel

The logarithmic kernel from the actual model-A coexistence construction
is a Stieltjes-type integral in the squared radius asymmetry. Its weighted
moments have explicit polynomial lower bounds and geometric upper bounds.
An exact recurrence supplies remainders of every order without truncating
or numerically approximating the logarithm.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbCoexistenceAKernelMomentCoefficient (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 3)
def egbCoexistenceAKernelMomentIntegrand (τ : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  u ^ (2 * n) * egbCoexistenceAKernelIntegrand τ u
def egbCoexistenceAKernelMoment (τ : ℝ) (n : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1, egbCoexistenceAKernelMomentIntegrand τ n u

theorem egbCoexistenceAKernelMomentCoefficient_pos (n : ℕ) : 0 < egbCoexistenceAKernelMomentCoefficient n := by
  unfold egbCoexistenceAKernelMomentCoefficient
  positivity

theorem egbCoexistenceAKernelMoment_polynomial_integral (n : ℕ) :
    (∫ u in (0 : ℝ)..1, u ^ (2 * n) * (1 + u ^ (2 : ℕ))) = egbCoexistenceAKernelMomentCoefficient n := by
  have he : (fun u : ℝ => u ^ (2 * n) * (1 + u ^ (2 : ℕ))) = (fun u => u ^ (2 * n) + u ^ (2 * n + 2)) := by
    funext u
    rw [pow_add]
    ring
  have h₁ : IntervalIntegrable (fun u : ℝ => u ^ (2 * n)) MeasureTheory.volume 0 1 :=
    (continuous_id.pow (2 * n)).intervalIntegrable 0 1
  have h₂ : IntervalIntegrable (fun u : ℝ => u ^ (2 * n + 2)) MeasureTheory.volume 0 1 :=
    (continuous_id.pow (2 * n + 2)).intervalIntegrable 0 1
  rw [he, intervalIntegral.integral_add h₁ h₂]
  norm_num [integral_pow, egbCoexistenceAKernelMomentCoefficient, Nat.cast_add, Nat.cast_mul] <;> ring

theorem egbCoexistenceAKernelMomentIntegrand_continuousOn (τ : ℝ) (n : ℕ) :
    ContinuousOn (egbCoexistenceAKernelMomentIntegrand τ n) (Icc 0 1) :=
  (continuous_id.pow (2 * n)).continuousOn.mul (egbCoexistenceAKernelIntegrand_continuousOn τ)

theorem egbCoexistenceAKernelMomentIntegrand_intervalIntegrable (τ : ℝ) (n : ℕ) :
    IntervalIntegrable (egbCoexistenceAKernelMomentIntegrand τ n) MeasureTheory.volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (egbCoexistenceAKernelMomentIntegrand_continuousOn τ n)

private theorem weighted_integrand_bounds (τ : ℝ) (n : ℕ) :
    ∀ u ∈ Icc (0 : ℝ) 1,
      u ^ (2 * n) * (1 + u ^ (2 : ℕ)) ≤ egbCoexistenceAKernelMomentIntegrand τ n u ∧
      egbCoexistenceAKernelMomentIntegrand τ n u ≤
        (u ^ (2 * n) * (1 + u ^ (2 : ℕ))) / (1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) := by
  intro u hu
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hc : 0 < 1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by nlinarith [hd.1, hd.2]
  have hu₂ : u ^ (2 : ℕ) ≤ 1 := by nlinarith [hu.1, hu.2]
  have hm : egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * u ^ (2 : ℕ) ≤ egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sq_nonneg (egbCoexistenceASymmetricRatio τ)) (sub_nonneg.mpr hu₂)]
  have hden : 0 < 1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * u ^ (2 : ℕ) := by linarith
  have hp : 0 ≤ u ^ (2 * n) * (1 + u ^ (2 : ℕ)) := mul_nonneg (pow_nonneg hu.1 _) (by positivity)
  have he : egbCoexistenceAKernelMomentIntegrand τ n u =
      (u ^ (2 * n) * (1 + u ^ (2 : ℕ))) / (1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * u ^ (2 : ℕ)) := by
    unfold egbCoexistenceAKernelMomentIntegrand egbCoexistenceAKernelIntegrand
    ring
  rw [he]
  constructor
  · apply (le_div_iff₀ hden).2
    have hq : 0 ≤ egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * u ^ (2 : ℕ) := by positivity
    nlinarith [mul_nonneg hp hq]
  · apply (div_le_div_iff₀ hden hc).2
    nlinarith [mul_nonneg hp (show 0 ≤ egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * u ^ (2 : ℕ) by linarith)]

theorem egbCoexistenceAKernelMoment_bounds (τ : ℝ) (n : ℕ) :
    egbCoexistenceAKernelMomentCoefficient n ≤ egbCoexistenceAKernelMoment τ n ∧
      egbCoexistenceAKernelMoment τ n ≤ egbCoexistenceAKernelMomentCoefficient n /
        (1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) := by
  have hp : IntervalIntegrable (fun u : ℝ => u ^ (2 * n) * (1 + u ^ (2 : ℕ))) MeasureTheory.volume 0 1 :=
    ((continuous_id.pow (2 * n)).mul (continuous_const.add (continuous_id.pow 2))).intervalIntegrable 0 1
  have hd : IntervalIntegrable (fun u : ℝ => (u ^ (2 * n) * (1 + u ^ (2 : ℕ))) /
      (1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))) MeasureTheory.volume 0 1 :=
    (((continuous_id.pow (2 * n)).mul (continuous_const.add (continuous_id.pow 2))).div_const _).intervalIntegrable 0 1
  constructor
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hp
      (egbCoexistenceAKernelMomentIntegrand_intervalIntegrable τ n) (fun u hu => (weighted_integrand_bounds τ n u hu).1)
    rwa [egbCoexistenceAKernelMoment_polynomial_integral] at h
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (egbCoexistenceAKernelMomentIntegrand_intervalIntegrable τ n) hd (fun u hu => (weighted_integrand_bounds τ n u hu).2)
    rwa [intervalIntegral.integral_div, egbCoexistenceAKernelMoment_polynomial_integral] at h

theorem egbCoexistenceAKernelMoment_pos (τ : ℝ) (n : ℕ) : 0 < egbCoexistenceAKernelMoment τ n :=
  lt_of_lt_of_le (egbCoexistenceAKernelMomentCoefficient_pos n) (egbCoexistenceAKernelMoment_bounds τ n).1

theorem egbCoexistenceAKernelMoment_zero (τ : ℝ) :
    egbCoexistenceALogKernel τ = 3 * egbCoexistenceAKernelMoment τ 0 - 1 := by
  simp only [egbCoexistenceALogKernel, egbCoexistenceAKernelMoment, egbCoexistenceAKernelMomentIntegrand, mul_zero, pow_zero, one_mul]

/-- Exact resolvent recurrence; the next positive moment is the full remainder. -/
theorem egbCoexistenceAKernelMoment_recurrence (τ : ℝ) (n : ℕ) :
    egbCoexistenceAKernelMoment τ n - egbCoexistenceAKernelMomentCoefficient n =
      egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbCoexistenceAKernelMoment τ (n + 1) := by
  have hp : IntervalIntegrable (fun u : ℝ => u ^ (2 * n) * (1 + u ^ (2 : ℕ))) MeasureTheory.volume 0 1 :=
    ((continuous_id.pow (2 * n)).mul (continuous_const.add (continuous_id.pow 2))).intervalIntegrable 0 1
  rw [← egbCoexistenceAKernelMoment_polynomial_integral]
  unfold egbCoexistenceAKernelMoment
  rw [← intervalIntegral.integral_sub (egbCoexistenceAKernelMomentIntegrand_intervalIntegrable τ n) hp,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  have huI : u ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hu₂ : u ^ (2 : ℕ) ≤ 1 := by nlinarith [huI.1, huI.2]
  have hd₂ : egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) < 1 := by nlinarith [hd.1, hd.2]
  have hm : egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * u ^ (2 : ℕ) ≤ egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sq_nonneg (egbCoexistenceASymmetricRatio τ)) (sub_nonneg.mpr hu₂)]
  have hn : 1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * u ^ (2 : ℕ) ≠ 0 := by linarith
  unfold egbCoexistenceAKernelMomentIntegrand egbCoexistenceAKernelIntegrand
  dsimp only
  rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
  have hn' : 1 - u ^ (2 : ℕ) * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) ≠ 0 := by
    simpa only [mul_comm] using hn
  field_simp [hn, hn']
  ring

theorem egbCoexistenceAKernelMoment_strict_lower_bound (τ : ℝ) (n : ℕ) :
    egbCoexistenceAKernelMomentCoefficient n < egbCoexistenceAKernelMoment τ n := by
  have h := egbCoexistenceAKernelMoment_recurrence τ n
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hm := egbCoexistenceAKernelMoment_pos τ (n + 1)
  have hp : 0 < egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbCoexistenceAKernelMoment τ (n + 1) := by positivity
  linarith

theorem egbCoexistenceALogKernel_strict_lower_bound (τ : ℝ) : 3 < egbCoexistenceALogKernel τ := by
  have h := egbCoexistenceAKernelMoment_strict_lower_bound τ 0
  norm_num [egbCoexistenceAKernelMomentCoefficient] at h
  rw [egbCoexistenceAKernelMoment_zero]
  linarith

end GaloisForLFunctions.HTGeometry
