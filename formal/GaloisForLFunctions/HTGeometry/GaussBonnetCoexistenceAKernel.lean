import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Positive integral controlling logarithmic-entropy coexistence

For the two-radius model-A coexistence problem from arXiv:2609.00025,
write z for the small/large radius ratio and δ=(1-z)/(1+z).
The integral H=3∫₀¹(1+u²)/(1-δ²u²)du-1 will encode the logarithm in
the equal-Gibbs equation. Its bounds 3≤H≤(z²+z+1)/z are proved from
pointwise inequalities on the actual integral. All physical parameters
are constructed from unrestricted real data.
-/
noncomputable section
open Real Set
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbCoexistenceASymmetricRatio (τ : ℝ) : ℝ := (1 - thermalRatio τ) / (1 + thermalRatio τ)
def egbCoexistenceAKernelIntegrand (τ u : ℝ) : ℝ :=
  (1 + u ^ 2) / (1 - egbCoexistenceASymmetricRatio τ ^ 2 * u ^ 2)
def egbCoexistenceALogKernel (τ : ℝ) : ℝ :=
  3 * (∫ u in (0 : ℝ)..1, egbCoexistenceAKernelIntegrand τ u) - 1

theorem egbCoexistenceASymmetricRatio_bounds (τ : ℝ) :
    0 < egbCoexistenceASymmetricRatio τ ∧ egbCoexistenceASymmetricRatio τ < 1 := by
  have hz := thermalRatio_pos τ
  have hzu := thermalRatio_lt_one τ
  unfold egbCoexistenceASymmetricRatio
  constructor
  · exact div_pos (by linarith) (by positivity)
  · rw [div_lt_one (by positivity : 0 < 1 + thermalRatio τ)]
    linarith

theorem egbCoexistenceASymmetricRatio_complement (τ : ℝ) :
    1 - egbCoexistenceASymmetricRatio τ ^ 2 = 4 * thermalRatio τ / (1 + thermalRatio τ) ^ 2 := by
  have hz := thermalRatio_pos τ
  unfold egbCoexistenceASymmetricRatio
  field_simp
  ring

private theorem egbCoexistenceAKernel_den_bounds (τ : ℝ) :
    ∀ u ∈ Icc (0 : ℝ) 1,
      0 < 1 - egbCoexistenceASymmetricRatio τ ^ 2 * u ^ 2 ∧
      1 - egbCoexistenceASymmetricRatio τ ^ 2 ≤ 1 - egbCoexistenceASymmetricRatio τ ^ 2 * u ^ 2 ∧
      1 - egbCoexistenceASymmetricRatio τ ^ 2 * u ^ 2 ≤ 1 := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  intro u hu
  have hu₂ : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
  have hmul : egbCoexistenceASymmetricRatio τ ^ 2 * u ^ 2 ≤ egbCoexistenceASymmetricRatio τ ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (egbCoexistenceASymmetricRatio τ)) (sub_nonneg.mpr hu₂)]
  have hd₂ : egbCoexistenceASymmetricRatio τ ^ 2 < 1 := by nlinarith [hd.1, hd.2]
  refine ⟨by linarith, by linarith, ?_⟩
  have hm : 0 ≤ egbCoexistenceASymmetricRatio τ ^ 2 * u ^ 2 := by positivity
  linarith

theorem egbCoexistenceAKernelIntegrand_continuousOn (τ : ℝ) :
    ContinuousOn (egbCoexistenceAKernelIntegrand τ) (Icc 0 1) := by
  unfold egbCoexistenceAKernelIntegrand
  have hn : Continuous (fun u : ℝ => 1 + u ^ 2) := continuous_const.add (continuous_id.pow 2)
  have hd : Continuous (fun u : ℝ => 1 - egbCoexistenceASymmetricRatio τ ^ 2 * u ^ 2) :=
    continuous_const.sub (continuous_const.mul (continuous_id.pow 2))
  exact hn.continuousOn.div hd.continuousOn fun u hu => ne_of_gt (egbCoexistenceAKernel_den_bounds τ u hu).1

theorem egbCoexistenceAKernelIntegrand_intervalIntegrable (τ : ℝ) :
    IntervalIntegrable (egbCoexistenceAKernelIntegrand τ) MeasureTheory.volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (egbCoexistenceAKernelIntegrand_continuousOn τ)

private theorem egbCoexistenceAKernel_polynomial_integral :
    (∫ u in (0 : ℝ)..1, (1 + u ^ 2)) = 4 / 3 := by
  have h₁ : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 := continuous_const.intervalIntegrable 0 1
  have h₂ : IntervalIntegrable (fun u : ℝ => u ^ 2) MeasureTheory.volume 0 1 := (continuous_id.pow 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add h₁ h₂]
  norm_num [integral_pow]

theorem egbCoexistenceALogKernel_lower_bound (τ : ℝ) : 3 ≤ egbCoexistenceALogKernel τ := by
  have hi : IntervalIntegrable (fun u : ℝ => 1 + u ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_const.add (continuous_id.pow 2)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi
    (egbCoexistenceAKernelIntegrand_intervalIntegrable τ) (fun u hu => by
      have hb := egbCoexistenceAKernel_den_bounds τ u hu
      unfold egbCoexistenceAKernelIntegrand
      apply (le_div_iff₀ hb.1).2
      nlinarith [mul_nonneg (show 0 ≤ 1 + u ^ 2 by positivity) (sub_nonneg.mpr hb.2.2)])
  rw [egbCoexistenceAKernel_polynomial_integral] at h
  unfold egbCoexistenceALogKernel
  linarith

theorem egbCoexistenceALogKernel_upper_bound (τ : ℝ) :
    egbCoexistenceALogKernel τ ≤ (thermalRatio τ ^ 2 + thermalRatio τ + 1) / thermalRatio τ := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hd₀ : 0 < 1 - egbCoexistenceASymmetricRatio τ ^ 2 := by nlinarith [hd.1, hd.2]
  have hi : IntervalIntegrable (fun u : ℝ => (1 + u ^ 2) / (1 - egbCoexistenceASymmetricRatio τ ^ 2))
      MeasureTheory.volume 0 1 :=
    ((continuous_const.add (continuous_id.pow 2)).div_const _).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (egbCoexistenceAKernelIntegrand_intervalIntegrable τ) hi (fun u hu => by
      have hb := egbCoexistenceAKernel_den_bounds τ u hu
      unfold egbCoexistenceAKernelIntegrand
      apply (div_le_div_iff₀ hb.1 hd₀).2
      nlinarith [mul_nonneg (show 0 ≤ 1 + u ^ 2 by positivity) (sub_nonneg.mpr hb.2.1)])
  rw [intervalIntegral.integral_div, egbCoexistenceAKernel_polynomial_integral] at h
  calc
    egbCoexistenceALogKernel τ = 3 * (∫ u in (0 : ℝ)..1, egbCoexistenceAKernelIntegrand τ u) - 1 := rfl
    _ ≤ 3 * ((4 / 3) / (1 - egbCoexistenceASymmetricRatio τ ^ 2)) - 1 := by linarith
    _ = (thermalRatio τ ^ 2 + thermalRatio τ + 1) / thermalRatio τ := by
      rw [egbCoexistenceASymmetricRatio_complement]
      have hz := thermalRatio_pos τ
      field_simp
      ring

theorem egbCoexistenceALogKernel_pos (τ : ℝ) : 0 < egbCoexistenceALogKernel τ := by
  linarith [egbCoexistenceALogKernel_lower_bound τ]

end GaloisForLFunctions.HTGeometry
