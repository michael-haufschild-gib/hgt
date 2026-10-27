import GaloisForLFunctions.HTGeometry.PlanarLogSquare
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanBandPerturbation

/-!
# Multiplicity-weighted planar logarithmic squares

Weighted Cauchy–Schwarz bounds the squared potential of a finite positive
mass distribution by its total mass times the sum of the squared kernels.
Integration gives a bound quadratic in total mass and kernel radius,
independent of the locations and separation of the poles.
-/

open MeasureTheory Metric Set
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Finite positive logarithmic potentials have globally integrable squares. -/
lemma integrable_sum_planarLogKernel_sq {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i)
    {S : ℝ} (hS : 0 < S) :
    Integrable (fun z : ℂ => (∑ i ∈ s, w i * planarLogKernel S (z - a i)) ^ 2) := by
  have ht (i : ι) : Integrable (fun z : ℂ => w i * planarLogKernel S (z - a i) ^ 2) :=
    (integrable_planarLogKernel_sq_sub hS (a i)).const_mul _
  have hmajor := (integrable_finsetSum s (fun i _ => ht i)).const_mul (∑ i ∈ s, w i)
  have hm : Measurable (fun z : ℂ => (∑ i ∈ s, w i * planarLogKernel S (z - a i)) ^ 2) := by
    unfold planarLogKernel
    fun_prop
  apply hmajor.mono hm.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine (sq_sum_weighted_le s w (fun i => planarLogKernel S (z - a i)) hw).trans ?_
  exact le_abs_self _

/-- Total mass controls the whole-plane squared potential without a separation condition. -/
lemma integral_sum_planarLogKernel_sq_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i)
    {S : ℝ} (hS : 0 < S) :
    (∫ z : ℂ, (∑ i ∈ s, w i * planarLogKernel S (z - a i)) ^ 2) ≤
      (∑ i ∈ s, w i) ^ 2 * (8 * Real.pi * S ^ 2) := by
  have ht (i : ι) : Integrable (fun z : ℂ => w i * planarLogKernel S (z - a i) ^ 2) :=
    (integrable_planarLogKernel_sq_sub hS (a i)).const_mul _
  have hmass : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  calc
    (∫ z : ℂ, (∑ i ∈ s, w i * planarLogKernel S (z - a i)) ^ 2) ≤
        ∫ z : ℂ, (∑ i ∈ s, w i) * ∑ i ∈ s, w i * planarLogKernel S (z - a i) ^ 2 :=
      integral_mono (integrable_sum_planarLogKernel_sq s w a hw hS)
        ((integrable_finsetSum s (fun i _ => ht i)).const_mul _)
        (fun z => sq_sum_weighted_le s w (fun i => planarLogKernel S (z - a i)) hw)
    _ = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (∫ z : ℂ, planarLogKernel S (z - a i) ^ 2) := by
      rw [integral_const_mul, integral_finsetSum s (fun i _ => ht i)]
      simp_rw [integral_const_mul]
    _ ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (8 * Real.pi * S ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hmass
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw i hi)
      have hmp : MeasurePreserving (fun z : ℂ => z + -(a i)) volume volume :=
        measurePreserving_add_right volume (-(a i))
      have hme : MeasurableEmbedding (fun z : ℂ => z + -(a i)) :=
        (MeasurableEquiv.addRight (-(a i))).measurableEmbedding
      have he := hmp.integral_comp hme (fun z : ℂ => planarLogKernel S z ^ 2)
      simp only [← sub_eq_add_neg] at he
      rw [he]
      exact integral_planarLogKernel_sq_le hS
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Restricting the potential to any disc preserves the uniform mass bound. -/
lemma integral_sum_planarLogKernel_sq_on_disc_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i)
    {S : ℝ} (hS : 0 < S) (c : ℂ) (R : ℝ) :
    (∫ z in closedBall c R, (∑ i ∈ s, w i * planarLogKernel S (z - a i)) ^ 2) ≤
      (∑ i ∈ s, w i) ^ 2 * (8 * Real.pi * S ^ 2) := by
  exact (integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall fun z => sq_nonneg _)
    (integrable_sum_planarLogKernel_sq s w a hw hS)).trans
      (integral_sum_planarLogKernel_sq_le s w a hw hS)

end GaloisForLFunctions.HTGeometry
