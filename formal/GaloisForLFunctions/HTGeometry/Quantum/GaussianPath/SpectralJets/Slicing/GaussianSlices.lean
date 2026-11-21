import GaloisForLFunctions.HTGeometry.GaussianDeterminantTubeUpperBound
import Mathlib.MeasureTheory.Integral.Pi

/-! # Conditioning a Gaussian strip on all but one coordinate -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- A uniform Lebesgue bound on the sections of a measurable set bounds its
probability under independent standard Gaussian coordinates. -/
theorem gaussian_coordinate_slices {n : ℕ} (i : Fin (n+1)) (S : Set (Fin (n+1) → ℝ))
    (hS : MeasurableSet S) (B : ℝ≥0∞)
    (hs : ∀ y : Fin n → ℝ, volume {t : ℝ | i.insertNth (α := fun _ => ℝ) t y ∈ S} ≤ B) :
    (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) S ≤ B := by
  let E := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have hE := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hp : ENNReal.ofReal gaussianDensityPeak ≤ 1 := by
    rw [ENNReal.ofReal_le_one,gaussianDensityPeak]
    apply inv_le_one_of_one_le₀
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    linarith only [Real.pi_gt_three]
  rw [← hE.measure_preimage hS.nullMeasurableSet,Measure.prod_apply_symm (E.measurable hS)]
  calc
    _ ≤ ∫⁻ _y : Fin n → ℝ, B ∂(Measure.pi fun _ => gaussianReal 0 1) := by
      apply lintegral_mono
      intro y
      let A := {t : ℝ | i.insertNth (α := fun _ => ℝ) t y ∈ S}
      change gaussianReal 0 1 A ≤ B
      have hμ := Measure.le_iff'.mp gaussianReal_le_densityPeak_smul_volume A
      rw [Measure.smul_apply,smul_eq_mul] at hμ
      exact hμ.trans ((mul_le_mul_left hp (volume A)).trans ((one_mul _).le.trans (hs y)))
    _ = _ := by simp

/-- Condition on any coordinate, in the parameterization that overwrites
that coordinate in a full coupling vector. -/
theorem gaussian_update_slices {n : ℕ} (i : Fin n) (S : Set (Fin n → ℝ))
    (hS : MeasurableSet S) (B : ℝ≥0∞)
    (hs : ∀ y : Fin n → ℝ, volume {t : ℝ | Function.update y i t ∈ S} ≤ B) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) S ≤ B := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    apply gaussian_coordinate_slices i S hS B
    intro y
    let x := i.insertNth (α := fun _ => ℝ) 0 y
    have he (t : ℝ) : i.insertNth (α := fun _ => ℝ) t y = Function.update x i t := by
      funext j
      induction j using i.succAboveCases with
      | x => simp
      | p k => simp [Function.update_of_ne,x]
    simpa only [he] using hs x

#print axioms gaussian_coordinate_slices
#print axioms gaussian_update_slices
end
end GaloisForLFunctions.HTGeometry.SpectralJets
