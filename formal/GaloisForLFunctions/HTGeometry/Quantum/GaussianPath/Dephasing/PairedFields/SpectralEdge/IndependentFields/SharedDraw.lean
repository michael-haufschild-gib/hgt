import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Prod

/-! # Repeating a circuit test with a common random base -/

open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private theorem real_sections (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure ν]
    {A : Set (X × Y)} (hA : MeasurableSet A) :
    (μ.prod ν).real A = ∫ x, ν.real (Prod.mk x ⁻¹' A) ∂μ := by
  unfold Measure.real
  rw [Measure.prod_apply hA, integral_toReal (measurable_measure_prodMk_left hA).aemeasurable
    (ae_of_all _ fun _ => measure_lt_top _ _)]

/-- Repeating a measurable test on independent perturbations of the same base
has probability equal to the square of its success probability plus the
variance of its conditional success probability. -/
theorem shared_draw_success (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {A : Set (X × Y)} (hA : MeasurableSet A) :
    (μ.prod (ν.prod ν)).real {z | (z.1,z.2.1) ∈ A ∧ (z.1,z.2.2) ∈ A} =
      ((μ.prod ν).real A)^2 + variance (fun x => ν.real (Prod.mk x ⁻¹' A)) μ := by
  let q (x : X) := ν.real (Prod.mk x ⁻¹' A)
  have hq : MemLp q 2 μ := memLp_of_bounded
    (ae_of_all _ fun x => show q x ∈ Icc (0:ℝ) 1 from ⟨measureReal_nonneg,measureReal_le_one⟩)
    (measurable_measure_prodMk_left hA).ennreal_toReal.aestronglyMeasurable _
  let S : Set (X × Y × Y) := {z | (z.1,z.2.1) ∈ A ∧ (z.1,z.2.2) ∈ A}
  have hS : MeasurableSet S :=
    (hA.preimage (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).inter
    (hA.preimage (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hsec (x : X) : (ν.prod ν).real (Prod.mk x ⁻¹' S) = (q x)^2 := by
    change (ν.prod ν).real ((Prod.mk x ⁻¹' A) ×ˢ (Prod.mk x ⁻¹' A)) = _
    rw [Measure.real, Measure.prod_prod, ENNReal.toReal_mul, sq]
    rfl
  change (μ.prod (ν.prod ν)).real S = _
  rw [real_sections μ (ν.prod ν) hS, real_sections μ ν hA]
  simp_rw [hsec]
  change (∫ x, (q x)^2 ∂μ) = (∫ x, q x ∂μ)^2 + variance q μ
  rw [variance_eq_sub hq]
  change _ = _ + ((∫ x, (q x)^2 ∂μ) - _)
  abel

#print axioms shared_draw_success
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
