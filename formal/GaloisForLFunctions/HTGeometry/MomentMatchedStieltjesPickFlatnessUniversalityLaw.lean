import GaloisForLFunctions.HTGeometry.CauchyMomentFlatness
import GaloisForLFunctions.HTGeometry.StieltjesTransformPick

/-!
# Moment-matched Stieltjes–Pick flatness universality law

Finite moment agreement and the Pick property are usually recorded in opposite Cauchy-kernel
conventions.  After converting `(z - x)⁻¹ = -((x - z)⁻¹)`, they become one law: two nonzero finite
positive measures with matching moments generate holomorphic strict Pick functions whose difference
has an exact high-order remainder and the same real symmetry.
-/

open MeasureTheory

namespace HTGeometry

/-- Moment matching gives the exact remainder formula directly in the Stieltjes/Pick convention. -/
theorem stieltjes_transform_sub_of_moments_eq
    {mu nu : Measure ℝ} (z : ℂ) (hz : z ≠ 0) (himz : z.im ≠ 0) (N : ℕ)
    (hIntMu : ∀ k ∈ Finset.range (N + 1), Integrable (fun x : ℝ => (x : ℂ) ^ k) mu)
    (hIntRMu : Integrable
      (fun x : ℝ => (x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹) mu)
    (hIntNu : ∀ k ∈ Finset.range (N + 1), Integrable (fun x : ℝ => (x : ℂ) ^ k) nu)
    (hIntRNu : Integrable
      (fun x : ℝ => (x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹) nu)
    (hmom : ∀ k ∈ Finset.range (N + 1),
      (∫ x, (x : ℂ) ^ k ∂mu) = ∫ x, (x : ℂ) ^ k ∂nu) :
    (∫ x, ((x : ℂ) - z)⁻¹ ∂mu) - ∫ x, ((x : ℂ) - z)⁻¹ ∂nu
      = ((∫ x, (x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹ ∂mu)
          - ∫ x, (x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹ ∂nu) / z ^ (N + 1) := by
  have hIntRMu' : Integrable
      (fun x : ℝ => (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹) mu := by
    refine hIntRMu.neg.congr (ae_of_all mu fun x => ?_)
    change -((x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹) =
      (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹
    rw [show z - (x : ℂ) = -((x : ℂ) - z) by ring, inv_neg]
    ring
  have hIntRNu' : Integrable
      (fun x : ℝ => (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹) nu := by
    refine hIntRNu.neg.congr (ae_of_all nu fun x => ?_)
    change -((x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹) =
      (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹
    rw [show z - (x : ℂ) = -((x : ℂ) - z) by ring, inv_neg]
    ring
  have hflat := cauchy_transform_sub_of_moments_eq z hz himz N
    hIntMu hIntRMu' hIntNu hIntRNu' hmom
  have hCmu : (∫ x, (z - (x : ℂ))⁻¹ ∂mu) =
      -(∫ x, ((x : ℂ) - z)⁻¹ ∂mu) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all mu fun x => ?_)
    change (z - (x : ℂ))⁻¹ = -((x : ℂ) - z)⁻¹
    rw [show z - (x : ℂ) = -((x : ℂ) - z) by ring, inv_neg]
  have hCnu : (∫ x, (z - (x : ℂ))⁻¹ ∂nu) =
      -(∫ x, ((x : ℂ) - z)⁻¹ ∂nu) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all nu fun x => ?_)
    change (z - (x : ℂ))⁻¹ = -((x : ℂ) - z)⁻¹
    rw [show z - (x : ℂ) = -((x : ℂ) - z) by ring, inv_neg]
  have hRmu : (∫ x, (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹ ∂mu) =
      -(∫ x, (x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹ ∂mu) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all mu fun x => ?_)
    change (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹ =
      -((x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹)
    rw [show z - (x : ℂ) = -((x : ℂ) - z) by ring, inv_neg]
    ring
  have hRnu : (∫ x, (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹ ∂nu) =
      -(∫ x, (x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹ ∂nu) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all nu fun x => ?_)
    change (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹ =
      -((x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹)
    rw [show z - (x : ℂ) = -((x : ℂ) - z) by ring, inv_neg]
    ring
  rw [hCmu, hCnu, hRmu, hRnu] at hflat
  linear_combination -hflat

/-- **Moment-matched Stieltjes–Pick flatness universality law.**  Equal finite moments force an
exact high-order defect between two holomorphic strict Pick functions, and that defect obeys the
real-symmetric Schwarz reflection law. -/
theorem momentMatched_stieltjesPick_flatness
    {mu nu : Measure ℝ} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (z : ℂ) (hz : 0 < z.im) (N : ℕ)
    (hmu : 0 < mu Set.univ) (hnu : 0 < nu Set.univ)
    (hStMu : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) mu)
    (hStNu : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) nu)
    (hIntMu : ∀ k ∈ Finset.range (N + 1), Integrable (fun x : ℝ => (x : ℂ) ^ k) mu)
    (hIntRMu : Integrable
      (fun x : ℝ => (x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹) mu)
    (hIntNu : ∀ k ∈ Finset.range (N + 1), Integrable (fun x : ℝ => (x : ℂ) ^ k) nu)
    (hIntRNu : Integrable
      (fun x : ℝ => (x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹) nu)
    (hmom : ∀ k ∈ Finset.range (N + 1),
      (∫ x, (x : ℂ) ^ k ∂mu) = ∫ x, (x : ℂ) ^ k ∂nu) :
    DifferentiableOn ℂ (fun w => ∫ x, ((x : ℂ) - w)⁻¹ ∂mu) {w : ℂ | 0 < w.im} ∧
      DifferentiableOn ℂ (fun w => ∫ x, ((x : ℂ) - w)⁻¹ ∂nu) {w : ℂ | 0 < w.im} ∧
      0 < (∫ x, ((x : ℂ) - z)⁻¹ ∂mu).im ∧
      0 < (∫ x, ((x : ℂ) - z)⁻¹ ∂nu).im ∧
      (∫ x, ((x : ℂ) - z)⁻¹ ∂mu) - ∫ x, ((x : ℂ) - z)⁻¹ ∂nu
        = ((∫ x, (x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹ ∂mu)
            - ∫ x, (x : ℂ) ^ (N + 1) * ((x : ℂ) - z)⁻¹ ∂nu) / z ^ (N + 1) ∧
      (∫ x, ((x : ℂ) - (starRingEnd ℂ) z)⁻¹ ∂mu)
          - ∫ x, ((x : ℂ) - (starRingEnd ℂ) z)⁻¹ ∂nu
        = (starRingEnd ℂ)
            ((∫ x, ((x : ℂ) - z)⁻¹ ∂mu) - ∫ x, ((x : ℂ) - z)⁻¹ ∂nu) := by
  refine ⟨stieltjesTransform_differentiableOn,
    stieltjesTransform_differentiableOn,
    stieltjesTransform_im_pos z hz hmu hStMu,
    stieltjesTransform_im_pos z hz hnu hStNu,
    stieltjes_transform_sub_of_moments_eq z (by intro h; simpa [h] using hz.ne')
      hz.ne' N hIntMu hIntRMu hIntNu hIntRNu hmom,
    ?_⟩
  rw [stieltjesTransform_conj, stieltjesTransform_conj, map_sub]

end HTGeometry
