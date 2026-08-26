import GaloisForLFunctions.HTGeometry.DiskSmirnovHardyTwo
import GaloisForLFunctions.HTGeometry.DiskMultiplierSquareRoot

/-!
# Integrable Smirnov boundaries factor through two Hardy boundaries

Canonical inner--outer factorization of the numerator, followed by bounded analytic square roots
of both outer factors, splits a nonzero integrable Smirnov boundary into two square-integrable
Smirnov boundaries.  The `L²` Smirnov theorem then realizes both factors as exact Hardy boundaries.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every nonzero integrable Smirnov circle boundary is almost everywhere a product of two
`H²` boundary functions. -/
theorem DiskSmirnovBoundary.exists_hardyDisk_product_of_integrable_circleBoundary
    (F : DiskSmirnovBoundary)
    (hF : ∃ z ∈ ball (0 : ℂ) 1, F.numerator.fn z ≠ 0)
    (hint : Integrable F.circleBoundary circleLebesgue) :
    ∃ f g : HardyDisk,
      (fun z => (hardyDiskBoundary f : Circle → ℂ) z *
        (hardyDiskBoundary g : Circle → ℂ) z) =ᵐ[circleLebesgue]
          F.circleBoundary := by
  let I := diskMultiplierInnerFactor F.numerator hF
  let O := diskMultiplierOuterFactor F.numerator hF
  have hOouter : IsOuterDiskMultiplier O :=
    isOuterDiskMultiplier_diskMultiplierOuterFactor F.numerator hF
  obtain ⟨R, hRsq⟩ := O.exists_squareRoot_of_zeroFree (fun z hz =>
    hOouter.ne_zero_on_disk (by
      simpa [Metric.mem_ball, dist_zero_right] using hz))
  obtain ⟨S, hSsq⟩ := F.denominator.exists_squareRoot_of_zeroFree (fun z hz =>
    F.denominator_outer.ne_zero_on_disk (by
      simpa [Metric.mem_ball, dist_zero_right] using hz))
  have hSouter : IsOuterDiskMultiplier S :=
    F.denominator_outer.of_square_eq hSsq
  let A : DiskSmirnovBoundary :=
    { numerator := I.mul R
      denominator := S
      denominator_outer := hSouter }
  let B : DiskSmirnovBoundary :=
    { numerator := R
      denominator := S
      denominator_outer := hSouter }
  have hfac := diskMultiplierBoundaryFun_innerFactor_mul_outerFactor_ae
    F.numerator hF
  have hI := ae_norm_diskMultiplierInnerFactor_boundary_eq_one F.numerator hF
  have hRbd := diskMultiplierBoundaryFun_sq_ae_of_square_eq hRsq
  have hSbd := diskMultiplierBoundaryFun_sq_ae_of_square_eq hSsq
  have hIR := diskMultiplierBoundaryFun_mul_ae I R
  have hAnorm : (fun z => ‖A.circleBoundary z‖ ^ 2) =ᵐ[circleLebesgue]
      fun z => ‖F.circleBoundary z‖ := by
    filter_upwards [hfac, hI, hRbd, hSbd, hIR] with z hfacz hIz hRz hSz hIRz
    have hRnorm : ‖diskMultiplierBoundaryFun R z‖ ^ 2 =
        ‖diskMultiplierBoundaryFun O z‖ := by
      rw [← norm_pow, hRz]
    have hSnorm : ‖diskMultiplierBoundaryFun S z‖ ^ 2 =
        ‖diskMultiplierBoundaryFun F.denominator z‖ := by
      rw [← norm_pow, hSz]
    have hNnorm : ‖diskMultiplierBoundaryFun F.numerator z‖ =
        ‖diskMultiplierBoundaryFun O z‖ := by
      rw [← hfacz, norm_mul, hIz, one_mul]
    change ‖diskMultiplierBoundaryFun (I.mul R) z /
        diskMultiplierBoundaryFun S z‖ ^ 2 =
      ‖diskMultiplierBoundaryFun F.numerator z /
        diskMultiplierBoundaryFun F.denominator z‖
    rw [hIRz, norm_div, norm_mul, norm_div, div_pow, mul_pow,
      hIz, one_pow, one_mul, hRnorm, hSnorm, hNnorm]
  have hBnorm : (fun z => ‖B.circleBoundary z‖ ^ 2) =ᵐ[circleLebesgue]
      fun z => ‖F.circleBoundary z‖ := by
    filter_upwards [hfac, hI, hRbd, hSbd] with z hfacz hIz hRz hSz
    have hRnorm : ‖diskMultiplierBoundaryFun R z‖ ^ 2 =
        ‖diskMultiplierBoundaryFun O z‖ := by
      rw [← norm_pow, hRz]
    have hSnorm : ‖diskMultiplierBoundaryFun S z‖ ^ 2 =
        ‖diskMultiplierBoundaryFun F.denominator z‖ := by
      rw [← norm_pow, hSz]
    have hNnorm : ‖diskMultiplierBoundaryFun F.numerator z‖ =
        ‖diskMultiplierBoundaryFun O z‖ := by
      rw [← hfacz, norm_mul, hIz, one_mul]
    change ‖diskMultiplierBoundaryFun R z /
        diskMultiplierBoundaryFun S z‖ ^ 2 =
      ‖diskMultiplierBoundaryFun F.numerator z /
        diskMultiplierBoundaryFun F.denominator z‖
    rw [norm_div, norm_div, div_pow, hRnorm, hSnorm, hNnorm]
  have hAint : Integrable (fun z => ‖A.circleBoundary z‖ ^ 2)
      circleLebesgue := hint.norm.congr hAnorm.symm
  have hBint : Integrable (fun z => ‖B.circleBoundary z‖ ^ 2)
      circleLebesgue := hint.norm.congr hBnorm.symm
  have hAmem : MemLp A.circleBoundary 2 circleLebesgue := by
    apply (memLp_norm_iff A.aestronglyMeasurable_circleBoundary).mp
    exact (memLp_two_iff_integrable_sq
      A.aestronglyMeasurable_circleBoundary.norm).2 hAint
  have hBmem : MemLp B.circleBoundary 2 circleLebesgue := by
    apply (memLp_norm_iff B.aestronglyMeasurable_circleBoundary).mp
    exact (memLp_two_iff_integrable_sq
      B.aestronglyMeasurable_circleBoundary.norm).2 hBint
  obtain ⟨f, hf⟩ := A.exists_hardyDisk_of_memLp_two_circleBoundary hAmem
  obtain ⟨g, hg⟩ := B.exists_hardyDisk_of_memLp_two_circleBoundary hBmem
  refine ⟨f, g, ?_⟩
  filter_upwards [hf, hg, hfac, hRbd, hSbd, hIR] with
      z hfz hgz hfacz hRz hSz hIRz
  rw [hfz, hgz]
  change (diskMultiplierBoundaryFun (I.mul R) z /
      diskMultiplierBoundaryFun S z) *
    (diskMultiplierBoundaryFun R z /
      diskMultiplierBoundaryFun S z) =
    diskMultiplierBoundaryFun F.numerator z /
      diskMultiplierBoundaryFun F.denominator z
  rw [hIRz, div_mul_div_comm]
  congr 1
  · rw [mul_assoc, ← pow_two, hRz, hfacz]
  · rw [← pow_two, hSz]

end

end GaloisForLFunctions.HTGeometry
