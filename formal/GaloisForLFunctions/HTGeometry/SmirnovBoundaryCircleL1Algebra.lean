import GaloisForLFunctions.HTGeometry.SmirnovBoundaryInnerOuterFactor
import GaloisForLFunctions.HTGeometry.DiskMultiplierAlgebra
import GaloisForLFunctions.HTGeometry.DiskMultiplierInnerOuterFactor

open Complex MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem DiskSmirnovBoundary.circleBoundary_mul_ae
    (F G : DiskSmirnovBoundary) :
    (F.mul G).circleBoundary =ᵐ[circleLebesgue]
      fun z => F.circleBoundary z * G.circleBoundary z := by
  filter_upwards [diskMultiplierBoundaryFun_mul_ae F.numerator G.numerator,
    diskMultiplierBoundaryFun_mul_ae F.denominator G.denominator,
    F.denominator_circle_ne_zero_ae, G.denominator_circle_ne_zero_ae]
      with z hnum hden hF hG
  rw [DiskSmirnovBoundary.circleBoundary, DiskSmirnovBoundary.circleBoundary,
    DiskSmirnovBoundary.circleBoundary]
  change diskMultiplierBoundaryFun (F.numerator.mul G.numerator) z /
      diskMultiplierBoundaryFun (F.denominator.mul G.denominator) z = _
  rw [hnum, hden]
  field_simp

theorem DiskSmirnovBoundary.circleBoundary_ofMultiplier_ae
    (A : DiskMultiplier) :
    (DiskSmirnovBoundary.ofMultiplier A).circleBoundary =ᵐ[circleLebesgue]
      diskMultiplierBoundaryFun A := by
  have honeHardy : hardyOf DiskMultiplier.one =
      hardyOf (DiskMultiplier.const 1) :=
    hardyOf_congr (fun _ _ => rfl)
  have hone : diskMultiplierBoundaryFun DiskMultiplier.one =ᵐ[circleLebesgue]
      fun _ => 1 := by
    rw [diskMultiplierBoundaryFun, honeHardy]
    exact diskMultiplierBoundaryFun_const_ae 1
  filter_upwards [hone] with z hz
  rw [DiskSmirnovBoundary.circleBoundary, DiskSmirnovBoundary.ofMultiplier, hz, div_one]

theorem DiskSmirnovBoundary.integrable_circleBoundary_mul_ofMultiplier
    (F : DiskSmirnovBoundary) (A : DiskMultiplier)
    (hF : Integrable F.circleBoundary circleLebesgue) :
    Integrable (F.mul (DiskSmirnovBoundary.ofMultiplier A)).circleBoundary
      circleLebesgue := by
  have hAmeas : AEStronglyMeasurable (diskMultiplierBoundaryFun A) circleLebesgue :=
    Lp.aestronglyMeasurable (hardyDiskBoundary (hardyOf A))
  have hprod : Integrable (fun z => F.circleBoundary z *
      diskMultiplierBoundaryFun A z) circleLebesgue :=
    hF.mul_bdd hAmeas (ae_norm_diskMultiplierBoundaryFun_le A)
  apply hprod.congr
  filter_upwards [F.circleBoundary_mul_ae (DiskSmirnovBoundary.ofMultiplier A),
    DiskSmirnovBoundary.circleBoundary_ofMultiplier_ae A] with z hmul hA
  rw [hmul, hA]

theorem DiskSmirnovBoundary.integrable_circleBoundary_ofMultiplier_mul
    (F : DiskSmirnovBoundary) (A : DiskMultiplier)
    (hF : Integrable F.circleBoundary circleLebesgue) :
    Integrable ((DiskSmirnovBoundary.ofMultiplier A).mul F).circleBoundary
      circleLebesgue := by
  have hAmeas : AEStronglyMeasurable (diskMultiplierBoundaryFun A) circleLebesgue :=
    Lp.aestronglyMeasurable (hardyDiskBoundary (hardyOf A))
  have hprod : Integrable (fun z => diskMultiplierBoundaryFun A z *
      F.circleBoundary z) circleLebesgue :=
    hF.bdd_mul hAmeas (ae_norm_diskMultiplierBoundaryFun_le A)
  apply hprod.congr
  filter_upwards [(DiskSmirnovBoundary.ofMultiplier A).circleBoundary_mul_ae F,
    DiskSmirnovBoundary.circleBoundary_ofMultiplier_ae A] with z hmul hA
  rw [hmul, hA]

/-- Removing a canonical unit inner factor preserves circle-boundary integrability. -/
theorem DiskSmirnovBoundary.integrable_outerPart_circleBoundary
    (F : DiskSmirnovBoundary)
    (hF : ∃ z ∈ Metric.ball (0 : ℂ) 1, F.numerator.fn z ≠ 0)
    (hint : Integrable F.circleBoundary circleLebesgue) :
    Integrable (F.outerPart hF).circleBoundary circleLebesgue := by
  let I := F.innerFactor hF
  let H := F.outerPart hF
  have hImeas : AEStronglyMeasurable
      (fun z => (starRingEnd ℂ) (diskMultiplierBoundaryFun I z))
      circleLebesgue :=
    Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (hardyDiskBoundary (hardyOf I)))
  have hmul : Integrable
      (fun z => (starRingEnd ℂ) (diskMultiplierBoundaryFun I z) *
        F.circleBoundary z) circleLebesgue :=
    hint.bdd_mul hImeas (by
      filter_upwards [ae_norm_diskMultiplierInnerFactor_boundary_eq_one
        F.numerator hF] with z hz
      simpa [I, DiskSmirnovBoundary.innerFactor] using hz.le)
  apply hmul.congr
  filter_upwards [diskMultiplierBoundaryFun_innerFactor_mul_outerFactor_ae
      F.numerator hF, F.denominator_circle_ne_zero_ae,
    ae_norm_diskMultiplierInnerFactor_boundary_eq_one F.numerator hF]
      with z hfactor hden hunit
  have hIunit : ‖diskMultiplierBoundaryFun I z‖ = 1 := by
    simpa [I, DiskSmirnovBoundary.innerFactor] using hunit
  have hprod : (starRingEnd ℂ) (diskMultiplierBoundaryFun I z) *
      diskMultiplierBoundaryFun I z = 1 := by
    rw [Complex.conj_mul', hIunit]
    norm_num
  rw [DiskSmirnovBoundary.circleBoundary, DiskSmirnovBoundary.circleBoundary]
  change (starRingEnd ℂ) (diskMultiplierBoundaryFun I z) *
      (diskMultiplierBoundaryFun F.numerator z /
        diskMultiplierBoundaryFun F.denominator z) =
      diskMultiplierBoundaryFun (diskMultiplierOuterFactor F.numerator hF) z /
        diskMultiplierBoundaryFun F.denominator z
  rw [← hfactor]
  field_simp [hden]
  change ((starRingEnd ℂ) (diskMultiplierBoundaryFun I z) *
      diskMultiplierBoundaryFun I z) *
        diskMultiplierBoundaryFun (diskMultiplierOuterFactor F.numerator hF) z = _
  rw [hprod, one_mul]

end

end GaloisForLFunctions.HTGeometry
