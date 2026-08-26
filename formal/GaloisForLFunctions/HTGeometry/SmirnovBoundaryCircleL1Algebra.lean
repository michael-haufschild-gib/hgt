import GaloisForLFunctions.HTGeometry.SmirnovBoundaryInnerOuterFactor
import GaloisForLFunctions.HTGeometry.DiskMultiplierAlgebra

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

end

end GaloisForLFunctions.HTGeometry
