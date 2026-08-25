import GaloisForLFunctions.HTGeometry.SmirnovBoundaryQuotient
import GaloisForLFunctions.HTGeometry.CayleyGeneralizedSchurCongruence
import GaloisForLFunctions.HTGeometry.CayleySchur

/-!
# Interior analytic values of Smirnov boundary quotients

The boundary algebra stores a Smirnov function as bounded numerator divided by an outer
denominator.  Outer cyclicity makes that denominator zero-free in the disk, so the quotient has an
honest analytic value there and after transport to the upper half-plane.
-/

open Complex Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Interior value of a Smirnov quotient. -/
def DiskSmirnovBoundary.value (F : DiskSmirnovBoundary) (z : ℂ) : ℂ :=
  F.numerator.fn z / F.denominator.fn z

theorem DiskSmirnovBoundary.analyticOnNhd_value (F : DiskSmirnovBoundary) :
    AnalyticOnNhd ℂ F.value (Metric.ball 0 1) := by
  intro z hz
  have hznorm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  exact (F.numerator.diff.analyticOnNhd Metric.isOpen_ball z hz).div
    (F.denominator.diff.analyticOnNhd Metric.isOpen_ball z hz)
    (F.denominator_outer.ne_zero_on_disk hznorm)

/-- Upper-half-plane realization through the standard Cayley transform. -/
def DiskSmirnovBoundary.upperValue (F : DiskSmirnovBoundary) (z : ℂ) : ℂ :=
  F.value (upperToDiskCayley z)

theorem analyticAt_upperToDiskCayley {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ upperToDiskCayley z := by
  change AnalyticAt ℂ (fun w : ℂ => (w - I) / (w + I)) z
  apply (analyticAt_id.sub analyticAt_const).div
    (analyticAt_id.add analyticAt_const)
  intro h
  have him := congrArg Complex.im h
  norm_num at him
  linarith

theorem DiskSmirnovBoundary.analyticAt_upperValue
    (F : DiskSmirnovBoundary) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ F.upperValue z := by
  have hmap : ‖upperToDiskCayley z‖ < 1 := by
    exact GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz
  have hv := F.analyticOnNhd_value (upperToDiskCayley z) (by
    simpa [Metric.mem_ball, dist_zero_right] using hmap)
  change AnalyticAt ℂ (fun w => F.value (upperToDiskCayley w)) z
  simpa [Function.comp_def] using
    AnalyticAt.comp (g := F.value) (f := upperToDiskCayley) (x := z)
      hv (analyticAt_upperToDiskCayley hz)

theorem DiskSmirnovBoundary.upperValue_denominator_ne_zero
    (F : DiskSmirnovBoundary) {z : ℂ} (hz : 0 < z.im) :
    F.denominator.fn (upperToDiskCayley z) ≠ 0 :=
  F.denominator_outer.ne_zero_on_disk
    (GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz)

/-- Literal radial value of a Smirnov quotient on the circle. -/
def DiskSmirnovBoundary.radialBoundaryFun
    (n : ℕ) (F : DiskSmirnovBoundary) (z : Circle) : ℂ :=
  diskMultiplierRadialBoundaryFun n F.numerator z /
    diskMultiplierRadialBoundaryFun n F.denominator z

/-- Numerator and outer denominator admit one common cofinal radial subsequence on which their
quotient converges almost everywhere to the exact Smirnov boundary quotient. -/
theorem DiskSmirnovBoundary.exists_radialBoundary_subseq_ae
    (F : DiskSmirnovBoundary) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂circleLebesgue,
        Tendsto (fun i => F.radialBoundaryFun (ns i) z) atTop
          (𝓝 (diskMultiplierBoundaryFun F.numerator z /
            diskMultiplierBoundaryFun F.denominator z)) := by
  obtain ⟨nsNum, hnsNum, hnum⟩ :=
    exists_diskMultiplierRadialBoundary_subseq_ae F.numerator
  obtain ⟨nsDen, hnsDen, hden⟩ :=
    exists_diskMultiplierRadialBoundary_subseq_ae_of_strictMono
      F.denominator hnsNum
  let ns : ℕ → ℕ := fun i => nsNum (nsDen i)
  have hns : StrictMono ns := hnsNum.comp hnsDen
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hnum, hden,
    diskMultiplierBoundary_ne_zero_ae F.denominator
      F.denominator_outer.exists_nonzero]
      with z hnumz hdenz hdenNe
  have hnumz' : Tendsto
      (fun i => diskMultiplierRadialBoundaryFun (ns i) F.numerator z)
      atTop (𝓝 (diskMultiplierBoundaryFun F.numerator z)) :=
    hnumz.comp hnsDen.tendsto_atTop
  have hquot := hnumz'.div hdenz hdenNe
  change Tendsto (fun i =>
    diskMultiplierRadialBoundaryFun (ns i) F.numerator z /
      diskMultiplierRadialBoundaryFun (ns i) F.denominator z) atTop _
  exact hquot.congr' (Eventually.of_forall fun _ => rfl)

end

end GaloisForLFunctions.HTGeometry
