import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeClearedDomination
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompleteAngularSourceProjection
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

/-! Entire dependence of the polynomial-cleared original quotient pairing. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup Metric
open scoped ContDiff
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

/-- The original quotient integral with the full scalar field multiplied by its clearing polynomial. -/
def clearedResidualPeriod (q : XiZeroCopy) (u : ℂ) : ℂ :=
  ∫ z : UpperHalfPlane, clearedScalar u (coordinates z) * squareResidual q (coordinates z)
    ∂D4BMModularCore.measure

/-- The cleared original integrand is spatially continuous, including real spectral parameters. -/
theorem clearedScalar_squareResidual_continuous (q : XiZeroCopy) (u : ℂ) :
    Continuous (fun z : UpperHalfPlane => clearedScalar u (coordinates z) * squareResidual q (coordinates z)) := by
  have hm := (height_cpow_contDiffOn (1/2-u) ∞).continuousOn
  have hp := (height_cpow_contDiffOn (1/2+u) ∞).continuousOn
  have ht := (cuspTailPart_contDiffOn .scalar u).continuousOn
  have hc : ContinuousOn (clearedScalar u) domain :=
    ((continuousOn_const.mul hm).add (continuousOn_const.mul hp)).add (continuousOn_const.mul ht)
  exact (hc.mul (squareResidual_continuousOn q)).comp_continuous (by
    apply continuous_pi; intro i; fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im) (fun z => z.im_pos)

/-- The full cleared product is absolutely admitted to the original quotient measure. -/
theorem clearedScalar_squareResidual_integrable (q : XiZeroCopy) (u : ℂ) :
    Integrable (fun z : UpperHalfPlane => clearedScalar u (coordinates z) * squareResidual q (coordinates z))
      D4BMModularCore.measure := by
  obtain ⟨C,hC,hb⟩ := clearedScalar_squareResidual_fd_uniform q (‖u‖+1) (by positivity)
  apply Integrable.mono' (integrable_const C) (clearedScalar_squareResidual_continuous q u).aestronglyMeasurable
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  exact hb u z (by linarith) hz

/-- The actual quotient pairing is entire after polynomial clearing, by a common cusp majorant. -/
theorem clearedResidualPeriod_differentiable (q : XiZeroCopy) :
    Differentiable ℂ (clearedResidualPeriod q) := by
  intro u0
  obtain ⟨C,hC,hb⟩ := clearedScalar_squareResidual_fd_uniform q (‖u0‖+1) (by positivity)
  let F : ℂ → UpperHalfPlane → ℂ := fun u => fd.indicator
    (fun z => clearedScalar u (coordinates z) * squareResidual q (coordinates z))
  have hmeas (u : ℂ) (_ : u ∈ ball u0 1) : AEStronglyMeasurable (F u) D4BMModularCore.measure :=
    (clearedScalar_squareResidual_continuous q u).aestronglyMeasurable.indicator
      ModularGroup.isClosed_fd.measurableSet
  have hdiff (z : UpperHalfPlane) : DifferentiableOn ℂ (fun u => F u z) (ball u0 1) := by
    by_cases hz : z ∈ fd
    · simpa only [F,indicator_of_mem hz] using
        ((clearedScalar_differentiable (coordinates z) z.im_pos).mul_const
          (squareResidual q (coordinates z))).differentiableOn
    · simpa only [F,indicator_of_notMem hz] using (differentiableOn_const (0:ℂ) :
        DifferentiableOn ℂ (fun _ : ℂ => (0:ℂ)) (ball u0 1))
  have hbound (z : UpperHalfPlane) (u : ℂ) (hu : u ∈ ball u0 1) : ‖F u z‖ ≤ C := by
    by_cases hz : z ∈ fd
    · simp only [F,indicator_of_mem hz]
      apply hb u z _ hz
      have hnorm : ‖u‖ ≤ ‖u0‖ + ‖u-u0‖ := norm_le_norm_add_norm_sub' u u0
      have hdist : ‖u-u0‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hu
      linarith
    · simpa only [F,indicator_of_notMem hz,norm_zero] using hC
  have hd := differentiableAt_integral_of_cauchy_dominated (F := F) (z₀ := u0)
    (R := 1) (bound := fun _ => C) (by norm_num) hmeas hdiff hbound (integrable_const C)
  have he : (fun u => ∫ z, F u z ∂D4BMModularCore.measure) = clearedResidualPeriod q := by
    funext u
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    exact indicator_of_mem hz _
  rw [he] at hd
  exact hd

/-- At nonreal parameters the cleared quotient integral is the polynomial times the original one. -/
theorem clearedResidualPeriod_eq (q : XiZeroCopy) (u : ℂ) (hu : u.im ≠ 0) :
    clearedResidualPeriod q u = clearFactor u * scalarResidualPeriod q u := by
  unfold clearedResidualPeriod scalarResidualPeriod
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  rw [clearedScalar_eq u hu]
  ring

end
end RHTower.D4BMJointSource
