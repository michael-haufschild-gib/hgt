import GaloisForLFunctions.HTGeometry.HilbertHalfPlaneBoundary
import GaloisForLFunctions.HTGeometry.BochnerL2ProbeTotality

/-! The common inverse Fourier vector is causal and recovers the original holomorphic map. -/
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CauchyBoundedHilbertMap
variable (F : CauchyBoundedHilbertMap H)

def causalDatum (t : ℝ) : H := (Real.exp t : ℂ) • F.linePreimage t

theorem causalDatum_probe (ℓ : H →L[ℂ] ℂ) :
    (fun t => ℓ (F.causalDatum t)) =ᵐ[volume]
      hardyDatum (fun w => ℓ (F.value w)) (F.probe_hardy ℓ) := by
  filter_upwards [F.linePreimage_probe_ae ℓ] with t ht
  simp only [causalDatum,map_smul,smul_eq_mul,ht,hardyDatum,one_mul]

/-- Scalar support is upgraded to support of the single spatial vector, without separability. -/
theorem causalDatum_support : ∀ᵐ t ∂(volume : Measure ℝ), t < 0 → F.causalDatum t = 0 := by
  have hp : ∀ᵐ t ∂(volume : Measure ℝ), t < 0 → F.linePreimage t = 0 := by
    apply bochnerL2_ae_zero_on_of_inner_probes _ (Lp.memLp _) (Iio (0 : ℝ)) measurableSet_Iio
    intro v
    let ℓ : H →L[ℂ] ℂ := innerSL ℂ v
    filter_upwards [F.linePreimage_probe_ae ℓ,
      hardyDatum_weight_ae (F.probe_hardy ℓ) one_pos,
      hardyDatum_ae_zero_of_neg (F.probe_hardy ℓ)] with t ht hw hs hneg
    change ℓ (F.linePreimage t) = 0
    rw [ht,← hw,hs hneg,mul_zero]
  filter_upwards [hp] with t ht hneg
  simp only [causalDatum,ht hneg,smul_zero]

theorem causalDatum_damping (t : ℝ) : expRay (1 : ℂ) t • F.causalDatum t = F.linePreimage t := by
  simp only [causalDatum,smul_smul,expRay,Complex.ofReal_exp,one_mul,← Complex.exp_add]
  simp

theorem causalDatum_weighted_memLp :
    MemLp (fun t => expRay (1 : ℂ) t • F.causalDatum t) 2 volume := by
  simp only [F.causalDatum_damping]
  exact Lp.memLp _

private theorem integrand (w : ℂ) (t : ℝ) :
    expRay w t • F.causalDatum t = expRay (w-1) t • F.linePreimage t := by
  simp only [causalDatum,smul_smul,expRay,Complex.ofReal_exp,← Complex.exp_add]
  congr 2
  ring

/-- Norm convergence of the vector Laplace integral, before scalar-probe identification. -/
theorem causalDatum_integrable (w : ℂ) (hw : 1 < w.re) :
    IntegrableOn (fun t => expRay w t • F.causalDatum t) (Ioi (0 : ℝ)) := by
  have hw' : 0 < (w-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  have hE := memLp_two_expRay_restrict hw' 0
  have hP := (Lp.memLp F.linePreimage).restrict (Ioi (0 : ℝ))
  have hi : IntegrableOn (fun t => expRay (w-1) t • F.linePreimage t) (Ioi (0 : ℝ)) :=
    (hE.norm.integrable_mul hP.norm).mono'
      (hE.aestronglyMeasurable.smul hP.aestronglyMeasurable)
      (Eventually.of_forall (fun t => (norm_smul _ _).le))
  simpa only [F.integrand] using hi

/-- The one causal vector recovers the given analytic vector, not merely selected scalar outputs. -/
theorem causalDatum_laplace (w : ℂ) (hw : 1 < w.re) :
    (∫ t in Ioi (0 : ℝ), expRay w t • F.causalDatum t) = F.value w := by
  apply ext_inner_left ℂ
  intro v
  let ℓ : H →L[ℂ] ℂ := innerSL ℂ v
  change ℓ (∫ t in Ioi (0 : ℝ), expRay w t • F.causalDatum t) = ℓ (F.value w)
  calc
    _ = ∫ t in Ioi (0 : ℝ), ℓ (expRay w t • F.causalDatum t) :=
      (ℓ.integral_comp_comm (F.causalDatum_integrable w hw)).symm
    _ = laplaceRay (hardyDatum _ (F.probe_hardy ℓ)) w := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (F.causalDatum_probe ℓ)] with t ht
      rw [map_smul,smul_eq_mul,ht,mul_comm]
    _ = _ := (isHalfPlaneHardy_eq_laplaceRay (F.probe_hardy ℓ) (by linarith : 0 < w.re)).symm

end CauchyBoundedHilbertMap
end
end GaloisForLFunctions.HTGeometry
