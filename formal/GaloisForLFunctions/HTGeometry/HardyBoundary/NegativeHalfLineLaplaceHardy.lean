import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.NegativeHalfLineLaplaceContinuity
import GaloisForLFunctions.HTGeometry.HalfPlaneHardy
import GaloisForLFunctions.HTGeometry.CausalLaplaceDelay
import GaloisForLFunctions.HTGeometry.HardyDiskMultiplier
import GaloisForLFunctions.HTGeometry.CaratheodoryNevanlinnaPick
import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness

/-!
# The negative-half-line Laplace transform as a Hardy function

Reflection identifies the actual negative-half-line transform with the existing
positive-ray Laplace transform. Square-integrability gives Hardy admission;
integrability gives a bounded disk multiplier after the Cayley map.
-/

noncomputable section
open MeasureTheory Set Complex Filter Topology Metric
open _root_.RHTower

namespace GaloisForLFunctions.HTGeometry

/-- Reflection identifies the two literal Laplace conventions. -/
theorem negativeHalfLineLaplace_eq_laplaceRay_reflect (f : ℝ → ℂ)
    (hs : ∀ u, 0 ≤ u → f u = 0) (z : ℂ) :
    negativeHalfLineLaplace f z = laplaceRay (fun u => f (-u)) z := by
  unfold negativeHalfLineLaplace laplaceRay
  rw [← integral_neg_eq_self
    (fun u : ℝ => Complex.exp (z * (u : ℂ)) * f u) volume]
  calc
    _ = ∫ u : ℝ, f (-u) * expRay z u := by
      apply integral_congr_ae
      refine Eventually.of_forall fun u => ?_
      simp only [expRay, Complex.ofReal_neg, mul_neg]
      exact mul_comm _ _
    _ = ∫ u in Ioi (0 : ℝ), f (-u) * expRay z u := by
      apply (causal_integral_ray _ _).symm
      intro u hu
      rw [hs (-u) (by linarith only [hu]), zero_mul]

/-- The reflected profile retains its square-integrability on the positive ray. -/
theorem memLp_reflected_negativeProfile {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (fun u => f (-u)) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (hf.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))).mono_measure
    Measure.restrict_le_self

/-- A negative-half-line square-integrable profile has a Hardy Laplace transform. -/
theorem isHalfPlaneHardy_negativeHalfLineLaplace {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hs : ∀ u, 0 ≤ u → f u = 0) :
    IsHalfPlaneHardy (negativeHalfLineLaplace f)
      (∫ u in Ioi (0 : ℝ), ‖f (-u)‖ ^ (2 : ℕ)) := by
  have he : negativeHalfLineLaplace f = laplaceRay (fun u => f (-u)) :=
    funext (negativeHalfLineLaplace_eq_laplaceRay_reflect f hs)
  rw [he]
  exact isHalfPlaneHardy_laplaceRay (memLp_reflected_negativeProfile hf)

/-- The original L¹ mass bounds all Laplace values in the closed right half-plane. -/
theorem norm_negativeHalfLineLaplace_le {f : ℝ → ℂ} (hf : Integrable f)
    (hs : ∀ u, 0 ≤ u → f u = 0) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖negativeHalfLineLaplace f z‖ ≤ ∫ u, ‖f u‖ := by
  calc
    _ ≤ ∫ u : ℝ, ‖Complex.exp (z * (u : ℂ)) * f u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, ‖f u‖ :=
      integral_mono (integrable_negativeHalfLineLaplace hf hs hz).norm hf.norm
        (norm_negativeHalfLineLaplaceIntegrand_le hs hz)

/-- The actual half-line transform, transported to a bounded analytic disk multiplier. -/
def negativeHalfLineLaplaceDiskMultiplier (f : ℝ → ℂ)
    (h1 : Integrable f) (h2 : MemLp f 2 (volume : Measure ℝ))
    (hs : ∀ u, 0 ≤ u → f u = 0) : DiskMultiplier where
  fn := fun z => negativeHalfLineLaplace f (diskToRight z)
  diff := (isHalfPlaneHardy_negativeHalfLineLaplace h2 hs).holo.comp
    (fun _ hz => (diskToRight_analyticAt hz).differentiableAt.differentiableWithinAt)
    (fun _ hz => diskToRight_re_pos hz)
  bd := ∫ u, ‖f u‖
  bd_nonneg := integral_nonneg fun _ => norm_nonneg _
  bd_le := fun _ hz => norm_negativeHalfLineLaplace_le h1 hs (diskToRight_re_pos hz).le

/-- The Cayley transform preserves continuity up to every finite boundary point. -/
theorem continuousOn_negativeHalfLineLaplace_comp_diskToRight {f : ℝ → ℂ}
    (hf : Integrable f) (hs : ∀ u, 0 ≤ u → f u = 0) :
    ContinuousOn (fun z => negativeHalfLineLaplace f (diskToRight z))
      {z : ℂ | ‖z‖ ≤ 1 ∧ z ≠ 1} := by
  have hc : ContinuousOn diskToRight {z : ℂ | ‖z‖ ≤ 1 ∧ z ≠ 1} := by
    intro z hz
    exact ((continuousAt_const.add continuousAt_id).div
      (continuousAt_const.sub continuousAt_id)
      (sub_ne_zero.mpr hz.2.symm)).continuousWithinAt
  refine (continuousOn_negativeHalfLineLaplace hf hs).comp hc ?_
  intro z hz
  exact re_cayleyInv_nonneg hz.1 hz.2

/-- Closed-half-plane zero exclusion includes every finite point of the Cayley boundary. -/
theorem negativeHalfLineLaplace_comp_diskToRight_ne_zero {f : ℝ → ℂ}
    (hf : ∀ z : ℂ, 0 ≤ z.re → negativeHalfLineLaplace f z ≠ 0)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (hne : z ≠ 1) :
    negativeHalfLineLaplace f (diskToRight z) ≠ 0 :=
  hf _ (re_cayleyInv_nonneg hz hne)

/-- Reflection identifies the masses on the two endpoint intervals. -/
theorem integral_reflect_initial_interval (g : ℝ → ℝ) (a : ℝ) :
    (∫ x in Ioo (0 : ℝ) a, g (-x)) = ∫ x in Ioo (-a) 0, g x := by
  rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo]
  rw [← integral_neg_eq_self ((Ioo (-a) 0).indicator g) volume]
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  change (Ioo (0 : ℝ) a).indicator (fun x => g (-x)) x =
    (Ioo (-a) 0).indicator g (-x)
  by_cases hx : x ∈ Ioo (0 : ℝ) a
  · have hn : -x ∈ Ioo (-a) 0 :=
      ⟨by linarith only [hx.2], by linarith only [hx.1]⟩
    rw [indicator_of_mem hx, indicator_of_mem hn]
  · have hn : -x ∉ Ioo (-a) 0 := by
      intro hn
      apply hx
      exact ⟨by linarith only [hn.2], by linarith only [hn.1]⟩
    rw [indicator_of_notMem hx, indicator_of_notMem hn]

#print axioms isHalfPlaneHardy_negativeHalfLineLaplace
#print axioms negativeHalfLineLaplaceDiskMultiplier
#print axioms continuousOn_negativeHalfLineLaplace_comp_diskToRight
#print axioms integral_reflect_initial_interval

end GaloisForLFunctions.HTGeometry
