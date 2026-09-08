import GaloisForLFunctions.RHTower.SelbergPlanarTestScaling
import GaloisForLFunctions.RHTower.SelbergMaassCurvatureMeasure

/-!
# No point atoms in actual Maass curvature

The actual amplitude is continuous, including at common source zeros. A shrinking
C² cutoff has vanishing planar mass and a scale-independent Laplacian L¹ norm.
Subtracting the amplitude's center value cancels the total Laplacian, so its
actual curvature pairing tends to zero. Positivity then excludes every point
atom of the constructed measure. Curve-supported nodal charge is retained.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCurvatureNoAtoms
open SelbergPlanarTestScaling SelbergMaassTraceEnergy SelbergLocalTestGreen
  SelbergMaassCurvatureMeasure SelbergMaassWeakCurvature SelbergMaassRegulatorMass
noncomputable section

/-- A bound only on test support controls the actual integral against that test. -/
theorem norm_test_pairing_le {phi F : ℂ → ℝ} (hp : Continuous phi) (hc : HasCompactSupport phi)
    {B : ℝ} (hB : ∀ z ∈ tsupport phi, ‖F z‖ ≤ B) :
    ‖∫ z, phi z * F z‖ ≤ B * ∫ z, ‖phi z‖ := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((hp.norm.integrable_of_hasCompactSupport hc.norm).const_mul B)
  filter_upwards with z
  rw [norm_mul]
  by_cases hz : z ∈ tsupport phi
  · simpa only [mul_comm B] using mul_le_mul_of_nonneg_left (hB z hz) (norm_nonneg (phi z))
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero, zero_mul, mul_zero]

/-- Continuity gives vanishing oscillation on the actual shrinking cutoff supports. -/
theorem eventually_cutoff_oscillation {F : ℂ → ℝ} {c : ℂ} (hF : ContinuousAt F c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r : Ioi (0 : ℝ) in regulatorAtZero,
      ∀ z ∈ tsupport (cutoff c r), ‖F z - F c‖ ≤ δ := by
  obtain ⟨η, hη, hnear⟩ := Metric.continuousAt_iff.mp hF δ hδ
  filter_upwards [regulator_coe_limit.eventually_lt_const (half_pos hη)] with r hr z hz
  have hd := cutoff_support c r.2 hz
  rw [Metric.mem_closedBall] at hd
  have ht : dist z c < η := lt_of_le_of_lt hd (by linarith)
  simpa only [dist_eq_norm] using (hnear ht).le

/-- A continuous germ is uniformly bounded on sufficiently small cutoff supports. -/
theorem eventually_cutoff_bound {F : ℂ → ℝ} {c : ℂ} (hF : ContinuousAt F c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r : Ioi (0 : ℝ) in regulatorAtZero,
      ∀ z ∈ tsupport (cutoff c r), ‖F z‖ ≤ B := by
  refine ⟨1 + ‖F c‖, by positivity, ?_⟩
  filter_upwards [eventually_cutoff_oscillation hF (δ := 1) (by norm_num)] with r hr z hz
  calc
    ‖F z‖ ≤ ‖F z - F c‖ + ‖F c‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + ‖F c‖ := by linarith [hr z hz]

/-- Shrinking cutoff pairings of a continuous germ vanish with their planar area. -/
theorem cutoff_pairing_limit {F : ℂ → ℝ} {c : ℂ} (hF : ContinuousAt F c) :
    Tendsto (fun r : Ioi (0 : ℝ) => ∫ z, cutoff c r z * F z) regulatorAtZero (𝓝 0) := by
  obtain ⟨B, _, hB⟩ := eventually_cutoff_bound hF
  have hl : Tendsto (fun r : Ioi (0 : ℝ) => B * ((r : ℝ) ^ 2 * ∫ z, ‖unitCutoff z‖))
      regulatorAtZero (𝓝 0) := by
    simpa only [zero_pow two_ne_zero, zero_mul, mul_zero] using
      ((regulator_coe_limit.pow 2).mul_const (∫ z, ‖unitCutoff z‖)).const_mul B
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hB, hl.eventually_lt_const hε] with r hr he
  have h := norm_test_pairing_le (cutoff_contDiff c r).continuous (cutoff_compact c r.2.ne') hr
  rw [integral_norm_cutoff] at h
  simpa only [dist_zero_right] using h.trans_lt he

/-- Constant-mode cancellation forces shrinking Laplacian tests of a locally continuous source to vanish. -/
theorem laplacian_cutoff_pairing_limit {F : ℂ → ℝ}
    (hF : ContinuousOn F {z : ℂ | 0 < z.im}) {c : ℂ} (hc : 0 < c.im) :
    Tendsto (fun r : Ioi (0 : ℝ) => ∫ z, realLaplacian (cutoff c r) z * F z)
      regulatorAtZero (𝓝 0) := by
  let C : ℝ := ∫ z, ‖realLaplacian unitCutoff z‖
  have hC : 0 ≤ C := integral_nonneg (fun _ => norm_nonneg _)
  have hFc := hF.continuousAt (isOpen_upperHalfPlaneSet.mem_nhds hc)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hsmall := eventually_cutoff_oscillation hFc hδ
  filter_upwards [hsmall, regulator_coe_limit.eventually_lt_const (half_pos hc)] with r hr hrc
  have hs : tsupport (cutoff c r) ⊆ {z : ℂ | 0 < z.im} := cutoff_support_upper c r.2 (by linarith)
  have hp := cutoff_contDiff c (r : ℝ)
  have hk := cutoff_compact c r.2.ne'
  have hD := laplacian_continuous hp
  have hDk := laplacian_hasCompactSupport hk
  have hDs := (laplacian_tsupport_subset (cutoff c r)).trans hs
  have hi := integrable_test_mul hD hDk hF hDs
  have hconst : Integrable (fun z : ℂ => realLaplacian (cutoff c r) z * F c) :=
    (hD.integrable_of_hasCompactSupport hDk).mul_const (F c)
  have heq : (∫ z, realLaplacian (cutoff c r) z * (F z - F c)) =
      ∫ z, realLaplacian (cutoff c r) z * F z := by
    simp_rw [mul_sub]
    rw [integral_sub hi hconst, integral_mul_const, integral_laplacian_zero hp hk hs, zero_mul, sub_zero]
  have hb := norm_test_pairing_le (F := fun z => F z - F c) hD hDk
    (fun z hz => hr z (laplacian_tsupport_subset (cutoff c r) hz))
  rw [heq, integral_norm_cutoff_laplacian c r.2.ne'] at hb
  have hstrict : δ * C < ε := by
    calc
      δ * C < δ * (C + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
      _ = ε := by dsimp [δ]; field_simp
  simpa only [dist_zero_right] using hb.trans_lt hstrict

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Every actual shrinking centered weak-curvature test tends to zero, including at common source zeros. -/
theorem weakCurvature_cutoff_limit (c : ℍ) :
    Tendsto (fun r : Ioi (0 : ℝ) => weakCurvature N f (cutoff (c : ℂ) r))
      regulatorAtZero (𝓝 0) := by
  have hA := laplacian_cutoff_pairing_limit (amplitude_continuousOn N f) c.im_pos
  have hB := cutoff_pairing_limit ((amplitudeWeight_continuousOn N f).continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds c.im_pos))
  simpa only [weakCurvature, mul_zero, zero_add] using hA.add (hB.const_mul lam)

/-- The actual curvature measure integrates shrinking centered cutoffs to zero. -/
theorem integral_cutoff_limit (c : ℍ) :
    Tendsto (fun r : Ioi (0 : ℝ) => ∫ z : ℍ, cutoff (c : ℂ) r z ∂curvatureMeasure N f)
      regulatorAtZero (𝓝 0) := by
  apply (weakCurvature_cutoff_limit N f c).congr'
  filter_upwards [regulator_coe_limit.eventually_lt_const (half_pos c.im_pos)] with r hr
  exact (integral_original_test N f (cutoff_contDiff (c : ℂ) r)
    (cutoff_compact (c : ℂ) r.2.ne') (cutoff_support_upper (c : ℂ) r.2 (by change 2 * (r : ℝ) < c.im; linarith))).symm

/-- The actual curvature measure has zero mass at every point of the upper half-plane. -/
theorem curvatureMeasure_singleton (c : ℍ) : curvatureMeasure N f {c} = 0 := by
  have hb : ∀ᶠ r : Ioi (0 : ℝ) in regulatorAtZero,
      curvatureMeasure N f {c} ≤ ENNReal.ofReal (∫ z : ℍ, cutoff (c : ℂ) r z ∂curvatureMeasure N f) := by
    filter_upwards [regulator_coe_limit.eventually_lt_const (half_pos c.im_pos)] with r hr
    apply (original_test_integrable N f (cutoff_contDiff (c : ℂ) r).continuous
      (cutoff_compact (c : ℂ) r.2.ne') (cutoff_support_upper (c : ℂ) r.2 (by change 2 * (r : ℝ) < c.im; linarith))).measure_le_integral
    · exact Eventually.of_forall (fun z : ℍ => cutoff_nonneg (c : ℂ) r z)
    · intro z hz
      have hz' : z = c := Set.mem_singleton_iff.mp hz
      rw [hz', cutoff_center]
  have hl := ENNReal.tendsto_ofReal (integral_cutoff_limit N f c)
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds hl hb
  simpa only [ENNReal.ofReal_zero, nonpos_iff_eq_zero] using hle

/-- Actual Maass curvature is atomless, without any spectral bound or nonvanishing at a point. -/
instance curvatureMeasure_noAtoms : NullSingletonClass (curvatureMeasure N f) :=
  ⟨curvatureMeasure_singleton N f⟩

/-- Every countable exceptional set has zero actual curvature measure. -/
theorem curvatureMeasure_countable {s : Set ℍ} (hs : s.Countable) : curvatureMeasure N f s = 0 :=
  hs.measure_zero _

end
end GaloisForLFunctions.RHTower.SelbergMaassCurvatureNoAtoms
