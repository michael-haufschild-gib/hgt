import GaloisForLFunctions.RHTower.SelbergLocalTestGreen
import GaloisForLFunctions.RHTower.SelbergMaassRegulatorMass

/-!
# Actual Maass curvature on compact tests

The original finite congruence trace defines a positive real linear functional on
C² compact tests supported in the upper half-plane. Two local integrations by
parts and quantitative scalar square-root errors identify its actual regularized
limit for every real eigenvalue. Positivity gives domination by compact cutoffs.
No pointwise curvature-limit interchange or representing measure is asserted.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassWeakCurvature
open SelbergMaassMean SelbergMaassCongruenceTrace SelbergMaassTraceEnergy
  SelbergMaassTraceRegularized SelbergMaassRegularizedArea SelbergMaassRegulatorMass
  SelbergSquareRootRegularizationError SelbergLocalTestGreen
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The square root of the original finite congruence trace density. -/
def amplitude (z : ℂ) : ℝ := Real.sqrt (density N f (ofComplex z))
/-- The original amplitude with its hyperbolic area weight. -/
def amplitudeWeight (z : ℂ) : ℝ := amplitude N f z / z.im ^ 2
/-- The regularized spectral density in planar coordinates. -/
def massWeight (e : Ioi (0 : ℝ)) (z : ℂ) : ℝ :=
  density N f (ofComplex z) / (z.im ^ 2 * radius N f e z)
/-- The full retained regularized curvature, including its nodal correction. -/
def curvatureWeight (e : Ioi (0 : ℝ)) (z : ℂ) : ℝ :=
  remainder N f e (ofComplex z) / radius N f e z

/-- Original source regularity makes the amplitude continuous at every positive height. -/
theorem amplitude_continuousOn : ContinuousOn (amplitude N f) {z : ℂ | 0 < z.im} :=
  (density_contDiffOn N f).continuousOn.sqrt

/-- The actual hyperbolically weighted amplitude is locally continuous. -/
theorem amplitudeWeight_continuousOn : ContinuousOn (amplitudeWeight N f) {z : ℂ | 0 < z.im} :=
  (amplitude_continuousOn N f).div (Complex.continuous_im.pow 2).continuousOn
    (fun _ hz => pow_ne_zero 2 (ne_of_gt hz))

/-- The actual regularized spectral density is locally continuous. -/
theorem massWeight_continuousOn (e : Ioi (0 : ℝ)) :
    ContinuousOn (massWeight N f e) {z : ℂ | 0 < z.im} := by
  exact (density_contDiffOn N f).continuousOn.div
    ((Complex.continuous_im.pow 2).continuousOn.mul (radius_contDiffOn N f e).continuousOn)
    (fun z hz => mul_ne_zero (pow_ne_zero 2 (ne_of_gt hz)) (radius_pos N f e z).ne')

/-- Every actual regularized curvature weight is nonnegative. -/
theorem curvatureWeight_nonneg (e : Ioi (0 : ℝ)) (z : ℂ) : 0 ≤ curvatureWeight N f e z :=
  div_nonneg (remainder_nonneg N f e _) (radius_pos N f e _).le

/-- The original source equation identifies retained curvature with the amplitude Laplacian plus spectral density. -/
theorem curvatureWeight_eq (e : Ioi (0 : ℝ)) {z : ℂ} (hz : 0 < z.im) :
    curvatureWeight N f e z = realLaplacian (radius N f e) z + lam * massWeight N f e z := by
  have hp : point z.re z.im = z := by apply Complex.ext <;> simp [point]
  simpa only [weightedRemainder, weightedMassDensity, hp, curvatureWeight, massWeight] using
    (weightedRemainder_eq N f e (p := (z.re, z.im)) hz)

/-- Original C² regularity makes the regularized planar Laplacian locally continuous. -/
theorem radius_laplacian_continuousOn (e : Ioi (0 : ℝ)) :
    ContinuousOn (realLaplacian (radius N f e)) {z : ℂ | 0 < z.im} := by
  have h (v : ℂ) := (dir_contDiffOn
    (dir_contDiffOn (radius_contDiffOn N f e) (m := 1) (by norm_num) v)
    (m := 0) (by norm_num) v).continuousOn
  exact (h 1).add (h Complex.I)

/-- The source curvature identity gives local continuity of the retained curvature. -/
theorem curvatureWeight_continuousOn (e : Ioi (0 : ℝ)) :
    ContinuousOn (curvatureWeight N f e) {z : ℂ | 0 < z.im} := by
  apply ((radius_laplacian_continuousOn N f e).add
    ((massWeight_continuousOn N f e).const_mul lam)).congr
  intro z hz
  exact curvatureWeight_eq N f e hz

/-- The literal planar integral of a test against actual regularized curvature. -/
def testedCurvature (e : Ioi (0 : ℝ)) (phi : ℂ → ℝ) : ℝ :=
  ∫ z, phi z * curvatureWeight N f e z

/-- The unregularized source functional, with both derivatives acting on the test. -/
def weakCurvature (phi : ℂ → ℝ) : ℝ :=
  (∫ z, realLaplacian phi z * amplitude N f z) + lam * ∫ z, phi z * amplitudeWeight N f z

/-- Every continuous compact test in the upper half-plane pairs integrably with actual curvature. -/
theorem test_curvature_integrable {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (e : Ioi (0 : ℝ)) :
    Integrable (fun z => phi z * curvatureWeight N f e z) :=
  integrable_test_mul hp hc (curvatureWeight_continuousOn N f e) hs

/-- The actual source Green identity moves both derivatives onto the compact C² test. -/
theorem testedCurvature_eq {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (e : Ioi (0 : ℝ)) :
    testedCurvature N f e phi = (∫ z, realLaplacian phi z * radius N f e z) +
      lam * ∫ z, phi z * massWeight N f e z := by
  have hi := integrable_test_mul hp.continuous hc (radius_laplacian_continuousOn N f e) hs
  have hj := integrable_test_mul hp.continuous hc (massWeight_continuousOn N f e) hs
  have he : (fun z => phi z * curvatureWeight N f e z) =
      (fun z => phi z * realLaplacian (radius N f e) z + lam * (phi z * massWeight N f e z)) := by
    funext z
    by_cases hz : 0 < z.im
    · rw [curvatureWeight_eq N f e hz]; ring
    · have hpz : phi z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
      simp only [hpz, zero_mul, mul_zero, zero_add]
  rw [testedCurvature, he, integral_add hi (hj.const_mul lam), integral_const_mul,
    integral_test_laplacian hp hc hs (radius_contDiffOn N f e)]

/-- Regularization increases the original amplitude, including at its zeros. -/
theorem radius_sub_amplitude_nonneg (e : Ioi (0 : ℝ)) (z : ℂ) :
    0 ≤ radius N f e z - amplitude N f z :=
  sub_nonneg.mpr (sqrt_le_regularized _ _)

/-- The actual amplitude error is at most the positive regulator everywhere. -/
theorem radius_sub_amplitude_le (e : Ioi (0 : ℝ)) (z : ℂ) :
    radius N f e z - amplitude N f z ≤ (e : ℝ) := by
  have h := regularized_le_sqrt_add (density_nonneg N f (ofComplex z)) e.2.le
  change Real.sqrt (density N f (ofComplex z) + (e : ℝ) ^ 2) - Real.sqrt (density N f (ofComplex z)) ≤ (e : ℝ)
  linarith

/-- The regularized spectral density is bounded by the actual amplitude density. -/
theorem massWeight_le_amplitudeWeight (e : Ioi (0 : ℝ)) (z : ℂ) :
    massWeight N f e z ≤ amplitudeWeight N f z := by
  unfold massWeight amplitudeWeight amplitude radius
  rw [mul_comm (z.im ^ 2), ← div_div]
  exact div_le_div_of_nonneg_right (weighted_sqrt_le (density_nonneg N f _) e.2) (sq_nonneg z.im)

/-- The spectral-density error is at most half the regulator times inverse squared height. -/
theorem amplitudeWeight_sub_mass_le (e : Ioi (0 : ℝ)) (z : ℂ) :
    amplitudeWeight N f z - massWeight N f e z ≤ (e : ℝ) / 2 * (1 / z.im ^ 2) := by
  have h := div_le_div_of_nonneg_right
    (weighted_sqrt_error_le_half (density_nonneg N f (ofComplex z)) e.2) (sq_nonneg z.im)
  unfold amplitudeWeight amplitude massWeight radius
  calc
    _ = (Real.sqrt (density N f (ofComplex z)) - density N f (ofComplex z) /
        Real.sqrt (density N f (ofComplex z) + (e : ℝ) ^ 2)) / z.im ^ 2 := by ring
    _ ≤ (e : ℝ) / 2 / z.im ^ 2 := h
    _ = _ := by ring

/-- Inverse squared height is continuous on the open upper half-plane. -/
theorem inverse_height_continuousOn :
    ContinuousOn (fun z : ℂ => 1 / z.im ^ 2) {z : ℂ | 0 < z.im} :=
  continuousOn_const.div (Complex.continuous_im.pow 2).continuousOn
    (fun _ hz => pow_ne_zero 2 (ne_of_gt hz))

/-- Every absolute compact test has integrable inverse-square height weight. -/
theorem norm_test_height_integrable {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    Integrable (fun z => ‖phi z‖ / z.im ^ 2) := by
  simpa only [mul_one_div] using integrable_norm_test_mul hp hc inverse_height_continuousOn hs

/-- Both literal integrals defining the source weak curvature are genuinely integrable on admissible tests. -/
theorem test_amplitude_integrable {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    Integrable (fun z => realLaplacian phi z * amplitude N f z) ∧
      Integrable (fun z => phi z * amplitudeWeight N f z) :=
  ⟨integrable_test_mul (laplacian_continuous hp) (laplacian_hasCompactSupport hc)
      (amplitude_continuousOn N f) ((laplacian_tsupport_subset phi).trans hs),
    integrable_test_mul hp.continuous hc (amplitudeWeight_continuousOn N f) hs⟩

/-- The Laplacian-test pairing has explicit error bounded by regulator times its L¹ norm. -/
theorem laplacian_radius_pairing_error {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (e : Ioi (0 : ℝ)) :
    ‖(∫ z, realLaplacian phi z * radius N f e z) - ∫ z, realLaplacian phi z * amplitude N f z‖ ≤
      (e : ℝ) * ∫ z, ‖realLaplacian phi z‖ := by
  have h := norm_pairing_sub_le (laplacian_continuous hp) (laplacian_hasCompactSupport hc)
    ((laplacian_tsupport_subset phi).trans hs) (radius_contDiffOn N f e).continuousOn
    (amplitude_continuousOn N f) (G := amplitude N f) (w := fun _ => (1 : ℝ)) continuousOn_const
    (c := (e : ℝ)) (fun z _ => by
      rw [Real.norm_of_nonneg (radius_sub_amplitude_nonneg N f e z), mul_one]
      exact radius_sub_amplitude_le N f e z)
  simpa only [mul_one] using h

/-- The spectral test pairing has explicit error bounded by half the regulator times its weighted L¹ norm. -/
theorem mass_pairing_error {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (e : Ioi (0 : ℝ)) :
    ‖(∫ z, phi z * massWeight N f e z) - ∫ z, phi z * amplitudeWeight N f z‖ ≤
      (e : ℝ) / 2 * ∫ z, ‖phi z‖ / z.im ^ 2 := by
  have h := norm_pairing_sub_le hp hc hs (amplitudeWeight_continuousOn N f)
    (massWeight_continuousOn N f e) inverse_height_continuousOn (c := (e : ℝ) / 2)
    (fun z _ => by
      rw [Real.norm_of_nonneg (sub_nonneg.mpr (massWeight_le_amplitudeWeight N f e z))]
      exact amplitudeWeight_sub_mass_le N f e z)
  simpa only [norm_sub_rev, mul_one_div] using h

/-- The finite test-dependent constant in the quantitative weak-curvature error. -/
def testBudget (lam : ℝ) (phi : ℂ → ℝ) : ℝ :=
  (∫ z, ‖realLaplacian phi z‖) + |lam| / 2 * ∫ z, ‖phi z‖ / z.im ^ 2

/-- The quantitative test budget is nonnegative for every real spectral parameter. -/
theorem testBudget_nonneg (lam : ℝ) (phi : ℂ → ℝ) : 0 ≤ testBudget lam phi :=
  add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
    (mul_nonneg (div_nonneg (abs_nonneg _) (by norm_num))
      (integral_nonneg (fun z => div_nonneg (norm_nonneg _) (sq_nonneg z.im))))

/-- The actual compact-test curvature error is at most regulator times the explicit test budget, for every real eigenvalue. -/
theorem testedCurvature_error_le {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (e : Ioi (0 : ℝ)) :
    ‖testedCurvature N f e phi - weakCurvature N f phi‖ ≤ (e : ℝ) * testBudget lam phi := by
  rw [testedCurvature_eq N f hp hc hs e, weakCurvature]
  have hr := laplacian_radius_pairing_error N f hp hc hs e
  have hm := mass_pairing_error N f hp.continuous hc hs e
  have he : (∫ z, realLaplacian phi z * radius N f e z) + lam * (∫ z, phi z * massWeight N f e z) -
      ((∫ z, realLaplacian phi z * amplitude N f z) + lam * ∫ z, phi z * amplitudeWeight N f z) =
      ((∫ z, realLaplacian phi z * radius N f e z) - ∫ z, realLaplacian phi z * amplitude N f z) +
        lam * ((∫ z, phi z * massWeight N f e z) - ∫ z, phi z * amplitudeWeight N f z) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Real.norm_eq_abs lam]
  refine (add_le_add hr (mul_le_mul_of_nonneg_left hm (abs_nonneg lam))).trans_eq ?_
  unfold testBudget
  ring

/-- Actual regularized curvature converges on every admissible compact C² test, retaining all concentration. -/
theorem testedCurvature_limit {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    Tendsto (fun e : Ioi (0 : ℝ) => testedCurvature N f e phi)
      regulatorAtZero (𝓝 (weakCurvature N f phi)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun e : Ioi (0 : ℝ) => (e : ℝ) * testBudget lam phi) regulatorAtZero (𝓝 0) := by
    simpa only [zero_mul] using regulator_coe_limit.mul_const (testBudget lam phi)
  exact tendsto_const_nhds.squeeze' hlim (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (testedCurvature_error_le N f hp hc hs))

/-- Actual regularized curvature is nonnegative on nonnegative tests. -/
theorem testedCurvature_nonneg {phi : ℂ → ℝ} (hn : ∀ z, 0 ≤ phi z) (e : Ioi (0 : ℝ)) :
    0 ≤ testedCurvature N f e phi :=
  integral_nonneg (fun z => mul_nonneg (hn z) (curvatureWeight_nonneg N f e z))

/-- The unregularized source weak curvature is nonnegative on every nonnegative admissible test. -/
theorem weakCurvature_nonneg {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hn : ∀ z, 0 ≤ phi z) : 0 ≤ weakCurvature N f phi :=
  ge_of_tendsto (testedCurvature_limit N f hp hc hs)
    (Eventually.of_forall (testedCurvature_nonneg N f hn))

/-- Actual regularized curvature is additive on integrable compact test pairings. -/
theorem testedCurvature_add {phi psi : ℂ → ℝ}
    (hp : Continuous phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hq : Continuous psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ {z : ℂ | 0 < z.im})
    (e : Ioi (0 : ℝ)) :
    testedCurvature N f e (fun z => phi z + psi z) =
      testedCurvature N f e phi + testedCurvature N f e psi := by
  unfold testedCurvature
  simp_rw [add_mul]
  exact integral_add (test_curvature_integrable N f hp hc hs e)
    (test_curvature_integrable N f hq hd ht e)

/-- Actual regularized curvature commutes with real scalar multiplication. -/
theorem testedCurvature_const_mul (phi : ℂ → ℝ) (c : ℝ) (e : Ioi (0 : ℝ)) :
    testedCurvature N f e (fun z => c * phi z) = c * testedCurvature N f e phi := by
  unfold testedCurvature
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

/-- Pointwise ordering of admissible tests orders their actual curvature integrals. -/
theorem testedCurvature_mono {phi psi : ℂ → ℝ}
    (hp : Continuous phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hq : Continuous psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ {z : ℂ | 0 < z.im})
    (h : ∀ z, phi z ≤ psi z) (e : Ioi (0 : ℝ)) :
    testedCurvature N f e phi ≤ testedCurvature N f e psi :=
  integral_mono (test_curvature_integrable N f hp hc hs e)
    (test_curvature_integrable N f hq hd ht e)
    (fun z => mul_le_mul_of_nonneg_right (h z) (curvatureWeight_nonneg N f e z))

/-- A pointwise compact-test envelope bounds the actual regularized curvature pairing. -/
theorem testedCurvature_norm_le {phi psi : ℂ → ℝ}
    (hq : Continuous psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ {z : ℂ | 0 < z.im})
    {c : ℝ} (h : ∀ z, ‖phi z‖ ≤ c * psi z) (e : Ioi (0 : ℝ)) :
    ‖testedCurvature N f e phi‖ ≤ c * testedCurvature N f e psi := by
  unfold testedCurvature
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((test_curvature_integrable N f hq hd ht e).const_mul c)
  filter_upwards with z
  rw [norm_mul, Real.norm_of_nonneg (curvatureWeight_nonneg N f e z), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h z) (curvatureWeight_nonneg N f e z)

/-- The actual source weak curvature is additive on admissible C² tests. -/
theorem weakCurvature_add {phi psi : ℂ → ℝ}
    (hp : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hq : ContDiff ℝ 2 psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ {z : ℂ | 0 < z.im}) :
    weakCurvature N f (fun z => phi z + psi z) = weakCurvature N f phi + weakCurvature N f psi := by
  have hleft := testedCurvature_limit N f (hp.add hq) (hc.add hd)
    ((tsupport_add phi psi).trans (union_subset hs ht))
  have hright := (testedCurvature_limit N f hp hc hs).add (testedCurvature_limit N f hq hd ht)
  simp only [testedCurvature_add N f hp.continuous hc hs hq.continuous hd ht] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The actual source weak curvature commutes with real scalar multiplication. -/
theorem weakCurvature_const_mul {phi : ℂ → ℝ}
    (hp : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (c : ℝ) : weakCurvature N f (fun z => c * phi z) = c * weakCurvature N f phi := by
  have hleft := testedCurvature_limit N f ((contDiff_const (c := c)).mul hp) hc.mul_left
    ((tsupport_mul_subset_right (f := fun _ => c) (g := phi)).trans hs)
  simp only [testedCurvature_const_mul] at hleft
  exact tendsto_nhds_unique hleft ((testedCurvature_limit N f hp hc hs).const_mul c)

/-- The source weak-curvature limit preserves pointwise test ordering. -/
theorem weakCurvature_mono {phi psi : ℂ → ℝ}
    (hp : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hq : ContDiff ℝ 2 psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ {z : ℂ | 0 < z.im})
    (h : ∀ z, phi z ≤ psi z) : weakCurvature N f phi ≤ weakCurvature N f psi :=
  le_of_tendsto_of_tendsto (testedCurvature_limit N f hp hc hs) (testedCurvature_limit N f hq hd ht)
    (Eventually.of_forall (testedCurvature_mono N f hp.continuous hc hs hq.continuous hd ht h))

/-- A dominating admissible test controls the source weak curvature without derivatives of the dominated test in the bound. -/
theorem weakCurvature_norm_le {phi psi : ℂ → ℝ}
    (hp : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hq : ContDiff ℝ 2 psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ {z : ℂ | 0 < z.im})
    {c : ℝ} (h : ∀ z, ‖phi z‖ ≤ c * psi z) : ‖weakCurvature N f phi‖ ≤ c * weakCurvature N f psi :=
  le_of_tendsto_of_tendsto (testedCurvature_limit N f hp hc hs).norm
    ((testedCurvature_limit N f hq hd ht).const_mul c)
    (Eventually.of_forall (testedCurvature_norm_le N f hq.continuous hd ht h))

/-- A nonnegative compact cutoff gives an order-zero bound on every admissible test supported in its unit region. -/
theorem weakCurvature_cutoff_bound {phi chi : ℂ → ℝ}
    (hp : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hq : ContDiff ℝ 2 chi) (hd : HasCompactSupport chi) (ht : tsupport chi ⊆ {z : ℂ | 0 < z.im})
    (hn : ∀ z, 0 ≤ chi z) (hone : ∀ z ∈ tsupport phi, chi z = 1)
    {c : ℝ} (hc0 : 0 ≤ c) (hb : ∀ z, ‖phi z‖ ≤ c) :
    ‖weakCurvature N f phi‖ ≤ c * weakCurvature N f chi := by
  apply weakCurvature_norm_le N f hp hc hs hq hd ht
  intro z
  by_cases hz : z ∈ tsupport phi
  · rw [hone z hz, mul_one]
    exact hb z
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
    exact mul_nonneg hc0 (hn z)

/-- The original source has a finite nonnegative order-zero bound on every compact subset of the upper half-plane. The cutoff and test integrability are constructed internally. -/
theorem exists_compact_order_zero_bound {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ {z : ℂ | 0 < z.im}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ phi : ℂ → ℝ, ContDiff ℝ 2 phi → tsupport phi ⊆ K →
      ∀ c : ℝ, 0 ≤ c → (∀ z, ‖phi z‖ ≤ c) → ‖weakCurvature N f phi‖ ≤ c * C := by
  obtain ⟨chi, hp, hc, hs, hn, hone⟩ := exists_nonnegative_cutoff hK hKU
  refine ⟨weakCurvature N f chi, weakCurvature_nonneg N f hp hc hs hn, ?_⟩
  intro phi hq ht c hc0 hb
  have hd : HasCompactSupport phi := hK.of_isClosed_subset isClosed_closure ht
  exact weakCurvature_cutoff_bound N f hq hd (ht.trans hKU) hp hc hs hn
    (fun z hz => hone z (ht hz)) hc0 hb

end
end GaloisForLFunctions.RHTower.SelbergMaassWeakCurvature
