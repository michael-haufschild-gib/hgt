import GaloisForLFunctions.RHTower.SelbergMaassResidualSupport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Literal source density of the Maass current limit

The original current numerator vanishes at common source zeros. Elsewhere its
regularized denominator tends to the positive amplitude cube. Extended-real
monotone convergence transfers the proved compact curvature bound to the
literal density integral, establishing genuine integrability. This density
then dominates every regulator on compact tests, so signed-test dominated
convergence identifies the actual current-measure pairings. The separate
nodal residual remains present; no spectral quarter comparison is assumed.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassCurrentDensity
open SelbergMaassCongruenceTrace SelbergMaassTraceRegularized SelbergMaassWeakCurvature
  SelbergMaassRegulatorMass SelbergMaassCurrentCurvature SelbergMaassCurrentTests
  SelbergMaassCurrentFunctional SelbergMaassCurrentMeasures SelbergMaassContinuousCurvature
  SelbergUpperHalfPlaneCompactTests
noncomputable section

/-- A literal decreasing sequence of positive regulators approaching zero. -/
def regulatorSeq (n : ℕ) : Ioi (0 : ℝ) := ⟨1 / ((n : ℝ) + 1), by change 0 < 1 / ((n : ℝ) + 1); positivity⟩

/-- The sequence reaches the actual regulator-limit filter. -/
theorem regulatorSeq_limit : Tendsto regulatorSeq atTop regulatorAtZero := by
  unfold regulatorAtZero
  apply tendsto_comap_iff.mpr
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The literal regulator sequence is antitone. -/
theorem regulatorSeq_antitone : Antitone regulatorSeq := by
  intro n m hnm
  change 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1)
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 1

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The unregularized source current density, with the literal zero value at common zeros. -/
def sourceCurrentDensity (z : ℂ) : ℝ :=
  currentEnergy N f z / (SelbergMaassWeakCurvature.amplitude N f z) ^ 3

/-- The actual unregularized current density is nonnegative. -/
theorem sourceCurrentDensity_nonneg (z : ℂ) : 0 ≤ sourceCurrentDensity N f z :=
  div_nonneg (currentEnergy_nonneg N f z) (pow_nonneg (Real.sqrt_nonneg _) 3)

/-- The current density vanishes at every original common zero. -/
theorem sourceCurrentDensity_at_node (z : ℍ) (hz : density N f z = 0) :
    sourceCurrentDensity N f z = 0 := by
  rw [sourceCurrentDensity, currentEnergy_zero_at_node N f z hz, zero_div]

/-- The original regularized current has the claimed pointwise limit, including at common zeros. -/
theorem currentWeight_limit (z : ℍ) :
    Tendsto (fun e : Ioi (0 : ℝ) => currentWeight N f e z) regulatorAtZero
      (𝓝 (sourceCurrentDensity N f z)) := by
  by_cases hz : density N f z = 0
  · simp only [currentWeight, currentEnergy_zero_at_node N f z hz, zero_div,
      sourceCurrentDensity_at_node N f z hz]
    exact tendsto_const_nhds
  · have hd : 0 < density N f z := lt_of_le_of_ne (density_nonneg N f z) (Ne.symm hz)
    have hr : Tendsto (fun e : Ioi (0 : ℝ) => radius N f e z) regulatorAtZero
        (𝓝 (SelbergMaassWeakCurvature.amplitude N f z)) := by
      have h := (tendsto_const_nhds (x := density N f z)).add (regulator_coe_limit.pow 2)
      simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero, radius,
        SelbergMaassWeakCurvature.amplitude, ofComplex_apply] using h.sqrt
    apply (tendsto_const_nhds (x := currentEnergy N f (z : ℂ))).div (hr.pow 3)
    exact pow_ne_zero 3 (by simpa only [SelbergMaassWeakCurvature.amplitude, ofComplex_apply]
      using (Real.sqrt_pos.mpr hd).ne')

/-- Every regulated current is pointwise bounded by its actual unregularized density. -/
theorem currentWeight_le_density (e : Ioi (0 : ℝ)) (z : ℍ) :
    currentWeight N f e z ≤ sourceCurrentDensity N f z := by
  apply ge_of_tendsto (currentWeight_limit N f z)
  have he : ∀ᶠ a : Ioi (0 : ℝ) in regulatorAtZero, (a : ℝ) < (e : ℝ) :=
    (tendsto_order.1 regulator_coe_limit).2 (e : ℝ) e.2
  filter_upwards [he] with a ha
  exact currentWeight_antitone N f z ha.le

/-- Supported source tests have the literal pointwise density limit on the whole complex plane. -/
theorem test_density_pointwise_limit {phi : ℂ → ℝ}
    (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (z : ℂ) :
    Tendsto (fun e : Ioi (0 : ℝ) => phi z * currentWeight N f e z) regulatorAtZero
      (𝓝 (phi z * sourceCurrentDensity N f z)) := by
  by_cases hz : 0 < z.im
  · have h := (currentWeight_limit N f (ofComplex z)).const_mul (phi z)
    simpa only [ofComplex_apply_of_im_pos hz] using h
  · have hpz : phi z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
    simp only [hpz, zero_mul]
    exact tendsto_const_nhds

/-- Actual compact density products are measurable, including at original zeros. -/
theorem test_density_aestronglyMeasurable {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    AEStronglyMeasurable (fun z => phi z * sourceCurrentDensity N f z) volume := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (test_current_integrable N f hp hc hs (regulatorSeq n)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z => (test_density_pointwise_limit N f hs z).comp regulatorSeq_limit)

/-- Monotone convergence and the actual curvature bound prove finite density integrals for nonnegative tests. -/
theorem nonnegative_test_density_integrable {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (hn : ∀ z, 0 ≤ phi z) :
    Integrable (fun z => phi z * sourceCurrentDensity N f z) := by
  have hi n := test_current_integrable N f hp hc hs (regulatorSeq n)
  have hl : Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (phi z * currentWeight N f (regulatorSeq n) z)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (phi z * sourceCurrentDensity N f z))) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hi n).aemeasurable.ennreal_ofReal)
    · exact Eventually.of_forall (fun z n m hnm => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (currentWeight_antitone N f z (regulatorSeq_antitone hnm)) (hn z)))
    · exact Eventually.of_forall (fun z => (ENNReal.continuous_ofReal.tendsto _).comp
        ((test_density_pointwise_limit N f hs z).comp regulatorSeq_limit))
  have hb : (∫⁻ z, ENNReal.ofReal (phi z * sourceCurrentDensity N f z)) ≤
      ENNReal.ofReal (continuousCurvature N f phi) := by
    apply le_of_tendsto hl
    exact Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hi n)
        (Eventually.of_forall (fun z => mul_nonneg (hn z) (currentWeight_nonneg N f _ z)))]
      exact ENNReal.ofReal_le_ofReal (testedCurrent_le_limit N f hp hc hs hn (regulatorSeq n)))
  apply (lintegral_ofReal_ne_top_iff_integrable (test_density_aestronglyMeasurable N f hp hc hs)
    (Eventually.of_forall (fun z => mul_nonneg (hn z) (sourceCurrentDensity_nonneg N f z)))).mp
  exact (lt_of_le_of_lt hb ENNReal.ofReal_lt_top).ne

/-- Every signed actual compact test has an integrable density product. -/
theorem test_density_integrable {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    Integrable (fun z => phi z * sourceCurrentDensity N f z) := by
  have hns : tsupport (fun z => ‖phi z‖) ⊆ {z : ℂ | 0 < z.im} :=
    (tsupport_comp_subset (g := fun x : ℝ => ‖x‖) (by simp) phi).trans hs
  apply (nonnegative_test_density_integrable N f hp.norm hc.norm hns (fun z => norm_nonneg _)).mono'
    (test_density_aestronglyMeasurable N f hp hc hs)
  exact Eventually.of_forall (fun z => by
    rw [norm_mul, Real.norm_of_nonneg (sourceCurrentDensity_nonneg N f z)])

/-- The full positive-regulator current limit equals the literal density integral on every signed test. -/
theorem testedCurrent_density_limit {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    Tendsto (fun e : Ioi (0 : ℝ) => testedCurrent N f e phi) regulatorAtZero
      (𝓝 (∫ z, phi z * sourceCurrentDensity N f z)) := by
  letI : regulatorAtZero.IsCountablyGenerated := by unfold regulatorAtZero; infer_instance
  have hns : tsupport (fun z => ‖phi z‖) ⊆ {z : ℂ | 0 < z.im} :=
    (tsupport_comp_subset (g := fun x : ℝ => ‖x‖) (by simp) phi).trans hs
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖phi z‖ * sourceCurrentDensity N f z)
    (Eventually.of_forall (fun e => (test_current_integrable N f hp hc hs e).aestronglyMeasurable))
  · exact Eventually.of_forall (fun e => Eventually.of_forall (fun z => by
      rw [norm_mul, Real.norm_of_nonneg (currentWeight_nonneg N f e z)]
      by_cases hz : 0 < z.im
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [ofComplex_apply_of_im_pos hz] using currentWeight_le_density N f e (ofComplex z)
      · simp only [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), norm_zero, zero_mul, le_refl]))
  · exact test_density_integrable N f hp.norm hc.norm hns
  · exact Eventually.of_forall (test_density_pointwise_limit N f hs)

/-- Integration against the actual current measure equals the source density integral. -/
theorem integral_current_eq_density (g : C_c(ℍ, ℝ)) :
    (∫ z, g z ∂currentMeasure N f) = ∫ z, zeroExtend g z * sourceCurrentDensity N f z :=
  tendsto_nhds_unique (current_limit_integral N f g)
    (testedCurrent_density_limit N f (zeroExtend_continuous g) (zeroExtend_compact g) (zeroExtend_support g))

end
end GaloisForLFunctions.RHTower.SelbergMaassCurrentDensity
