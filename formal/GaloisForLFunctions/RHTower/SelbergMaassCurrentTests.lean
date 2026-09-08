import GaloisForLFunctions.RHTower.SelbergMaassCurrentCurvature
import GaloisForLFunctions.RHTower.SelbergMaassContinuousCurvature

/-!
# Actual compact-test limits of the Maass current term

The original current weight is locally continuous and antitone in the positive
regulator. Its nonnegative compact-test integrals are bounded by the existing
full curvature limit, using comparison at every smaller regulator. Their finite
supremum is their actual regulator limit. Decomposition into two nonnegative
tests proves convergence for every signed admissible compact test.
No nodal term is discarded and no spectral quarter comparison is assumed.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassCurrentTests
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassSourceCurrents
  SelbergMaassPairPhaseEnergy SelbergMaassCurrentCurvature SelbergMaassTraceRegularized
  SelbergMaassWeakCurvature SelbergMaassRegulatorMass SelbergMaassContinuousCurvature
  SelbergLocalTestGreen
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The actual current-square numerator is continuous on the original upper half-plane. -/
theorem currentEnergy_continuousOn :
    ContinuousOn (currentEnergy N f) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hF (q : Deck N) : ContDiffAt ℝ 2 (field N f q) z := by
    simpa only [ofComplex_apply_of_im_pos hz] using field_smooth N f q (ofComplex z)
  have hV (q : Deck N) : ContinuousAt (field N f q) z := (hF q).continuousAt
  have hD (q : Deck N) (v : ℂ) : ContinuousAt (dir v (field N f q)) z :=
    (dir_contDiffAt (hF q) v).continuousAt
  apply ContinuousAt.continuousWithinAt
  unfold currentEnergy pairEnergy phaseCurrent bracket
  simp only [normSq_eq_norm_sq]
  fun_prop

/-- Every actual positive-regulator current weight is locally continuous. -/
theorem currentWeight_continuousOn (e : Ioi (0 : ℝ)) :
    ContinuousOn (currentWeight N f e) {z : ℂ | 0 < z.im} :=
  (currentEnergy_continuousOn N f).div ((radius_contDiffOn N f e).continuousOn.pow 3)
    (fun z _ => pow_ne_zero 3 (radius_pos N f e z).ne')

/-- Every continuous compact upper-half-plane test has an actual integrable current pairing. -/
theorem test_current_integrable {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (e : Ioi (0 : ℝ)) :
    Integrable (fun z => phi z * currentWeight N f e z) :=
  integrable_test_mul hp hc (currentWeight_continuousOn N f e) hs

/-- The literal planar integral of a test against the actual regulated current weight. -/
def testedCurrent (e : Ioi (0 : ℝ)) (phi : ℂ → ℝ) : ℝ :=
  ∫ z, phi z * currentWeight N f e z

/-- Nonnegative tests give nonnegative actual current integrals. -/
theorem testedCurrent_nonneg {phi : ℂ → ℝ} (hn : ∀ z, 0 ≤ phi z) (e : Ioi (0 : ℝ)) :
    0 ≤ testedCurrent N f e phi :=
  integral_nonneg (fun z => mul_nonneg (hn z) (currentWeight_nonneg N f e z))

/-- The actual current weight decreases with the positive regulator. -/
theorem currentWeight_antitone (z : ℂ) : Antitone (fun e : Ioi (0 : ℝ) => currentWeight N f e z) := by
  intro a b hab
  have ha : 0 < (a : ℝ) := a.2
  have hb : 0 < (b : ℝ) := b.2
  have hab' : (a : ℝ) ≤ (b : ℝ) := hab
  have hr : radius N f a z ≤ radius N f b z := by
    apply Real.sqrt_le_sqrt
    nlinarith
  exact div_le_div_of_nonneg_left (currentEnergy_nonneg N f z)
    (pow_pos (radius_pos N f a z) 3) (pow_le_pow_left₀ (radius_pos N f a z).le hr 3)

/-- Nonnegative actual compact-test current integrals are antitone in the regulator. -/
theorem testedCurrent_antitone {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (hn : ∀ z, 0 ≤ phi z) :
    Antitone (fun e : Ioi (0 : ℝ) => testedCurrent N f e phi) := by
  intro a b hab
  exact integral_mono (test_current_integrable N f hp hc hs b) (test_current_integrable N f hp hc hs a)
    (fun z => mul_le_mul_of_nonneg_left (currentWeight_antitone N f z hab) (hn z))

/-- The actual current contribution is bounded by the full regulated curvature on nonnegative compact tests. -/
theorem testedCurrent_le_curvature {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hn : ∀ z, 0 ≤ phi z) (e : Ioi (0 : ℝ)) :
    testedCurrent N f e phi ≤ testedCurvature N f e phi := by
  apply integral_mono (test_current_integrable N f hp hc hs e) (test_curvature_integrable N f hp hc hs e)
  intro z
  by_cases hz : 0 < z.im
  · have he := curvatureWeight_split N f e (ofComplex z)
    rw [ofComplex_apply_of_im_pos hz] at he
    exact mul_le_mul_of_nonneg_left (by linarith [regulatorGradientWeight_nonneg N f e z]) (hn z)
  · have hpz : phi z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
    simp only [hpz, zero_mul, le_refl]

/-- Comparison at all smaller regulators bounds each actual current integral by the original full curvature limit. -/
theorem testedCurrent_le_limit {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hn : ∀ z, 0 ≤ phi z) (e : Ioi (0 : ℝ)) :
    testedCurrent N f e phi ≤ continuousCurvature N f phi := by
  apply ge_of_tendsto (continuousCurvature_limit N f hp hc hs)
  have he : ∀ᶠ a : Ioi (0 : ℝ) in regulatorAtZero, (a : ℝ) < (e : ℝ) :=
    (tendsto_order.1 regulator_coe_limit).2 (e : ℝ) e.2
  filter_upwards [he] with a ha
  exact (testedCurrent_antitone N f hp hc hs hn ha.le).trans (testedCurrent_le_curvature N f hp hc hs hn a)

/-- The actual positive-test current supremum is finite and is its full positive-regulator limit. -/
theorem nonnegative_current_limit {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (hn : ∀ z, 0 ≤ phi z) :
    Tendsto (fun e : Ioi (0 : ℝ) => testedCurrent N f e phi) regulatorAtZero
      (𝓝 (sSup (range (fun e : Ioi (0 : ℝ) => testedCurrent N f e phi)))) := by
  have hb : BddAbove (range (fun e : Ioi (0 : ℝ) => testedCurrent N f e phi)) :=
    ⟨continuousCurvature N f phi, by rintro _ ⟨e, rfl⟩; exact testedCurrent_le_limit N f hp hc hs hn e⟩
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨b, ⟨e, rfl⟩, hbe⟩ := exists_lt_of_lt_csSup (range_nonempty _) ha
    have he : ∀ᶠ d : Ioi (0 : ℝ) in regulatorAtZero, (d : ℝ) < (e : ℝ) :=
      (tendsto_order.1 regulator_coe_limit).2 (e : ℝ) e.2
    filter_upwards [he] with d hd
    exact hbe.trans_le (testedCurrent_antitone N f hp hc hs hn hd.le)
  · intro b hb'
    exact Eventually.of_forall (fun e => (le_csSup hb (mem_range_self e)).trans_lt hb')

/-- The original regulated current pairing is additive on actual admissible compact tests. -/
theorem testedCurrent_add {phi psi : ℂ → ℝ}
    (hp : Continuous phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hq : Continuous psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ {z : ℂ | 0 < z.im})
    (e : Ioi (0 : ℝ)) :
    testedCurrent N f e (fun z => phi z + psi z) = testedCurrent N f e phi + testedCurrent N f e psi := by
  unfold testedCurrent
  simp_rw [add_mul]
  exact integral_add (test_current_integrable N f hp hc hs e) (test_current_integrable N f hq hd ht e)

/-- The actual regulated current pairing commutes with every real scalar. -/
theorem testedCurrent_const_mul (phi : ℂ → ℝ) (c : ℝ) (e : Ioi (0 : ℝ)) :
    testedCurrent N f e (fun z => c * phi z) = c * testedCurrent N f e phi := by
  unfold testedCurrent
  simp_rw [mul_assoc]
  exact integral_const_mul c _

/-- Every signed compact continuous source test has an actual current limit, derived from two nonnegative test limits. -/
theorem exists_testedCurrent_limit {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    ∃ a : ℝ, Tendsto (fun e : Ioi (0 : ℝ) => testedCurrent N f e phi) regulatorAtZero (𝓝 a) := by
  have hns : tsupport (fun z => ‖phi z‖) ⊆ {z : ℂ | 0 < z.im} :=
    (tsupport_comp_subset (g := fun x : ℝ => ‖x‖) (by simp) phi).trans hs
  have hps : tsupport (fun z => phi z + ‖phi z‖) ⊆ {z : ℂ | 0 < z.im} :=
    (tsupport_comp_subset (g := fun x : ℝ => x + ‖x‖) (by simp) phi).trans hs
  have hpn : ∀ z, 0 ≤ phi z + ‖phi z‖ := by
    intro z
    have h := le_abs_self (-phi z)
    rw [abs_neg, ← Real.norm_eq_abs] at h
    linarith
  have hpLim := nonnegative_current_limit N f (hp.add hp.norm) (hc.add hc.norm) hps hpn
  have hnLim := nonnegative_current_limit N f hp.norm hc.norm hns (fun z => norm_nonneg (phi z))
  refine ⟨sSup (range (fun e : Ioi (0 : ℝ) => testedCurrent N f e (fun z => phi z + ‖phi z‖))) -
    sSup (range (fun e : Ioi (0 : ℝ) => testedCurrent N f e (fun z => ‖phi z‖))), ?_⟩
  have h := hpLim.sub hnLim
  have he (e : Ioi (0 : ℝ)) : testedCurrent N f e (fun z => phi z + ‖phi z‖) -
      testedCurrent N f e (fun z => ‖phi z‖) = testedCurrent N f e phi := by
    rw [testedCurrent_add N f hp hc hs hp.norm hc.norm hns, add_sub_cancel_right]
  exact h.congr' (Eventually.of_forall he)

end
end GaloisForLFunctions.RHTower.SelbergMaassCurrentTests
