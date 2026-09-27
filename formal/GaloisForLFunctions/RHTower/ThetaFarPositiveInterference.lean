import GaloisForLFunctions.RHTower.ThetaFarPositiveBumpPairs

/-!
# Positive cross coupling and positive full energies coexist arbitrarily far out

Nonnegative profiles positive throughout two separated balls have strictly
positive continuous cross pairing beyond the kernel threshold. The previously
proved coercivity then shows that modulus increase can occur while both complete
Weil energies are strictly positive. Thus failure of modulus contraction in this
family does not produce a negative Weil direction.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem thetaGammaPolarGroundCrossPairing_pos_of_balls
    (phi psi : 𝓢(ℝ, ℝ)) {c r : ℝ} (hr : 0 < r)
    (hps : Function.support phi = Metric.ball 0 r)
    (hqs : Function.support psi = Metric.ball c r)
    (hp : ∀ x, 0 ≤ phi x) (hq : ∀ x, 0 ≤ psi x)
    (hgap : screwSignThreshold < c - 2 * r) :
    0 < thetaGammaPolarGroundCrossPairing phi psi := by
  let R : Set (ℝ × ℝ) := Metric.closedBall c r ×ˢ Metric.closedBall 0 r
  let O : Set (ℝ × ℝ) := Metric.ball c r ×ˢ Metric.ball 0 r
  let G : ℝ × ℝ → ℝ := fun p => thetaGammaPolarScalingKernel (p.1 - p.2) *
    thetaCuspFullSource p.1 * thetaCuspFullSource p.2 * phi p.2 * psi p.1
  have hRc : IsCompact R := (isCompact_closedBall c r).prod (isCompact_closedBall (0 : ℝ) r)
  have hRm : MeasurableSet R := Metric.isClosed_closedBall.measurableSet.prod
    Metric.isClosed_closedBall.measurableSet
  have hlag (p : ℝ × ℝ) (hh : p ∈ R) : screwSignThreshold < p.1 - p.2 := by
    obtain ⟨hx, hy⟩ := hh
    rw [Real.closedBall_eq_Icc] at hx hy
    linarith [hx.1, hy.2]
  have hKpos (p : ℝ × ℝ) (hh : p ∈ R) : 0 < thetaGammaPolarScalingKernel (p.1 - p.2) :=
    (thetaGammaPolarScalingKernel_pos_iff_threshold (screwSignThreshold_pos.trans (hlag p hh))).mpr
      (hlag p hh)
  have hKcont : ContinuousOn (fun p : ℝ × ℝ => thetaGammaPolarScalingKernel (p.1 - p.2)) R := by
    have h : ContinuousOn (fun p : ℝ × ℝ => screwRegularKernel (p.1 - p.2)) R :=
      continuousOn_screwRegularKernel.comp (continuous_fst.sub continuous_snd).continuousOn
        (fun p hh => screwSignThreshold_pos.trans (hlag p hh))
    exact h.congr (fun p hh =>
      thetaGammaPolarScalingKernel_eq_screw (screwSignThreshold_pos.trans (hlag p hh)))
  have hk := contDiff_thetaCuspFullSource.continuous
  have hGc : ContinuousOn G R :=
    ((((hKcont.mul (hk.comp continuous_fst).continuousOn).mul
      (hk.comp continuous_snd).continuousOn).mul
      (phi.continuous.comp continuous_snd).continuousOn).mul
      (psi.continuous.comp continuous_fst).continuousOn)
  have hGi : IntegrableOn G R := hGc.integrableOn_compact hRc
  have hGnonneg (p : ℝ × ℝ) (hh : p ∈ R) : 0 ≤ G p := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hKpos p hh).le
      (thetaCuspTiltSource.pos p.1).le) (thetaCuspTiltSource.pos p.2).le) (hp p.2)) (hq p.1)
  have hGzero : ∀ p ∉ R, G p = 0 := by
    intro p hh
    by_cases hphi : phi p.2 = 0
    · simp only [G, hphi, mul_zero, zero_mul]
    by_cases hpsi : psi p.1 = 0
    · simp only [G, hpsi, mul_zero]
    exact False.elim (hh ⟨Metric.ball_subset_closedBall (hqs ▸ hpsi),
      Metric.ball_subset_closedBall (hps ▸ hphi)⟩)
  have hOsub : O ⊆ Function.support G ∩ R := by
    intro p hh
    have hpR : p ∈ R := ⟨Metric.ball_subset_closedBall hh.1, Metric.ball_subset_closedBall hh.2⟩
    have hphi : p.2 ∈ Function.support phi := by rw [hps]; exact hh.2
    have hpsi : p.1 ∈ Function.support psi := by rw [hqs]; exact hh.1
    refine ⟨?_, hpR⟩
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hKpos p hpR).ne'
      (thetaCuspTiltSource.pos p.1).ne') (thetaCuspTiltSource.pos p.2).ne') hphi) hpsi
  have hvol : 0 < volume (Function.support G ∩ R) := by
    apply lt_of_lt_of_le _ (measure_mono hOsub)
    change 0 < volume (Metric.ball c r ×ˢ Metric.ball (0 : ℝ) r)
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_ball, Real.volume_ball]
    exact ENNReal.mul_pos (by simpa using hr) (by simpa using hr)
  have hnonneg : 0 ≤ᵐ[volume.restrict R] G := by
    filter_upwards [ae_restrict_mem hRm] with p hpR
    exact hGnonneg p hpR
  have hpos : 0 < ∫ p in R, G p :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hGi).mpr hvol
  change 0 < ∫ p, G p
  rwa [← setIntegral_eq_integral_of_forall_compl_eq_zero hGzero]

/-- The full energy can increase under absolute value while staying strictly positive;
this happens at arbitrarily large separation, not only near the kernel sign threshold. -/
theorem exists_arbitrarily_far_positive_modulus_increase (T : ℝ) :
    ∃ (phi psi : 𝓢(ℝ, ℝ)) (c r : ℝ), 0 < r ∧ T ≤ c - 2 * r ∧
      HasCompactSupport phi ∧ HasCompactSupport psi ∧
      Function.support phi = Metric.ball 0 r ∧ Function.support psi = Metric.ball c r ∧
      (∀ x, (phi + psi) x = |(phi - psi) x|) ∧
      thetaGroundNormSq (thetaComplexify (phi - psi)) =
        thetaGroundNormSq (thetaComplexify (phi + psi)) ∧
      0 < thetaGammaPolarGroundCrossPairing phi psi ∧
      0 < thetaRealArithmeticQuadratic (phi - psi) ∧
      thetaRealArithmeticQuadratic (phi - psi) < thetaRealArithmeticQuadratic (phi + psi) := by
  obtain ⟨phi, psi, c, r, hr, hfar, hpc, hqc, hps, hqs, hp, hq, _, _, hfree, _, hminus⟩ :=
    exists_arbitrarily_far_positive_thetaPair (max T (screwSignThreshold + 1))
  have hgap : screwSignThreshold < c - 2 * r := by
    have := (le_max_right T (screwSignThreshold + 1)).trans hfar
    linarith
  have hC := thetaGammaPolarGroundCrossPairing_pos_of_balls phi psi hr hps hqs hp hq hgap
  have hpair : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      x - y ∈ Ioo (c - 2 * r) (c + 2 * r) := by
    intro x hx y hy
    rw [hqs, Real.ball_eq_Ioo] at hx
    rw [hps, Real.ball_eq_Ioo] at hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y :=
    fun x hx y hy => (screwSignThreshold_pos.trans hgap).trans (hpair x hx y hy).1
  have habs (x : ℝ) : (phi + psi) x = |(phi - psi) x| := by
    simp only [add_apply, sub_apply]
    by_cases hx : phi x = 0
    · simp [hx, abs_of_nonneg (hq x)]
    have hy : psi x = 0 := by
      by_contra hy
      have hh := hsep x hy x hx
      linarith
    simp [hy, abs_of_nonneg (hp x)]
  have hnorm : thetaGroundNormSq (thetaComplexify (phi - psi)) =
      thetaGroundNormSq (thetaComplexify (phi + psi)) := by
    unfold thetaGroundNormSq thetaGroundNormDensity
    apply integral_congr_ae
    filter_upwards with x
    simp only [thetaComplexify_apply, Complex.norm_real, Real.norm_eq_abs, habs, abs_abs]
  have hatom : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n := by
    intro x hx y hy n hn he
    exact hfree n hn (he ▸ hpair x hx y hy)
  have hdiff := thetaRealArithmeticQuadratic_disjoint_polarization phi psi hsep hatom
  exact ⟨phi, psi, c, r, hr, (le_max_left _ _).trans hfar, hpc, hqc, hps, hqs,
    habs, hnorm, hC, hminus, by linarith⟩

end RHTower
