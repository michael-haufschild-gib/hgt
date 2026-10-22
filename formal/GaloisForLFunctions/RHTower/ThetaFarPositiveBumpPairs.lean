import GaloisForLFunctions.RHTower.CCM.CCMFarIntegerLogGapCoercivity

/-!
# Nonzero positive-energy pairs at arbitrary separation

Non-atom intervals and smooth bumps realize the far-gap source class at every
requested separation. Its full sum and difference energies are strictly positive.
This makes the uniform coercivity result nonvacuous without numerical sampling.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem thetaGroundNormSq_pos_of_ne_zero (chi : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : chi x ≠ 0) :
    0 < thetaGroundNormSq chi := by
  have hcont : Continuous (thetaGroundNormDensity chi) := by
    have hk := contDiff_thetaCuspFullSource.continuous
    have hc := chi.continuous
    unfold thetaGroundNormDensity
    fun_prop
  have hp : 0 < thetaGroundNormDensity chi x :=
    mul_pos (pow_pos (show 0 < thetaCuspFullSource x from thetaCuspTiltSource.pos x) 2)
      (pow_pos (norm_pos_iff.mpr hx) 2)
  exact integral_pos_of_integrable_nonneg_nonzero hcont (integrable_thetaGroundNormDensity chi)
    (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hp.ne'

/-- Actual nonnegative, nonzero bump profiles with a completely integer-log-free difference
interval can be placed beyond any prescribed separation. -/
theorem exists_farIntegerLogFree_bump_pair (T : ℝ) :
    ∃ (phi psi : 𝓢(ℝ, ℝ)) (c r : ℝ), 0 < r ∧ T ≤ c - 2 * r ∧
      HasCompactSupport phi ∧ HasCompactSupport psi ∧
      Function.support phi = Metric.ball 0 r ∧ Function.support psi = Metric.ball c r ∧
      (∀ x, 0 ≤ phi x) ∧ (∀ x, 0 ≤ psi x) ∧ 0 < phi 0 ∧ 0 < psi c ∧
      (∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo (c - 2 * r) (c + 2 * r)) := by
  obtain ⟨c, hc, hnot⟩ := exists_atomFree_mem_Ioo
    (show max T 0 + 1 < max T 0 + 2 by linarith)
  obtain ⟨eps, heps, hfree⟩ := exists_atomFree_radius hnot
  let r := min (eps / 8) (1 / 8 : ℝ)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hre : r ≤ eps / 8 := min_le_left _ _
  have hr1 : r ≤ 1 / 8 := min_le_right _ _
  let F : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩
  let H : ContDiffBump c := ⟨r / 2, r, by linarith, by linarith⟩
  let phi : 𝓢(ℝ, ℝ) := F.hasCompactSupport.toSchwartzMap F.contDiff
  let psi : 𝓢(ℝ, ℝ) := H.hasCompactSupport.toSchwartzMap H.contDiff
  have hp (x : ℝ) : phi x = F x := rfl
  have hq (x : ℝ) : psi x = H x := rfl
  have hps : Function.support phi = Metric.ball 0 r := F.support_eq
  have hqs : Function.support psi = Metric.ball c r := H.support_eq
  refine ⟨phi, psi, c, r, hr, ?_, F.hasCompactSupport, H.hasCompactSupport,
    hps, hqs, fun x => F.nonneg, fun x => H.nonneg, ?_, ?_, ?_⟩
  · linarith [hc.1, le_max_left T 0]
  · rw [hp]
    apply F.pos_of_mem_ball
    change dist (0 : ℝ) 0 < r
    simpa only [dist_self] using hr
  · rw [hq]
    apply H.pos_of_mem_ball
    change dist c c < r
    simpa only [dist_self] using hr
  · intro n hn hlog
    have he : |Real.log n - c| < eps := by
      rw [abs_lt]
      constructor <;> linarith [hlog.1, hlog.2]
    exact hfree (Real.log n) he n hn rfl

/-- Unconditional existence of nonzero separated source pairs whose full sum and difference
energies are both strictly positive, at every prescribed distance. -/
theorem exists_arbitrarily_far_positive_thetaPair (T : ℝ) :
    ∃ (phi psi : 𝓢(ℝ, ℝ)) (c r : ℝ), 0 < r ∧ T ≤ c - 2 * r ∧
      HasCompactSupport phi ∧ HasCompactSupport psi ∧
      Function.support phi = Metric.ball 0 r ∧ Function.support psi = Metric.ball c r ∧
      (∀ x, 0 ≤ phi x) ∧ (∀ x, 0 ≤ psi x) ∧ 0 < phi 0 ∧ 0 < psi c ∧
      (∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo (c - 2 * r) (c + 2 * r)) ∧
      0 < thetaRealArithmeticQuadratic (phi + psi) ∧
      0 < thetaRealArithmeticQuadratic (phi - psi) := by
  obtain ⟨R, kappa, _, hk, hcoercive⟩ := exists_thetaReal_farIntegerLogGap_coercivity
  obtain ⟨phi, psi, c, r, hr, hfar, hpc, hqc, hps, hqs, hp, hq, hp0, hqc0, hfree⟩ :=
    exists_farIntegerLogFree_bump_pair (max T R)
  have hTR : T ≤ c - 2 * r := (le_max_left _ _).trans hfar
  have hRR : R ≤ c - 2 * r := (le_max_right _ _).trans hfar
  have h := hcoercive phi psi hpc hqc 0 c r hr.le (by simpa only [sub_zero] using hRR)
    hps.subset hqs.subset (by simpa only [sub_zero] using hfree)
  have hm : 0 < thetaGroundNormSq (thetaComplexify phi) :=
    thetaGroundNormSq_pos_of_ne_zero _ (by
      rw [thetaComplexify_apply]
      exact Complex.ofReal_ne_zero.mpr hp0.ne')
  have hpos : 0 < kappa * (thetaGroundNormSq (thetaComplexify phi) +
      thetaGroundNormSq (thetaComplexify psi)) :=
    mul_pos hk (add_pos_of_pos_of_nonneg hm (thetaGroundNormSq_nonneg _))
  exact ⟨phi, psi, c, r, hr, hTR, hpc, hqc, hps, hqs, hp, hq, hp0, hqc0, hfree,
    hpos.trans_le h.1, hpos.trans_le h.2⟩

end RHTower
