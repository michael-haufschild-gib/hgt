import GaloisForLFunctions.RHTower.ThetaNonlinearExtremalJump
import GaloisForLFunctions.RHTower.ThetaFarPositiveBumpPairs
import GaloisForLFunctions.RHTower.ThetaGammaPolarKernelOrientation

/-!
# Positive quadratic energy and nonlinear escape for actual theta arithmetic

Opposite smooth plateaus in an integer-log gap have no extremal prime
links, but positive continuous extremal mass. The complete cosh action
therefore tends to minus infinity, even when the full quadratic energy
is strictly positive. This refutes global nonlinear positivity, not RH.
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

open GaloisForLFunctions.RHTower

private theorem extremalJump_mem_gap (phi psi : 𝓢(ℝ, ℝ)) {c r u x : ℝ}
    (hp : ∀ y, 0 ≤ phi y ∧ phi y ≤ 1) (hq : ∀ y, 0 ≤ psi y ∧ psi y ≤ 1)
    (hs : Function.support phi ⊆ Metric.ball 0 r)
    (ht : Function.support psi ⊆ Metric.ball c r) (hsep : 0 < c - 2 * r)
    (hu : 0 < u) (he : |thetaRealJump (phi - psi) u x| = 2) :
    u ∈ Ioo (c - 2 * r) (c + 2 * r) := by
  change |(phi (x + u) - psi (x + u)) - (phi x - psi x)| = 2 at he
  rcases le_total 0 ((phi (x + u) - psi (x + u)) - (phi x - psi x)) with h | h
  · rw [abs_of_nonneg h] at he
    have hx : psi x ≠ 0 := by intro hz; rw [hz] at he; linarith [(hp (x + u)).2, (hq (x + u)).1, (hp x).1]
    have hy : phi (x + u) ≠ 0 := by intro hz; rw [hz] at he; linarith [(hq x).2, (hq (x + u)).1, (hp x).1]
    have hxb := ht hx
    have hyb := hs hy
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hxb hyb
    exfalso
    linarith [hxb.1, hyb.2]
  · rw [abs_of_nonpos h] at he
    have hx : phi x ≠ 0 := by intro hz; rw [hz] at he; linarith [(hq (x + u)).2, (hp (x + u)).1, (hq x).1]
    have hy : psi (x + u) ≠ 0 := by intro hz; rw [hz] at he; linarith [(hp x).2, (hp (x + u)).1, (hq x).1]
    have hxb := hs hx
    have hyb := ht hy
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hxb hyb
    constructor <;> linarith [hxb.1, hxb.2, hyb.1, hyb.2]

private theorem primeExtremalMass_eq_zero_of_gap (phi psi : 𝓢(ℝ, ℝ)) {c r : ℝ}
    (hp : ∀ y, 0 ≤ phi y ∧ phi y ≤ 1) (hq : ∀ y, 0 ≤ psi y ∧ psi y ≤ 1)
    (hs : Function.support phi ⊆ Metric.ball 0 r)
    (ht : Function.support psi ⊆ Metric.ball c r) (hsep : 0 < c - 2 * r)
    (hfree : ∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo (c - 2 * r) (c + 2 * r)) :
    thetaPrimeExtremalMass (phi - psi) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with p
  by_cases hn : 2 ≤ p.1
  · have hlog : 0 < Real.log (p.1 : ℝ) := Real.log_pos
      (by exact_mod_cast (show 1 < p.1 by omega))
    have he : |thetaRealJump (phi - psi) (Real.log p.1) p.2| ≠ 2 :=
      fun h => hfree p.1 hn (extremalJump_mem_gap phi psi hp hq hs ht hsep hlog h)
    simp only [he, ↓reduceIte, Pi.zero_apply]
  · have hsmall : p.1 = 0 ∨ p.1 = 1 := by omega
    rcases hsmall with h | h <;> simp [h, thetaRealJump]

private theorem continuousExtremalMass_pos_of_plateaus (phi psi : 𝓢(ℝ, ℝ)) {c r : ℝ}
    (hr : 0 < r) (hp : ∀ y, 0 ≤ phi y ∧ phi y ≤ 1)
    (hq : ∀ y, 0 ≤ psi y ∧ psi y ≤ 1)
    (hs : Function.support phi ⊆ Metric.ball 0 r)
    (ht : Function.support psi ⊆ Metric.ball c r) (hsep : 0 < c - 2 * r)
    (hfar : screwSignThreshold < c - 2 * r)
    (hleft : ∀ x ∈ Metric.closedBall 0 (r / 2), (phi - psi) x = 1)
    (hright : ∀ x ∈ Metric.closedBall c (r / 2), (phi - psi) x = -1) :
    0 < thetaContinuousExtremalMass (phi - psi) := by
  have hweight (u x : ℝ) (hu : 0 < u)
      (he : |thetaRealJump (phi - psi) u x| = 2) :
      0 < thetaContinuousWeight (u, x) := by
    have hloc := extremalJump_mem_gap phi psi hp hq hs ht hsep hu he
    exact mul_pos (mul_pos ((thetaGammaPolarScalingKernel_pos_iff_threshold hu).mpr
      (hfar.trans hloc.1)) (thetaCuspTiltSource.pos x)) (thetaCuspTiltSource.pos (x + u))
  have hnonneg : ∀ᵐ p ∂thetaContinuousLinkMeasure,
      0 ≤ thetaContinuousExtremalDensity (phi - psi) p := by
    have hpos : ∀ᵐ p : ℝ × ℝ ∂thetaContinuousLinkMeasure, 0 < p.1 := by
      apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact Eventually.of_forall fun _ => hu
    filter_upwards [hpos] with p hp0
    unfold thetaContinuousExtremalDensity
    split_ifs with he
    · exact (div_pos (hweight p.1 p.2 hp0 he) (by norm_num)).le
    · exact le_rfl
  apply (integral_pos_iff_support_of_nonneg_ae hnonneg
    (integrable_thetaContinuousExtremalDensity (phi - psi))).mpr
  let box := Metric.ball c (r / 8) ×ˢ Metric.ball (0 : ℝ) (r / 8)
  have hball : Metric.ball c (r / 8) ⊆ Ioi (0 : ℝ) := by
    intro u hu
    simp only [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
    change 0 < u
    linarith [hu.1]
  have hboxpos : 0 < thetaContinuousLinkMeasure box := by
    change 0 < (volume.restrict (Ioi (0 : ℝ))).prod volume
      (Metric.ball c (r / 8) ×ˢ Metric.ball (0 : ℝ) (r / 8))
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hball]
    exact CanonicallyOrderedAdd.mul_pos.mpr
      ⟨Metric.measure_ball_pos volume c (by positivity),
        Metric.measure_ball_pos volume 0 (by positivity)⟩
  apply hboxpos.trans_le (measure_mono ?_)
  rintro ⟨u, x⟩ ⟨hu, hx⟩
  have hu0 := hball hu
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hu hx
  have hl : x ∈ Metric.closedBall 0 (r / 2) := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hr' : x + u ∈ Metric.closedBall c (r / 2) := by
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hu.1, hu.2, hx.1, hx.2]
  have he : |thetaRealJump (phi - psi) u x| = 2 := by
    rw [thetaRealJump, hleft x hl, hright (x + u) hr']
    norm_num
  change thetaContinuousExtremalDensity (phi - psi) (u, x) ≠ 0
  rw [thetaContinuousExtremalDensity, if_pos he]
  exact (div_pos (hweight u x hu0 he) (by norm_num)).ne'

/-- Actual compact smooth profiles have positive full quadratic energy but a negative
extremal-link limit. No hypothetical arithmetic source or RH premise is used. -/
theorem exists_positive_quadratic_negative_nonlinear_limit :
    ∃ chi : 𝓢(ℝ, ℝ), HasCompactSupport chi ∧ (∀ x, |chi x| ≤ 1) ∧
      0 < thetaRealArithmeticQuadratic chi ∧ thetaPrimeExtremalMass chi = 0 ∧
      0 < thetaContinuousExtremalMass chi ∧
      Tendsto (fun a => Real.exp (-2 * a) * thetaNonlinearAction chi a) atTop
        (𝓝 (-thetaContinuousExtremalMass chi)) := by
  obtain ⟨R, kappa, _, hk, hcoercive⟩ := RHTower.exists_thetaReal_farIntegerLogGap_coercivity
  obtain ⟨_, _, c, r, hr, hfar, _, _, _, _, _, _, _, _, hfree⟩ :=
    RHTower.exists_farIntegerLogFree_bump_pair (max R (max 0 screwSignThreshold + 1))
  have hR : R ≤ c - 2 * r := (le_max_left _ _).trans hfar
  have hsep : 0 < c - 2 * r := by
    have := (le_max_right _ _).trans hfar
    linarith [le_max_left (0 : ℝ) screwSignThreshold]
  have hthreshold : screwSignThreshold < c - 2 * r := by
    have := (le_max_right _ _).trans hfar
    linarith [le_max_right (0 : ℝ) screwSignThreshold]
  let F : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩
  let H : ContDiffBump c := ⟨r / 2, r, by linarith, by linarith⟩
  let phi : 𝓢(ℝ, ℝ) := F.hasCompactSupport.toSchwartzMap F.contDiff
  let psi : 𝓢(ℝ, ℝ) := H.hasCompactSupport.toSchwartzMap H.contDiff
  have hps : Function.support phi = Metric.ball 0 r := F.support_eq
  have hqs : Function.support psi = Metric.ball c r := H.support_eq
  have hp (x : ℝ) : 0 ≤ phi x ∧ phi x ≤ 1 := ⟨F.nonneg, F.le_one⟩
  have hq (x : ℝ) : 0 ≤ psi x ∧ psi x ≤ 1 := ⟨H.nonneg, H.le_one⟩
  have hleft (x : ℝ) (hx : x ∈ Metric.closedBall 0 (r / 2)) : (phi - psi) x = 1 := by
    have hF : F x = 1 := F.one_of_mem_closedBall hx
    have hH : H x = 0 := by
      apply H.zero_of_le_dist
      change r ≤ dist x c
      rw [Real.dist_eq]
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
      have := neg_le_abs (x - c)
      linarith [hx.2]
    change F x - H x = 1
    rw [hF, hH, sub_zero]
  have hright (x : ℝ) (hx : x ∈ Metric.closedBall c (r / 2)) : (phi - psi) x = -1 := by
    have hH : H x = 1 := H.one_of_mem_closedBall hx
    have hF : F x = 0 := by
      apply F.zero_of_le_dist
      change r ≤ dist x 0
      rw [Real.dist_eq, sub_zero]
      simp only [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
      have := le_abs_self x
      linarith [hx.1]
    change F x - H x = -1
    rw [hF, hH]; ring
  have hb (x : ℝ) : |(phi - psi) x| ≤ 1 := by
    rw [sub_apply, abs_le]
    constructor <;> linarith [(hp x).1, (hp x).2, (hq x).1, (hq x).2]
  have hprime := primeExtremalMass_eq_zero_of_gap phi psi hp hq hps.subset hqs.subset hsep hfree
  have hmass := continuousExtremalMass_pos_of_plateaus phi psi hr hp hq hps.subset hqs.subset
    hsep hthreshold hleft hright
  have hco := hcoercive phi psi F.hasCompactSupport H.hasCompactSupport 0 c r hr.le
    (by simpa only [sub_zero] using hR) hps.subset hqs.subset
    (by simpa only [sub_zero] using hfree)
  have hp0 : phi 0 ≠ 0 := by
    change F 0 ≠ 0
    rw [F.one_of_mem_closedBall (by change dist (0 : ℝ) 0 ≤ r / 2; simp; positivity)]
    norm_num
  have hnorm := RHTower.thetaGroundNormSq_pos_of_ne_zero (thetaComplexify phi)
    (by simpa only [thetaComplexify_apply, ne_eq, Complex.ofReal_eq_zero] using hp0)
  have hquad : 0 < thetaRealArithmeticQuadratic (phi - psi) :=
    (mul_pos hk (add_pos_of_pos_of_nonneg hnorm (thetaGroundNormSq_nonneg _))).trans_le hco.2
  refine ⟨phi - psi, F.hasCompactSupport.sub H.hasCompactSupport, hb, hquad, hprime, hmass, ?_⟩
  simpa only [hprime, zero_sub] using tendsto_thetaNonlinearAction_scaled (phi - psi) hb

/-- Global nonlinear minimization fails even along a direction with positive quadratic energy. -/
theorem exists_positive_quadratic_nonlinear_escape :
    ∃ chi : 𝓢(ℝ, ℝ), HasCompactSupport chi ∧ (∀ x, |chi x| ≤ 1) ∧
      0 < thetaRealArithmeticQuadratic chi ∧ Tendsto (thetaNonlinearAction chi) atTop atBot := by
  obtain ⟨chi, hc, hb, hq, _, hm, hlim⟩ := exists_positive_quadratic_negative_nonlinear_limit
  have he : Tendsto (fun a : ℝ => Real.exp (2 * a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  have h := he.atTop_mul_neg (neg_neg_of_pos hm) hlim
  refine ⟨chi, hc, hb, hq, ?_⟩
  convert h using 1
  ext a
  rw [← mul_assoc, ← Real.exp_add, show 2 * a + -2 * a = 0 by ring,
    Real.exp_zero, one_mul]

end RHTower.ThetaSourceWard
