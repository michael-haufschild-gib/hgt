import GaloisForLFunctions.RHTower.ThetaCompactRealGroundProfiles
import GaloisForLFunctions.RHTower.ThetaIsolatedPrimeAtomBounds
import GaloisForLFunctions.RHTower.ThetaPrimeLogCellPositivePairs

/-!
# Genuine prime resonance reverses modulus interference

At arbitrarily large actual primes, two narrow physical translates have
strictly positive full Weil energies, while taking the modulus strictly
decreases that energy. The resonant prime correlation equals the entire
physical mass and is strictly positive. The continuous interaction is made
smaller by narrowing the supports. No atom is deleted from the form.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem exists_arbitrarily_large_prime_resonant_modulus_decrease (N : ℕ) :
    ∃ (n : ℕ) (phi psi : 𝓢(ℝ, ℝ)) (r : ℝ), N ≤ n ∧ Nat.Prime n ∧ 0 < r ∧
      screwSignThreshold < Real.log n - 2 * r ∧
      HasCompactSupport phi ∧ HasCompactSupport psi ∧
      Function.support phi = Metric.ball 0 r ∧
      Function.support psi = Metric.ball (Real.log n) r ∧
      (∀ x, 0 ≤ phi x) ∧ (∀ x, 0 ≤ psi x) ∧ 0 < phi 0 ∧ 0 < psi (Real.log n) ∧
      (∀ x, (phi + psi) x = |(phi - psi) x|) ∧
      0 < thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
        thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi - psi)).toBoundedContinuousFunction ∧
      0 < thetaRealArithmeticQuadratic (phi + psi) ∧
      thetaRealArithmeticQuadratic (phi + psi) < thetaRealArithmeticQuadratic (phi - psi) := by
  obtain ⟨delta, C, hd, hC, hlocal⟩ := exists_thetaReal_center_independent_gap
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (tendsto_vonMangoldt_div_sqrt_zero.eventually
      (Iio_mem_nhds (div_pos hC (by positivity : (0 : ℝ) < 4))))
  obtain ⟨n, hn, hprime⟩ := Nat.exists_infinite_primes (max N M)
  let d : ℝ := Real.log n
  let w : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n
  have hw : 0 < w := div_pos (ArithmeticFunction.vonMangoldt_pos_iff.mpr hprime.isPrimePow)
    (Real.sqrt_pos.mpr (by exact_mod_cast hprime.pos))
  have hwC : w < C / 4 := hM n ((le_max_right _ _).trans hn)
  obtain ⟨e, he, hegap, hisolate⟩ := exists_logNat_isolating_radius hprime.two_le
  let E := Real.exp ((d + 1) / 2)
  have hE : 0 < E := Real.exp_pos _
  let r := min (delta / 2) (min (e / 4) (min (1 / 2 : ℝ) (w / (8 * E))))
  have hr : 0 < r := lt_min (half_pos hd)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hrd : r < delta := (min_le_left _ _).trans_lt (half_lt_self hd)
  have hre : r ≤ e / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrw : r ≤ w / (8 * E) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hgap : screwSignThreshold < d - 2 * r := by dsimp only [d]; linarith
  let F : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩
  let g : ℝ → ℝ := fun x => F (x - d)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := F.contDiff.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport g := by
    convert F.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (-d)) using 1
    funext x
    rfl
  let phi := thetaCompactRealGroundProfile F F.contDiff F.hasCompactSupport
  let psi := thetaCompactRealGroundProfile g hg hgc
  have hpc := hasCompactSupport_thetaCompactRealGroundProfile F F.contDiff F.hasCompactSupport
  have hqc := hasCompactSupport_thetaCompactRealGroundProfile g hg hgc
  have hps : Function.support phi = Metric.ball 0 r := by
    rw [support_thetaCompactRealGroundProfile]
    exact F.support_eq
  have hqs : Function.support psi = Metric.ball d r := by
    rw [support_thetaCompactRealGroundProfile]
    ext x
    change x - d ∈ Function.support F ↔ x ∈ Metric.ball d r
    rw [F.support_eq, Metric.mem_ball, Metric.mem_ball, Real.dist_eq, Real.dist_eq, sub_zero]
  have hp (x : ℝ) : 0 ≤ phi x := div_nonneg F.nonneg (thetaCuspTiltSource.pos x).le
  have hq (x : ℝ) : 0 ≤ psi x := div_nonneg F.nonneg (thetaCuspTiltSource.pos x).le
  have hF0 : 0 < F 0 := F.pos_of_mem_ball (by simpa only [Metric.mem_ball, dist_self] using hr)
  have hp0 : 0 < phi 0 := div_pos hF0 (thetaCuspTiltSource.pos 0)
  have hqd : 0 < psi d := by
    change 0 < F (d - d) / thetaCuspFullSource d
    rw [sub_self]
    exact div_pos hF0 (thetaCuspTiltSource.pos d)
  have hmatch (x : ℝ) : g (x + d) = F x := by simp only [g, add_sub_cancel_right]
  have hmasses : thetaGroundNormSq (thetaComplexify psi) = thetaGroundNormSq (thetaComplexify phi) :=
    thetaGroundNormSq_matched_physical_translate F g F.contDiff hg F.hasCompactSupport hgc d hmatch
  have hcross : thetaGroundShiftCross phi psi d = thetaGroundNormSq (thetaComplexify phi) :=
    thetaGroundShiftCross_matched_physical_translate F g F.contDiff hg F.hasCompactSupport hgc d hmatch
  have hm : 0 < thetaGroundNormSq (thetaComplexify phi) := thetaGroundNormSq_pos_of_ne_zero _ (by
    rw [thetaComplexify_apply]
    exact Complex.ofReal_ne_zero.mpr hp0.ne')
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y := by
    intro x hx y hy
    rw [hqs, Real.ball_eq_Ioo] at hx
    rw [hps, Real.ball_eq_Ioo] at hy
    linarith [hx.1, hy.2, screwSignThreshold_pos]
  have hactive : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ m : ℕ, IsPrimePow m → x - y = Real.log m → m ∈ ({n} : Finset ℕ) := by
    intro x hx y hy m hmp hlog
    rw [hqs, Real.ball_eq_Ioo] at hx
    rw [hps, Real.ball_eq_Ioo] at hy
    apply Finset.mem_singleton.mpr
    apply hisolate m (by have := IsPrimePow.one_lt hmp; omega)
    rw [← hlog, abs_lt]
    change -e < x - y - d ∧ x - y - d < e
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hatom : thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
      thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi - psi)).toBoundedContinuousFunction =
      2 * w * thetaGroundNormSq (thetaComplexify phi) := by
    have h := thetaPrimeScalingCross_difference_eq_finite phi psi {n} hsep hactive
    rw [Finset.sum_singleton] at h
    change _ = 2 * w * thetaGroundShiftCross phi psi d at h
    rwa [hcross] at h
  have hdifference := thetaRealArithmeticQuadratic_ordered_prime_correction phi psi hsep
  rw [hatom] at hdifference
  have hcontinuous := abs_thetaGammaPolarGroundCrossPairing_balls_le phi psi hpc hqc hr.le
    hps.subset hqs.subset (by simpa only [sub_zero] using hgap.le)
  rw [sub_zero, hmasses] at hcontinuous
  have hcoef : 2 * (Real.exp ((d + 2 * r) / 2) * r) ≤ w / 4 := by
    have he' : Real.exp ((d + 2 * r) / 2) ≤ E := Real.exp_le_exp.mpr (by linarith)
    have hprod := mul_le_mul_of_nonneg_right he' hr.le
    have hwr := (le_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < 8) hE)).mp hrw
    nlinarith only [hprod, hwr]
  have hcbound : |thetaGammaPolarGroundCrossPairing phi psi| ≤
      (w / 4) * thetaGroundNormSq (thetaComplexify phi) := by
    have hprod := mul_le_mul_of_nonneg_right hcoef hm.le
    nlinarith only [hcontinuous, hprod]
  obtain ⟨hclower, hcupper⟩ := abs_le.mp hcbound
  have hpts : tsupport phi ⊆ Metric.ball 0 delta :=
    (closure_minimal (hps.subset.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hrd)
  have hqts : tsupport psi ⊆ Metric.ball d delta :=
    (closure_minimal (hqs.subset.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hrd)
  have hplocal := hlocal phi hpc 0 hpts
  have hqlocal := hlocal psi hqc d hqts
  have hpara := thetaRealArithmeticQuadratic_compact_parallelogram phi psi hpc hqc
  rw [hmasses] at hqlocal
  have hwm := mul_pos hw hm
  have hsmall := mul_lt_mul_of_pos_right hwC hm
  have hpositive : 0 < thetaRealArithmeticQuadratic (phi + psi) := by
    nlinarith only [hdifference, hclower, hpara, hplocal, hqlocal, hsmall, hwm]
  have hdecrease : thetaRealArithmeticQuadratic (phi + psi) <
      thetaRealArithmeticQuadratic (phi - psi) := by
    nlinarith only [hdifference, hcupper, hwm]
  refine ⟨n, phi, psi, r, (le_max_left _ _).trans hn, hprime, hr, hgap,
    hpc, hqc, hps, hqs, hp, hq, hp0, hqd, ?_, ?_, hpositive, hdecrease⟩
  · intro x
    by_cases hpx : phi x = 0
    · simp only [add_apply, sub_apply, hpx, zero_add, zero_sub, abs_neg, abs_of_nonneg (hq x)]
    · have hqx : psi x = 0 := by
        by_contra hqx
        have := hsep x hqx x hpx
        linarith
      simp only [add_apply, sub_apply, hqx, add_zero, sub_zero, abs_of_nonneg (hp x)]
  · rw [hatom]
    positivity

end RHTower
