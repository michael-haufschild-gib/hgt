import GaloisForLFunctions.RHTower.Heat.HeatForwardSimpleZeros
import GaloisForLFunctions.RHTower.Heat.HeatZeroSumContinuity

/-!
# Simple heat-zero branches

Multiplicity conservation isolates a unique local zero. The spatial and
time Taylor bounds give a quadratic error around its reciprocal-field
velocity, hence its right derivative.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower.DeBruijn
namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

/-- Spatial and time Taylor bounds give a quadratic remainder for a simple zero. -/
private theorem exists_norm_zero_motion_le {t : ℝ} (ht : 0 ≤ t) {a : ℂ}
    (hz : riemannHeat t a = 0) (hd : deriv (riemannHeat t) a ≠ 0) :
    ∃ r > 0, ∃ h₀ > 0, ∃ C ≥ 0, ∀ h ∈ Icc (0 : ℝ) h₀, ∀ z : ℂ,
      ‖z - a‖ ≤ r → riemannHeat (t + h) z = 0 →
      ‖z - (a + (h : ℂ) *
        (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a))‖ ≤ C * h ^ 2 := by
  let b := deriv (riemannHeat t) a
  let F := deriv (deriv (riemannHeat t))
  let c := |a.im| + 1
  let M := ∫ x, |x| ^ 2 * ‖heatWeight t x‖ * Real.exp (c * |x|)
  let L := ∫ x, |x| ^ 3 * ‖heatWeight t x‖ * Real.exp (c * |x|)
  let K := ∫ x, |x| ^ 4 * ‖heatWeight (t + 1) x‖ * Real.exp (c * |x|)
  have hM : 0 ≤ M := integral_nonneg fun x => by positivity
  have hL : 0 ≤ L := integral_nonneg fun x => by positivity
  have hK : 0 ≤ K := integral_nonneg fun x => by positivity
  have hb : 0 < ‖b‖ := norm_pos_iff.mpr hd
  let D := 2 * (‖F a‖ + K) / ‖b‖
  have hD : 0 ≤ D := by positivity
  refine ⟨min 1 (‖b‖ / (4 * (M + 1))), by positivity,
    min 1 (‖b‖ / (4 * (L + 1))), by positivity,
    (M * D ^ 2 + L * D + K) / ‖b‖, by positivity, ?_⟩
  intro h hh z hzr hzero
  have hh0 := hh.1
  have hh1 : h ≤ 1 := hh.2.trans (min_le_left _ _)
  have hr1 : ‖z - a‖ ≤ 1 := hzr.trans (min_le_left _ _)
  have hzim : |z.im| ≤ c := by
    have h1 : |z.im - a.im| ≤ ‖z - a‖ := by
      simpa only [sub_im] using Complex.abs_im_le_norm (z - a)
    have h2 := abs_sub_abs_le_abs_sub z.im a.im
    dsimp only [c]
    linarith only [h1, h2, hr1]
  have hf : ‖riemannHeat t z - b * (z - a)‖ ≤ M * ‖z - a‖ ^ 2 := by
    have h := norm_riemannHeat_taylor_le ht (z₀ := a) hr1
    rwa [hz, sub_zero] at h
  have hg : ‖(fun w => -F w) z - (fun w => -F w) a‖ ≤ L * ‖z - a‖ := by
    calc
      _ = ‖F z - F a‖ := by rw [neg_sub_neg, norm_sub_rev]
      _ ≤ _ := norm_deriv_deriv_riemannHeat_sub_le ht hr1
  have hE : ‖riemannHeat (t + h) z - riemannHeat t z + h * F z‖ ≤ K * h ^ 2 := by
    refine (norm_riemannHeat_time_remainder_le ht hh0 hh1 z).trans ?_
    gcongr
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
      (integrable_pow_mul_heatWeight (by linarith only [ht]) 4 c)
      (Eventually.of_forall fun x => ?_)
    simp only
    gcongr
  have hdM : M * ‖z - a‖ ≤ ‖b‖ / 4 := by
    have h1 : ‖z - a‖ ≤ ‖b‖ / (4 * (M + 1)) := hzr.trans (min_le_right _ _)
    calc
      M * ‖z - a‖ ≤ M * (‖b‖ / (4 * (M + 1))) := by gcongr
      _ ≤ ‖b‖ / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith only [hM, hb]
  have hhL : h * L ≤ ‖b‖ / 4 := by
    have h1 : h ≤ ‖b‖ / (4 * (L + 1)) := hh.2.trans (min_le_right _ _)
    calc
      h * L ≤ ‖b‖ / (4 * (L + 1)) * L := by gcongr
      _ ≤ ‖b‖ / 4 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith only [hL, hb]
  obtain ⟨hdist, hpred⟩ := norm_sub_predicted_le (f := riemannHeat t) (g := fun w => -F w)
    (E := fun w => riemannHeat (t + h) w - riemannHeat t w + h * F w)
    (z₀ := a) (a := b) (z := z) hd hh0 hf hg hE (by rw [← hzero]; ring) hdM hhL
  rw [norm_neg] at hdist
  have hdh : ‖z - a‖ ≤ D * h := by
    refine hdist.trans ?_
    dsimp only [D]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hb hb]
    have hsq : h ^ 2 ≤ h := by
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hh1 hh0
    have hnum : 2 * (h * ‖F a‖ + K * h ^ 2) ≤ 2 * (‖F a‖ + K) * h := by
      nlinarith only [mul_le_mul_of_nonneg_left hsq hK]
    exact mul_le_mul_of_nonneg_right hnum hb.le
  have hrem : ‖z - (a - h * -F a / b)‖ ≤ (M * D ^ 2 + L * D + K) / ‖b‖ * h ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hb, mul_comm]
    refine hpred.trans ?_
    have e1 : M * ‖z - a‖ ^ 2 ≤ M * (D * h) ^ 2 := by gcongr
    have e2 : h * L * ‖z - a‖ ≤ h * L * (D * h) := by gcongr
    nlinarith only [e1, e2]
  convert hrem using 2
  dsimp only [F, b]
  ring

/-- A disk of total multiplicity one contains exactly one simple zero. -/
private theorem exists_unique_heat_zero_of_count_one {s r : ℝ} {a : ℂ}
    (hs : 0 ≤ s) (hr : 0 < r)
    (hfree : ∀ z ∈ sphere a r, riemannHeat s z ≠ 0)
    (hcount : zeroSumBall (riemannHeat s) a r = 1) :
    ∃ z ∈ ball a r, zeroMult (riemannHeat s) z = 1 ∧
      ∀ w ∈ ball a r, riemannHeat s w = 0 ↔ w = z := by
  classical
  obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall hr
    (by linarith only [hr] : r < 2 * r) isOpen_univ (subset_univ _)
    (differentiable_riemannHeat hs).differentiableOn hfree
  have hsum : ∑ z ∈ Z, zeroMult (riemannHeat s) z = 1 := by
    have h : ((∑ z ∈ Z, zeroMult (riemannHeat s) z : ℕ) : ℂ) = 1 := by
      push_cast
      exact hZs.symm.trans hcount
    exact_mod_cast h
  have hcard : Z.card ≤ 1 := by
    rw [← hsum, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun z hz =>
      one_le_zeroMult_riemannHeat hs ((hZz z (hZb z hz)).mpr hz)
  have hne : Z.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
    exact Nat.zero_ne_one hsum
  obtain ⟨z, hz⟩ := hne
  have hsingleton : Z = {z} := by
    ext w
    simp only [Finset.mem_singleton]
    exact ⟨fun hw => Finset.card_le_one.mp hcard w hw z hz, fun hw => hw ▸ hz⟩
  refine ⟨z, hZb z hz, ?_, ?_⟩
  · simpa only [hsingleton, Finset.sum_singleton] using hsum
  · intro w hw
    rw [hZz w hw, hsingleton, Finset.mem_singleton]

/-- A simple heat zero has a unique local branch with velocity given by the heat equation. -/
theorem exists_simple_heat_zero_branch {t : ℝ} (ht : 0 < t) {a : ℂ}
    (hz : riemannHeat t a = 0) (hd : deriv (riemannHeat t) a ≠ 0) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∃ δ > 0, ∃ ζ : ℝ → ℂ,
      ζ 0 = a ∧
      HasDerivWithinAt ζ (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a)
        (Ici 0) 0 ∧
      ∀ h ∈ Icc (0 : ℝ) δ, ζ h ∈ ball a r ∧
        zeroMult (riemannHeat (t + h)) (ζ h) = 1 ∧
        ∀ z ∈ ball a r, riemannHeat (t + h) z = 0 ↔ z = ζ h := by
  classical
  obtain ⟨rm, hrm, hm, hhm, C, hC, hmotion⟩ := exists_norm_zero_motion_le ht.le hz hd
  obtain ⟨rc, hrc, hstable⟩ := eventually_zeroSumBall_riemannHeat_eq ht a
  refine ⟨min rm rc, lt_min hrm hrc, ?_⟩
  intro r hr hrr
  obtain ⟨_, _, hcount⟩ := hstable r hr (hrr.trans (min_le_right _ _))
  have ham := zeroMult_riemannHeat_eq_one ht.le hz hd
  obtain ⟨ε, hε, hεcount⟩ := Metric.eventually_nhds_iff.mp hcount
  let δ := min hm (ε / 2)
  have hδ : 0 < δ := lt_min hhm (by positivity)
  have hchoose : ∀ h : ℝ, ∃ z : ℂ, h ∈ Icc (0 : ℝ) δ →
      z ∈ ball a r ∧ zeroMult (riemannHeat (t + h)) z = 1 ∧
      ∀ w ∈ ball a r, riemannHeat (t + h) w = 0 ↔ w = z := by
    intro h
    by_cases hh : h ∈ Icc (0 : ℝ) δ
    · have he : dist (t + h) t < ε := by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hh.1]
        have hhε := hh.2.trans (min_le_right hm (ε / 2))
        linarith only [hhε, hε]
      obtain ⟨hcs, hfs⟩ := hεcount he
      rw [ham, Nat.cast_one] at hcs
      obtain ⟨z, hzb, hzm, hzz⟩ := exists_unique_heat_zero_of_count_one
        (by linarith only [ht, hh.1]) hr hfs hcs
      exact ⟨z, fun _ => ⟨hzb, hzm, hzz⟩⟩
    · exact ⟨a, fun h => (hh h).elim⟩
  choose ζ hζ using hchoose
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) δ := ⟨le_rfl, hδ.le⟩
  have hζ0 : ζ 0 = a := ((hζ 0 h00).2.2 a (mem_ball_self hr)).mp
    (by simpa only [add_zero] using hz) |>.symm
  refine ⟨δ, hδ, ζ, hζ0, ?_, hζ⟩
  rw [hasDerivWithinAt_iff_tendsto]
  have hsmall : ∀ᶠ h : ℝ in 𝓝 0, |h| < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hh
  have hupper : ∀ᶠ h : ℝ in 𝓝[Ici 0] 0,
      ‖h - 0‖⁻¹ * ‖ζ h - ζ 0 - (h - 0) •
        (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a)‖ ≤ C * h := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h hh hh0
    change 0 ≤ h at hh0
    have hhd : h ∈ Icc (0 : ℝ) δ := ⟨hh0, (le_abs_self h).trans hh.le⟩
    obtain ⟨hzb, _, hzz⟩ := hζ h hhd
    have hdist : ‖ζ h - a‖ ≤ r := by
      simpa only [dist_eq_norm] using (mem_ball.mp hzb).le
    have hzr : ‖ζ h - a‖ ≤ rm := hdist.trans (hrr.trans (min_le_left _ _))
    have hest := hmotion h ⟨hh0, hhd.2.trans (min_le_left _ _)⟩ (ζ h) hzr
      ((hzz (ζ h) hzb).mpr rfl)
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hh0, hζ0, Complex.real_smul]
    rw [show ζ h - a - (h : ℂ) *
        (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a) =
        ζ h - (a + (h : ℂ) *
          (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a)) by ring]
    rcases eq_or_lt_of_le hh0 with he | hp
    · rw [← he]
      simp only [inv_zero, zero_mul, mul_zero, le_refl]
    · rw [inv_mul_le_iff₀ hp]
      nlinarith only [hest]
  apply squeeze_zero' (Eventually.of_forall fun h => by positivity) hupper
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul tendsto_id : Tendsto (fun h : ℝ => C * h) (𝓝 0) (𝓝 (C * 0))).mono_left
      nhdsWithin_le_nhds


#print axioms exists_simple_heat_zero_branch

end
end GaloisForLFunctions.ArithmeticElectrostatics
