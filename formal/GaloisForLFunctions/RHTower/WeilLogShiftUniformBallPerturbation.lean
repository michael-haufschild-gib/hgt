import GaloisForLFunctions.RHTower.WeilLogShiftBoundedOriginGenericity

/-!
# Large moments under uniformly small bounded-history perturbations

Inside every positive-radius closed ball of bounded histories, an arbitrarily
small uniform perturbation can create an arbitrarily large origin moment in
any chosen tail. Two opposite coordinate perturbations cancel the affine
baseline and expose the diverging inverse diagonal.
-/

open Filter Topology Zeta23 Real
open scoped BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

/-- A closed ball of bounded recovery histories, carrying the supremum metric. -/
abbrev WeilLogShiftUniformHistoryBall (center : ℕ →ᵇ ℝ) (r : ℝ) :=
  Metric.closedBall center r

/-- Each affine moment coordinate is continuous for the supremum norm. -/
theorem continuous_weilLogShiftRecoveryMomentBCF (y : ℝ) (n : ℕ) :
    Continuous (fun h : ℕ →ᵇ ℝ => weilLogShiftRecoveryMoment y h n) := by
  have h := (weilLogShiftRecoveryMomentCLM y n).continuous.add
    (continuous_const (y := weilLogShiftRecoveryMoment y (fun _ => 0) n))
  change Continuous (fun h : ℕ →ᵇ ℝ => weilLogShiftRecoveryMomentCLM y n h +
    weilLogShiftRecoveryMoment y (fun _ => 0) n) at h
  simpa only [weilLogShiftRecoveryMomentCLM_apply, sub_add_cancel] using h

/-- Taking a difference removes the affine moment baseline exactly. -/
theorem weilLogShiftRecoveryMoment_sub_eq (y : ℝ) (n : ℕ) (h g : ℕ →ᵇ ℝ) :
    weilLogShiftRecoveryMoment y h n - weilLogShiftRecoveryMoment y g n =
      weilLogShiftRecoveryMomentCLM y n (h - g) := by
  rw [map_sub, weilLogShiftRecoveryMomentCLM_apply, weilLogShiftRecoveryMomentCLM_apply]
  ring

theorem norm_weilLogShiftRecoveryUnitHistory_le (k : ℕ) :
    ‖weilLogShiftRecoveryUnitHistory k‖ ≤ 1 :=
  norm_weilLogShiftBoundedHistoryBCF_le _

private theorem convex_ball_perturbation (center h v : ℕ →ᵇ ℝ) (r δ : ℝ)
    (hh : ‖h - center‖ ≤ r) (hv : ‖v‖ ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ‖((1 - δ) • h + δ • (center + v)) - center‖ ≤ r ∧
      ‖((1 - δ) • h + δ • (center + v)) - h‖ ≤ 2 * δ * r := by
  have hleft : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  constructor
  · calc
      _ = ‖(1 - δ) • (h - center) + δ • v‖ := by congr 1; module
      _ ≤ ‖(1 - δ) • (h - center)‖ + ‖δ • v‖ := norm_add_le _ _
      _ = (1 - δ) * ‖h - center‖ + δ * ‖v‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hδ0]
      _ ≤ (1 - δ) * r + δ * r := add_le_add
        (mul_le_mul_of_nonneg_left hh hleft) (mul_le_mul_of_nonneg_left hv hδ0)
      _ = r := by ring
  · calc
      _ = ‖δ • (center - h + v)‖ := by congr 1; module
      _ = δ * ‖center - h + v‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ0]
      _ ≤ δ * (‖center - h‖ + ‖v‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hδ0
      _ ≤ δ * (r + r) := mul_le_mul_of_nonneg_left
        (add_le_add (by simpa only [norm_sub_rev] using hh) hv) hδ0
      _ = 2 * δ * r := by ring

/-- A diverging coordinate diagonal forces arbitrarily large affine values
inside every relative neighborhood of every positive-radius history ball. -/
theorem exists_weilLogShiftUniformBall_near_large_affine
    (T : ℕ → (ℕ →ᵇ ℝ) →L[ℝ] ℝ) (b : ℕ → ℝ)
    (hdiag : Tendsto (fun k => T (k + 2) (weilLogShiftRecoveryUnitHistory k)) atTop atTop)
    (center : ℕ →ᵇ ℝ) (r : ℝ) (hr : 0 < r)
    (h : WeilLogShiftUniformHistoryBall center r) (B : ℝ) (N : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : WeilLogShiftUniformHistoryBall center r, dist g h < ε ∧
      ∃ n : ℕ, N + 2 ≤ n ∧ B < ‖T n (g : ℕ →ᵇ ℝ) + b n‖ := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_between
    (show 0 < min 1 (ε / (2 * r)) by positivity)
  have hδ1 : δ ≤ 1 := (hδ.trans_le (min_le_left _ _)).le
  have hclose : 2 * δ * r < ε := by
    have h := (lt_div_iff₀ (show 0 < 2 * r by positivity)).mp
      (hδ.trans_le (min_le_right _ _))
    nlinarith only [h]
  have hgrowth := hdiag.const_mul_atTop (mul_pos hδ0 hr)
  obtain ⟨startIndex, hStart⟩ := eventually_atTop.mp (hgrowth.eventually_gt_atTop B)
  let k : ℕ := N + startIndex
  have hlarge : B < (δ * r) * T (k + 2) (weilLogShiftRecoveryUnitHistory k) :=
    hStart k (by dsimp only [k]; omega)
  let v : ℕ →ᵇ ℝ := r • weilLogShiftRecoveryUnitHistory k
  have hv : ‖v‖ ≤ r := by
    calc
      _ = r * ‖weilLogShiftRecoveryUnitHistory k‖ := by
        simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left (norm_weilLogShiftRecoveryUnitHistory_le k) hr.le
      _ = r := mul_one r
  have hh : ‖(h : ℕ →ᵇ ℝ) - center‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using h.property
  let gp : ℕ →ᵇ ℝ := (1 - δ) • (h : ℕ →ᵇ ℝ) + δ • (center + v)
  let gm : ℕ →ᵇ ℝ := (1 - δ) • (h : ℕ →ᵇ ℝ) + δ • (center + -v)
  have hp := convex_ball_perturbation center h v r δ hh hv hδ0.le hδ1
  have hm := convex_ball_perturbation center h (-v) r δ hh
    (by simpa only [norm_neg] using hv) hδ0.le hδ1
  let plus : WeilLogShiftUniformHistoryBall center r :=
    ⟨gp, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp.1⟩
  let minus : WeilLogShiftUniformHistoryBall center r :=
    ⟨gm, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hm.1⟩
  have hdiff : gp - gm = (2 * δ * r) • weilLogShiftRecoveryUnitHistory k := by
    dsimp only [gp, gm, v]
    module
  have hmoment : (T (k + 2) gp + b (k + 2)) - (T (k + 2) gm + b (k + 2)) =
      2 * δ * r * T (k + 2) (weilLogShiftRecoveryUnitHistory k) := by
    calc
      _ = T (k + 2) (gp - gm) := by rw [map_sub]; ring
      _ = _ := by rw [hdiff, map_smul, smul_eq_mul]
  have htriangle : 2 * δ * r * T (k + 2) (weilLogShiftRecoveryUnitHistory k) ≤
      ‖T (k + 2) gp + b (k + 2)‖ + ‖T (k + 2) gm + b (k + 2)‖ := by
    rw [← hmoment]
    have hnorm : (T (k + 2) gp + b (k + 2)) - (T (k + 2) gm + b (k + 2)) ≤
        ‖(T (k + 2) gp + b (k + 2)) - (T (k + 2) gm + b (k + 2))‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self
        ((T (k + 2) gp + b (k + 2)) - (T (k + 2) gm + b (k + 2)))
    exact hnorm.trans (norm_sub_le _ _)
  by_cases hpbig : B < ‖T (k + 2) gp + b (k + 2)‖
  · refine ⟨plus, ?_, k + 2, by dsimp only [k]; omega, hpbig⟩
    change dist gp (h : ℕ →ᵇ ℝ) < ε
    rw [dist_eq_norm]
    exact hp.2.trans_lt hclose
  · have hmbig : B < ‖T (k + 2) gm + b (k + 2)‖ := by
      have hpbound := le_of_not_gt hpbig
      nlinarith only [hlarge, htriangle, hpbound]
    refine ⟨minus, ?_, k + 2, by dsimp only [k]; omega, hmbig⟩
    change dist gm (h : ℕ →ᵇ ℝ) < ε
    rw [dist_eq_norm]
    exact hm.2.trans_lt hclose

/-- Every relative uniform neighborhood in a positive-radius history ball
contains an arbitrarily large absolute origin term after any chosen cutoff. -/
theorem exists_weilLogShiftUniformBall_near_large_origin
    (center : ℕ →ᵇ ℝ) (r : ℝ) (hr : 0 < r)
    (h : WeilLogShiftUniformHistoryBall center r) (B : ℝ) (N : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : WeilLogShiftUniformHistoryBall center r, dist g h < ε ∧
      ∃ n : ℕ, N + 2 ≤ n ∧ B < ‖weilLogShiftRecoveryMoment 0 (g : ℕ →ᵇ ℝ) n‖ := by
  obtain ⟨g, hnear, n, hn, hlarge⟩ := exists_weilLogShiftUniformBall_near_large_affine
    (weilLogShiftRecoveryMomentCLM 0) (weilLogShiftRecoveryMoment 0 (fun _ => 0))
    tendsto_weilLogShiftRecoveryDiagonal_origin_atTop center r hr h B N ε hε
  exact ⟨g, hnear, n, hn, by
    simpa only [weilLogShiftRecoveryMomentCLM_apply, sub_add_cancel] using hlarge⟩

end RHTower
