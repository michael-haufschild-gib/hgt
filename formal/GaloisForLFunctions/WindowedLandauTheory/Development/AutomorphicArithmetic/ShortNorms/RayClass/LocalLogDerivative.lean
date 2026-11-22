import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.RightLogDerivative
import Zeta23.WeilEF.Landau

/-! Jensen's estimate for the ray class family, with a fixed disk at each height. -/

open Complex Metric Finset

noncomputable section

namespace GlobalTheory.HkLocal

open GlobalTheory.Hk

theorem logDeriv_local :
    ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (t : ℝ),
      {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}.Finite ∧
      (∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0},
        (analyticOrderNatAt (𝓕.F χ) w : ℝ)) ≤ C * 𝓕.ell t ∧
      ∀ s : ℂ, ‖s - (5 / 4 + t * I)‖ ≤ 1 / 2 → 𝓕.F χ s ≠ 0 →
        ‖deriv (𝓕.F χ) s / 𝓕.F χ s -
          ∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0},
            (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ ≤ C * 𝓕.ell t := by
  classical
  let r : ℝ := 7 / 10
  let J : ℝ := 1 / Real.log ((24 / 25 : ℝ) / (22 / 25))
  let D : ℝ := 44795000 / r
  have hJ : 0 < J := one_div_pos.mpr (Real.log_pos (by norm_num))
  have hD : 0 < D := by dsimp [D, r]; positivity
  refine ⟨7 * (D + 11 * J), by positivity, ?_⟩
  intro 𝓕 χ t
  obtain ⟨han, hLS, hgrowth, -⟩ := RayCont.continuation_growth 𝓕 χ
  let z₀ : ℂ := 5 / 4 + t * I
  have hzre : z₀.re = 5 / 4 := by simp [z₀]
  have hzone : 1 < z₀.re := by rw [hzre]; norm_num
  have hnorm : ‖z₀‖ ≤ 5 / 4 + |t| := by
    exact (norm_add_le _ _).trans_eq (by simp [z₀, norm_mul, Real.norm_eq_abs])
  have hF₀ : 𝓕.F χ z₀ ≠ 0 := (LogDeriv.logDeriv_F 𝓕 χ z₀ hzone).2.2.1
  have hlow : (1 / 100 : ℝ) ≤ ‖𝓕.F χ z₀‖ := by
    have hL := (LogDeriv.logDeriv_F 𝓕 χ z₀ hzone).2.1
    rw [hzre] at hL
    have hP : (1 / 4 : ℝ) ≤ ‖if χ = 1 then z₀ - 1 else 1‖ := by
      split_ifs
      · have h := (le_abs_self (z₀ - 1).re).trans (Complex.abs_re_le_norm _)
        rw [sub_re, hzre, one_re] at h
        linarith only [h]
      · norm_num
    rw [(hLS z₀ hzone).2, norm_mul]
    calc (1 / 100 : ℝ) = (1 / 4) * ((5 / 4 - 1) / (5 / 4)) ^ 2 := by norm_num
      _ ≤ _ := mul_le_mul hP hL (by norm_num) (norm_nonneg _)
  have hre (w : ℂ) (hw : w ∈ closedBall z₀ r) : 11 / 20 ≤ w.re := by
    rw [mem_closedBall, Complex.dist_eq] at hw
    have h := (abs_le.mp ((Complex.abs_re_le_norm (w - z₀)).trans hw)).1
    rw [sub_re, hzre] at h
    dsimp [r] at h
    linarith only [h]
  have hAnalytic : AnalyticOnNhd ℂ (𝓕.F χ) (closedBall z₀ r) := fun w hw =>
    han w (by have := hre w hw; linarith)
  let X : ℝ := 𝓕.B * (|t| + 2)
  have hB := 𝓕.B_ge
  have hX8 : 8 ≤ X := by
    calc (8 : ℝ) = 4 * 2 := by norm_num
      _ ≤ X := mul_le_mul hB (show (2 : ℝ) ≤ |t| + 2 by positivity)
        (by norm_num) (by linarith : 0 ≤ 𝓕.B)
  have hX0 : 0 ≤ X := by linarith
  have hX7 : 2 ≤ X ^ 7 := (by norm_num : (2 : ℝ) ≤ 8 ^ 7).trans
    (pow_le_pow_left₀ (by norm_num) hX8 7)
  have hG (w : ℂ) (hw : w ∈ closedBall z₀ (24 / 25 * r)) : ‖𝓕.F χ w‖ ≤ X ^ 7 * ‖𝓕.F χ z₀‖ := by
    have hw' : w ∈ closedBall z₀ r := closedBall_subset_closedBall (by norm_num [r]) hw
    have hwNorm : ‖w‖ + 1 ≤ |t| + 3 := by
      rw [mem_closedBall, Complex.dist_eq] at hw'
      have h := norm_add_le (w - z₀) z₀
      rw [sub_add_cancel] at h
      dsimp [r] at hw'
      linarith only [hw', h, hnorm]
    have hScale : 300 * 𝓕.B * (|t| + 3) ^ 2 ≤ 16875 / 100 * X ^ 2 := by
      have ht : |t| + 3 ≤ (3 / 2 : ℝ) * (|t| + 2) := by linarith [abs_nonneg t]
      have ht2 := pow_le_pow_left₀ (show 0 ≤ |t| + 3 by positivity) ht 2
      have h4 := mul_le_mul_of_nonneg_right hB (by positivity : 0 ≤ 𝓕.B * (|t| + 2) ^ 2)
      have h2 := mul_le_mul_of_nonneg_left ht2 (by positivity : 0 ≤ 300 * 𝓕.B)
      dsimp [X]
      nlinarith only [h2, h4]
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hX8 5
    calc ‖𝓕.F χ w‖ ≤ 300 * 𝓕.B * (‖w‖ + 1) ^ 2 := hgrowth w (hre w hw')
      _ ≤ 300 * 𝓕.B * (|t| + 3) ^ 2 := by gcongr
      _ ≤ 16875 / 100 * X ^ 2 := hScale
      _ ≤ (8 ^ 5 / 100) * X ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg X)
      _ ≤ X ^ 7 * ‖𝓕.F χ z₀‖ := by
        rw [show (7 : ℕ) = 5 + 2 by rfl, pow_add]
        calc (8 ^ 5 / 100) * X ^ 2 = 8 ^ 5 * X ^ 2 * (1 / 100) := by ring
          _ ≤ _ := by gcongr
  obtain ⟨W, hW, hmass, hest⟩ := Zeta23.WeilEF.logDeriv_partial_fraction_disk
    (show 0 < r by norm_num [r]) hAnalytic hF₀ hX7 hG
  let S : Set ℂ := {w | ‖w - z₀‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}
  have hsub : S ⊆ (W : Set ℂ) := by
    intro w hw
    rw [hW, Set.mem_setOf_eq, mem_closedBall, Complex.dist_eq]
    exact ⟨hw.1.trans (by norm_num [r]), hw.2⟩
  have hf : S.Finite := W.finite_toSet.subset hsub
  let Z := hf.toFinset
  have hZW : Z ⊆ W := fun w hw => hsub (hf.mem_toFinset.mp hw)
  have hell : 0 ≤ 𝓕.ell t := (𝓕.two_lt_ell t).le.trans' (by norm_num)
  have hlog : Real.log (X ^ 7) = 7 * 𝓕.ell t := by
    rw [Real.log_pow]
    rfl
  have hmass' : (∑ w ∈ W, (analyticOrderNatAt (𝓕.F χ) w : ℝ)) ≤ J * (7 * 𝓕.ell t) := by
    simpa only [J, hlog] using hmass
  refine ⟨hf, ?_, fun s hs hFs => ?_⟩
  · change (∑ᶠ w ∈ S, (analyticOrderNatAt (𝓕.F χ) w : ℝ)) ≤ _
    rw [finsum_mem_eq_finite_toFinset_sum _ hf]
    have h := sum_le_sum_of_subset_of_nonneg hZW
      (fun w _ _ => Nat.cast_nonneg (α := ℝ) (analyticOrderNatAt (𝓕.F χ) w))
    nlinarith only [h, hmass', mul_nonneg hD.le hell, mul_nonneg hJ.le hell]
  · have hs' : s ∈ closedBall z₀ (83 / 100 * r) := by
      rw [mem_closedBall, Complex.dist_eq]
      exact hs.trans (by norm_num [r])
    let f (w : ℂ) := (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)
    have htail : ‖∑ w ∈ W \ Z, f w‖ ≤ 10 * (J * (7 * 𝓕.ell t)) := by
      calc ‖∑ w ∈ W \ Z, f w‖ ≤ ∑ w ∈ W \ Z, ‖f w‖ := norm_sum_le _ _
        _ ≤ ∑ w ∈ W \ Z, 10 * (analyticOrderNatAt (𝓕.F χ) w : ℝ) := by
          apply sum_le_sum
          intro w hw
          obtain ⟨hwW, hwZ⟩ := mem_sdiff.mp hw
          have hw0 : 𝓕.F χ w = 0 := by
            have hw : w ∈ (W : Set ℂ) := hwW
            rw [hW] at hw
            exact hw.2
          have hd : 3 / 5 < ‖w - z₀‖ := lt_of_not_ge fun h =>
            hwZ (hf.mem_toFinset.mpr ⟨h, hw0⟩)
          have htri := norm_add_le (w - s) (s - z₀)
          rw [sub_add_sub_cancel, norm_sub_rev w s] at htri
          have hdist : 1 / 10 ≤ ‖s - w‖ := by linarith only [htri, hd, hs]
          rw [f, norm_div, Complex.norm_natCast]
          calc _ ≤ (analyticOrderNatAt (𝓕.F χ) w : ℝ) / (1 / 10) :=
                div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hdist
            _ = _ := by ring
        _ ≤ _ := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left
            ((sum_le_sum_of_subset_of_nonneg sdiff_subset (fun w _ _ => Nat.cast_nonneg _)).trans hmass')
            (by norm_num)
    change ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ᶠ w ∈ S, f w‖ ≤ _
    rw [finsum_mem_eq_finite_toFinset_sum _ hf]
    have he : logDeriv (𝓕.F χ) s - ∑ w ∈ Z, f w =
        (logDeriv (𝓕.F χ) s - ∑ w ∈ W, f w) + ∑ w ∈ W \ Z, f w := by
      have hsum : (∑ w ∈ W \ Z, f w) + ∑ w ∈ Z, f w = ∑ w ∈ W, f w := sum_sdiff hZW
      rw [← hsum]
      ring
    rw [← logDeriv_apply, he]
    have hb := hest s hs' hFs
    rw [hlog] at hb
    refine (norm_add_le _ _).trans ((add_le_add hb htail).trans ?_)
    change D * (7 * 𝓕.ell t) + _ ≤ _
    nlinarith only [mul_nonneg hJ.le hell]

end GlobalTheory.HkLocal
