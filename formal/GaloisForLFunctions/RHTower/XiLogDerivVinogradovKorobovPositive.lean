import GaloisForLFunctions.RHTower.XiLogDerivZeroFreePositive
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovZeroFree

/-!
# Hadamard positivity in the Vinogradov–Korobov region

`RH ⟺ Re (ξ'/ξ)(s) ≥ 0` on `Re s > 1/2`.  With `w(T) = (log T)^{-2/3}(log log T)^{-5/3}/10⁸`,

`Re (ξ'/ξ)(s) ≥ 0`   whenever `|Im s| ≥ T₀` and `Re s ≥ 1 - w(4(|Im s| + 1))/2`

(`exists_re_logDeriv_xi_nonneg_vinogradovKorobov`).

The proof is that of `re_logDeriv_xi_nonneg_of_zeroFree` with the displacement bound of the
Vinogradov–Korobov region, `|β - 1/2| ≤ 1/2 - w(|γ|)` for `|γ| ≥ γ₁`
(`abs_re_sub_half_le_vinogradovKorobov`), in the near regime `|γ| ≤ 4(|Im s|+1)`; zeros below
`γ₁` are finitely constrained by the classical region, and the far regime is unchanged.
-/

namespace RHTower

open Complex

noncomputable section

/-- The Vinogradov–Korobov width `w(T) = (log T)^{-2/3}(log log T)^{-5/3}/10⁸`. -/
def vkHadamardWidth (T : ℝ) : ℝ :=
  Real.log T ^ (-(2 : ℝ) / 3) * Real.log (Real.log T) ^ (-(5 : ℝ) / 3) / 10 ^ 8

theorem vkHadamardWidth_pos {T : ℝ} (hT : Real.exp (Real.exp 1) ≤ T) : 0 < vkHadamardWidth T := by
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have hL : Real.exp 1 ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hT
  have hL0 : 0 < Real.log T := lt_of_lt_of_le (Real.exp_pos _) hL
  have hM : 1 ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hL
  unfold vkHadamardWidth
  have : 0 < Real.log (Real.log T) := by linarith
  positivity

theorem vkHadamardWidth_anti {T T' : ℝ} (hT : Real.exp (Real.exp 1) ≤ T) (hTT' : T ≤ T') :
    vkHadamardWidth T' ≤ vkHadamardWidth T := by
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have hL : Real.exp 1 ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hT
  have hL0 : 0 < Real.log T := lt_of_lt_of_le (Real.exp_pos _) hL
  have hLL' : Real.log T ≤ Real.log T' := Real.log_le_log hT0 hTT'
  have hM : 1 ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hL
  have hMM' : Real.log (Real.log T) ≤ Real.log (Real.log T') := Real.log_le_log hL0 hLL'
  unfold vkHadamardWidth
  have h1 : Real.log T' ^ (-(2 : ℝ) / 3) ≤ Real.log T ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hL0 hLL' (by norm_num)
  have h2 : Real.log (Real.log T') ^ (-(5 : ℝ) / 3) ≤ Real.log (Real.log T) ^ (-(5 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hMM' (by norm_num)
  have h0 : 0 ≤ Real.log (Real.log T') ^ (-(5 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  have h0' : 0 ≤ Real.log T ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hL0.le _
  gcongr

/-- `w(T) ≤ ε` for `log T ≥ max(e, (10⁸ ε)^{-3/2})`. -/
theorem vkHadamardWidth_le {T ε : ℝ} (hε : 0 < ε)
    (hT : Real.exp (max (Real.exp 1) ((10 ^ 8 * ε) ^ (-(3 : ℝ) / 2))) ≤ T) :
    vkHadamardWidth T ≤ ε := by
  have hE := Real.exp_pos (max (Real.exp 1) ((10 ^ 8 * ε) ^ (-(3 : ℝ) / 2)))
  have hT0 : 0 < T := lt_of_lt_of_le hE hT
  have hLmax : max (Real.exp 1) ((10 ^ 8 * ε) ^ (-(3 : ℝ) / 2)) ≤ Real.log T := by
    rw [← Real.log_exp (max (Real.exp 1) ((10 ^ 8 * ε) ^ (-(3 : ℝ) / 2)))]
    exact Real.log_le_log hE hT
  have hL : Real.exp 1 ≤ Real.log T := le_trans (le_max_left _ _) hLmax
  have hL2 : (10 ^ 8 * ε) ^ (-(3 : ℝ) / 2) ≤ Real.log T := le_trans (le_max_right _ _) hLmax
  have hL0 : 0 < Real.log T := lt_of_lt_of_le (Real.exp_pos _) hL
  have hM : 1 ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hL
  have h1 : Real.log (Real.log T) ^ (-(5 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hM (by norm_num)
  have hε8 : 0 < 10 ^ 8 * ε := by positivity
  have h2 : Real.log T ^ (-(2 : ℝ) / 3) ≤ 10 ^ 8 * ε := by
    calc Real.log T ^ (-(2 : ℝ) / 3) ≤ ((10 ^ 8 * ε) ^ (-(3 : ℝ) / 2)) ^ (-(2 : ℝ) / 3) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hε8 _) hL2 (by norm_num)
      _ = 10 ^ 8 * ε := by rw [← Real.rpow_mul hε8.le]; norm_num
  unfold vkHadamardWidth
  have h0 : 0 ≤ Real.log T ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hL0.le _
  calc Real.log T ^ (-(2 : ℝ) / 3) * Real.log (Real.log T) ^ (-(5 : ℝ) / 3) / 10 ^ 8
      ≤ Real.log T ^ (-(2 : ℝ) / 3) * 1 / 10 ^ 8 := by gcongr
    _ ≤ 10 ^ 8 * ε * 1 / 10 ^ 8 := by gcongr
    _ = ε := by ring

/-- The Vinogradov–Korobov region in displacement form. -/
theorem abs_re_sub_half_le_vinogradovKorobov :
    ∃ γ₁ : ℝ, Real.exp (Real.exp 1) ≤ γ₁ ∧ ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 →
      γ₁ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ 1 / 2 - vkHadamardWidth |ρ.im| := by
  obtain ⟨γ₀, hγ₀⟩ := Sieve.riemannZeta_ne_zero_vinogradovKorobov
  refine ⟨max γ₀ (Real.exp (Real.exp 1)), le_max_right _ _, ?_⟩
  intro ρ hρ0 hρ1 hz hγ
  set g := |ρ.im| with hg
  have hgγ₀ : γ₀ ≤ g := le_trans (le_max_left _ _) hγ
  -- the zero `ρ.re + i g`
  have hz1 : riemannZeta ((ρ.re : ℂ) + (g : ℂ) * Complex.I) = 0 := by
    rcases le_or_gt 0 ρ.im with h | h
    · have : (ρ.re : ℂ) + (g : ℂ) * Complex.I = ρ := by
        rw [hg, abs_of_nonneg h]; exact Complex.re_add_im ρ
      rw [this]; exact hz
    · have : (ρ.re : ℂ) + (g : ℂ) * Complex.I = (starRingEnd ℂ) ρ := by
        rw [hg, abs_of_neg h]; apply Complex.ext <;> simp
      rw [this, riemannZeta_conj, hz, map_zero]
  -- the zero `1 - ρ.re + i g`
  have hz2 : riemannZeta (((1 - ρ.re : ℝ) : ℂ) + (g : ℂ) * Complex.I) = 0 := by
    have hzr : riemannZeta (1 - ρ) = 0 := by
      have hne : ρ ≠ 1 := by intro h; rw [h] at hρ1; simp at hρ1
      have hxi : xi ρ = 0 := (xi_eq_zero_iff hρ0 hne).mpr hz
      have hxi' : xi (1 - ρ) = 0 := by rw [xi_one_sub]; exact hxi
      have h0 : 0 < (1 - ρ).re := by simp; linarith
      have hne' : 1 - ρ ≠ 1 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      exact (xi_eq_zero_iff h0 hne').mp hxi'
    rcases le_or_gt 0 ρ.im with h | h
    · have : ((1 - ρ.re : ℝ) : ℂ) + (g : ℂ) * Complex.I = (starRingEnd ℂ) (1 - ρ) := by
        rw [hg, abs_of_nonneg h]; apply Complex.ext <;> simp
      rw [this, riemannZeta_conj, hzr, map_zero]
    · have : ((1 - ρ.re : ℝ) : ℂ) + (g : ℂ) * Complex.I = 1 - ρ := by
        rw [hg, abs_of_neg h]; apply Complex.ext <;> simp
      rw [this]; exact hzr
  have hb1 : ρ.re ≤ 1 - vkHadamardWidth g := by
    by_contra hc; push Not at hc
    exact hγ₀ ρ.re g hgγ₀ (by unfold vkHadamardWidth at hc; linarith) hz1
  have hb2 : 1 - ρ.re ≤ 1 - vkHadamardWidth g := by
    by_contra hc; push Not at hc
    exact hγ₀ (1 - ρ.re) g hgγ₀ (by unfold vkHadamardWidth at hc; linarith) hz2
  rw [abs_le]; constructor <;> linarith

/-- **`Re (ξ'/ξ) ≥ 0` in the Vinogradov–Korobov region.** -/
theorem exists_re_logDeriv_xi_nonneg_vinogradovKorobov :
    ∃ T₀ : ℝ, ∀ s : ℂ, T₀ ≤ |s.im| → 1 - vkHadamardWidth (4 * (|s.im| + 1)) / 2 ≤ s.re →
      0 ≤ (logDeriv xi s).re := by
  obtain ⟨γ₁, hγ₁e, hdisp⟩ := abs_re_sub_half_le_vinogradovKorobov
  have hγ₁0 : 0 < γ₁ := lt_of_lt_of_le (Real.exp_pos _) hγ₁e
  have hlogγ₁ : 1 < Real.log γ₁ := by
    have : Real.exp 1 ≤ Real.log γ₁ := by
      rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hγ₁e
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  set c₀ : ℝ := 1 / 58 / Real.log γ₁ with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  set ε : ℝ := min (1 / 2) c₀ with hε
  have hε0 : 0 < ε := lt_min (by norm_num) hc₀0
  refine ⟨max γ₁ (Real.exp (max (Real.exp 1) ((10 ^ 8 * ε) ^ (-(3 : ℝ) / 2)))), ?_⟩
  intro s hs hre
  set t := s.im with ht
  set T := 4 * (|t| + 1) with hT
  have htγ₁ : γ₁ ≤ |t| := le_trans (le_max_left _ _) hs
  have hTbig : Real.exp (max (Real.exp 1) ((10 ^ 8 * ε) ^ (-(3 : ℝ) / 2))) ≤ T := by
    have := le_trans (le_max_right _ _) hs
    rw [hT]; linarith [abs_nonneg t]
  have hTe : Real.exp (Real.exp 1) ≤ T := by
    have : Real.exp (Real.exp 1) ≤ Real.exp (max (Real.exp 1) ((10 ^ 8 * ε) ^ (-(3 : ℝ) / 2))) :=
      Real.exp_le_exp.mpr (le_max_left _ _)
    linarith
  have hwT := vkHadamardWidth_le hε0 hTbig
  have hwT0 := vkHadamardWidth_pos hTe
  have hw12 : vkHadamardWidth T ≤ 1 / 2 := hwT.trans (min_le_left _ _)
  have hwc₀ : vkHadamardWidth T ≤ c₀ := hwT.trans (min_le_right _ _)
  have hxpos : 0 < s.re - 1 / 2 := by linarith
  have hx4 : (1 : ℝ) / 4 ≤ s.re - 1 / 2 := by linarith
  -- `ξ(s) ≠ 0`
  have hsne : xi s ≠ 0 := by
    intro hzero
    rcases le_or_gt 1 s.re with hge | hlt
    · exact xi_ne_zero_of_one_le_re hge hzero
    · have h0 : 0 < s.re := by linarith
      have hne1 : s ≠ 1 := by intro h; rw [h] at hlt; simp at hlt
      have hz : riemannZeta s = 0 := (xi_eq_zero_iff h0 hne1).mp hzero
      have hd := hdisp s h0 hlt hz htγ₁
      have hte : Real.exp (Real.exp 1) ≤ |t| := le_trans hγ₁e htγ₁
      have hanti := vkHadamardWidth_anti hte (show |t| ≤ T by rw [hT]; linarith [abs_nonneg t])
      have hwt0 := vkHadamardWidth_pos hte
      rw [abs_le] at hd
      linarith [hd.2]
  -- every paired term is nonnegative
  have hterm : ∀ q : XiZeroCopy, 0 ≤ xiPairedResolventTerm s q := by
    intro q
    obtain ⟨hb0, hb1⟩ := xi_divisor_support_re_mem_open_unit q.1
    have hxiq : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
    have hA : (0 : ℝ) < normSq (s - (q.1 : ℂ)) := by
      refine Complex.normSq_pos.mpr (sub_ne_zero.mpr ?_)
      intro h; rw [h] at hsne; exact hsne hxiq
    have hB : (0 : ℝ) < normSq (s - (1 - (q.1 : ℂ))) := by
      refine Complex.normSq_pos.mpr (sub_ne_zero.mpr ?_)
      intro h; rw [h] at hsne; exact hsne (by rw [xi_one_sub]; exact hxiq)
    refine xiPairedResolventTerm_nonneg_of_numerator hA hB ?_
    have habs : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    rcases le_or_gt (1 / 2 : ℝ) (s.re - 1 / 2) with hbig | hlt
    · exact pairedNumerator_nonneg_near hxpos (le_trans habs hbig)
    rcases le_or_gt |(q.1 : ℂ).im| T with hnear | hfar
    · refine pairedNumerator_nonneg_near hxpos ?_
      have hz := riemannZeta_eq_zero_of_xiZeroCopy q
      rcases le_or_gt γ₁ |(q.1 : ℂ).im| with hhigh | hlow
      · have hd := hdisp (q.1 : ℂ) hb0 hb1 hz hhigh
        have hqe : Real.exp (Real.exp 1) ≤ |(q.1 : ℂ).im| := le_trans hγ₁e hhigh
        have hanti := vkHadamardWidth_anti hqe hnear
        linarith
      · have hzf := abs_re_sub_half_le_of_xiZeroCopy q
        have hglog := one_lt_log_abs_im_of_xiZeroCopy q
        have hgpos : 0 < |(q.1 : ℂ).im| := by
          have := four_le_abs_im_of_zeta_zero hb0 hb1 hz; linarith
        have hlogle : Real.log |(q.1 : ℂ).im| ≤ Real.log γ₁ := Real.log_le_log hgpos hlow.le
        have hcmp : c₀ ≤ 1 / 58 / Real.log |(q.1 : ℂ).im| := by
          rw [hc₀, div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
    · refine pairedNumerator_nonneg_far hx4 (le_of_lt hlt) habs ?_
      rw [hT] at hfar
      exact hfar.le
  have htwice := two_mul_re_logDeriv_xi_eq_tsum_paired hsne
  have hsum : 0 ≤ ∑' q : XiZeroCopy, xiPairedResolventTerm s q := tsum_nonneg hterm
  linarith

end

end RHTower
