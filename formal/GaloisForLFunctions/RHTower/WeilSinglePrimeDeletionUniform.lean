import GaloisForLFunctions.RHTower.WeilSinglePrimeDeletion

/-!
# Every large prime is load-bearing for Weil positivity

The single-prime deletion argument of `WeilSinglePrimeDeletion` is made uniform: for every prime
`p ≥ e^{18}`, deleting `p` from the prime side of Weil's explicit formula produces a functional that
is negative on the autocorrelation of an explicit real `C²` test.  The test is the two-bump
`f = φ(·−u₀/2) − φ(·+u₀/2)` with `u₀ = log p` and `φ` a smoothed uniform convolution power whose
order `n ≈ 0.64·u₀` grows with `p`, so that the Fourier decay `(1081/780)^{2(n+1)}(2/41)^{n}` beats
the factor `p` coming from the off-line strip `|Im γ_ρ| ≤ ½`:

  `p·(1081/780)^{2n+2}·(2/41)^n ≤ exp(u₀ + (33/100)(2n+2) − 3n) ≤ 1`.
-/

open Complex MeasureTheory Set
open scoped Convolution

namespace RHTower.WeilDeletion

noncomputable section

/-! ## Numerical facts -/

theorem rat_le_exp_third : (1081 / 780 : ℝ) ≤ Real.exp (33 / 100) := by
  have h := Real.exp_bound (x := 33 / 100) (by norm_num) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  rw [abs_le] at h
  linarith [h.1]

theorem exp_three_le : Real.exp 3 ≤ 41 / 2 := by
  have h := Real.exp_one_lt_d9
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
  calc Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := by gcongr
    _ ≤ 41 / 2 := by norm_num

theorem two_div_fortyOne_le_exp : (2 / 41 : ℝ) ≤ Real.exp (-3) := by
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  have := exp_three_le
  calc Real.exp 3 ≤ 41 / 2 := this
    _ = (2 / 41 : ℝ)⁻¹ := by norm_num

/-! ## The scaled test -/

/-- The bump with `n+1` uniform factors. -/
def phiN (n : ℕ) : ℝ → ℝ := phi (2 / 5) (by norm_num) (39 / 50) n

/-- Half-width of the support of `phiN n`. -/
def sN (n : ℕ) : ℝ := 2 / 5 + ((n : ℝ) + 1) * (39 / 50)

theorem sN_pos (n : ℕ) : 0 < sN n := by unfold sN; positivity

theorem phiN_contDiff (n : ℕ) : ContDiff ℝ 2 (phiN n) := phi_contDiff _ _ _

theorem phiN_hasCompactSupport (n : ℕ) : HasCompactSupport (phiN n) := phi_hasCompactSupport _ _ _

theorem phiN_nonneg (n : ℕ) (x : ℝ) : 0 ≤ phiN n x := phi_nonneg _ (by norm_num) _ x

theorem integrable_phiN (n : ℕ) : Integrable (phiN n) := integrable_phi _ _ _

theorem integral_phiN (n : ℕ) : ∫ x, phiN n x = 1 := integral_phi _ (by norm_num) _

theorem support_phiN_subset (n : ℕ) : Function.support (phiN n) ⊆ Icc (-sN n) (sN n) :=
  support_phi_subset (r := 2 / 5) (by norm_num) (w := 39 / 50) (by norm_num) n

theorem integrable_phiN_sq (n : ℕ) : Integrable (fun x => phiN n x ^ 2) := by
  have hc : Continuous (fun x => phiN n x ^ 2) := (phiN_contDiff n).continuous.pow 2
  have hcs : HasCompactSupport (fun x => phiN n x ^ 2) := by
    have h := (phiN_hasCompactSupport n).mul_right (f' := phiN n)
    have e : (phiN n * phiN n) = fun x => phiN n x ^ 2 := by
      funext x
      simp [sq]
    rw [← e]
    exact h
  exact hc.integrable_of_hasCompactSupport hcs

theorem integral_phiN_sq_ge (n : ℕ) : 1 / (2 * sN n) ≤ ∫ x, phiN n x ^ 2 :=
  integral_sq_ge_of_support (sN_pos n) (phiN_nonneg n) (support_phiN_subset n)
    (integrable_phiN n) (integral_phiN n) (integrable_phiN_sq n)

/-- The Fourier bound of `phiN n` on the strip `|Im z| ≤ 1/2`. -/
theorem norm_paperFT_phiN_le (n : ℕ) {z : ℂ} (hz : z ≠ 0) (him : |z.im| ≤ 1 / 2) :
    ‖Zeta23.paperFT (fun x => (phiN n x : ℂ)) z‖ ≤
      Real.exp (1 / 5) * ((1081 / 780) / ‖z‖) ^ (n + 1) := by
  have h := norm_paperFT_phi_le (r := 2 / 5) (by norm_num) (w := 39 / 50) (by norm_num) n hz
  refine h.trans ?_
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hcosh : Real.cosh (39 / 50 * z.im) ≤ 1081 / 1000 := by
    refine le_trans ?_ cosh_le_bound
    rw [Real.cosh_le_cosh]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 39 / 50)]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 39 / 100)]
    nlinarith [him, abs_nonneg z.im]
  have hexp : Real.exp (2 / 5 * |z.im|) ≤ Real.exp (1 / 5) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hfac : Real.cosh (39 / 50 * z.im) / (39 / 50 * ‖z‖) ≤ (1081 / 780) / ‖z‖ := by
    rw [div_le_div_iff₀ (by positivity) hz0]
    have : (1081 / 780 : ℝ) * (39 / 50) = 1081 / 1000 := by norm_num
    nlinarith [hcosh, hz0]
  gcongr

/-! ## The uniform statement, in pieces -/

/-- The parameters: `N = ⌊(u₀ − 4/5)/(39/25)⌋`, `n = N − 2`; the support fits and the exponent
inequality holds once `u₀ ≥ 18`. -/
theorem params_ok {u₀ : ℝ} (hu18 : 18 ≤ u₀) :
    2 * sN (⌊(u₀ - 4 / 5) / (39 / 25)⌋₊ - 2) < u₀ ∧
    u₀ + (33 / 100) * (2 * ((⌊(u₀ - 4 / 5) / (39 / 25)⌋₊ - 2 : ℕ) : ℝ) + 2) -
      3 * ((⌊(u₀ - 4 / 5) / (39 / 25)⌋₊ - 2 : ℕ) : ℝ) ≤ 0 := by
  set N : ℕ := ⌊(u₀ - 4 / 5) / (39 / 25)⌋₊ with hN
  have hpos : 0 ≤ (u₀ - 4 / 5) / (39 / 25) := by
    apply div_nonneg <;> linarith
  have hNle : (N : ℝ) * (39 / 25) ≤ u₀ - 4 / 5 := by
    have := Nat.floor_le hpos
    rw [← hN, le_div_iff₀ (by norm_num)] at this
    linarith
  have hNgt : u₀ - 4 / 5 < ((N : ℝ) + 1) * (39 / 25) := by
    have := Nat.lt_floor_add_one ((u₀ - 4 / 5) / (39 / 25))
    rw [← hN, div_lt_iff₀ (by norm_num)] at this
    linarith
  have hN11 : 11 ≤ N := by
    rw [hN]
    apply Nat.le_floor
    rw [le_div_iff₀ (by norm_num)]
    push_cast
    linarith
  have hnR : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hN11R : (11 : ℝ) ≤ N := by exact_mod_cast hN11
  refine ⟨?_, ?_⟩
  · unfold sN
    rw [hnR]
    linarith
  · rw [hnR]
    linarith

/-- The per-zero majorant of `k̂(γ)` for the scaled two-bump autocorrelation. -/
theorem norm_paperFT_autocorr_twoBump_le (n : ℕ) {u₀ p : ℝ} (hu0 : 0 ≤ u₀)
    (hexp_half : Real.exp (u₀ / 2) = Real.sqrt p) {γ : ℂ} (hγ0 : γ ≠ 0)
    (hγim : |γ.im| ≤ 1 / 2) (hγsq : (41 / 2 : ℝ) < ‖γ‖ ^ 2) :
    ‖Zeta23.paperFT (fun x => (autocorr (twoBump (phiN n) u₀) x : ℂ)) γ‖ ≤
      (4 * Real.sqrt p * (3 / 2) * ((1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n)) *
        (1 / ‖γ‖ ^ 2) := by
  have hsupp := support_phiN_subset n
  have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hγ0
  set f := twoBump (phiN n) u₀ with hf
  have hkFT : Zeta23.paperFT (fun x => (autocorr f x : ℂ)) γ =
      Zeta23.paperFT (fun x => (f x : ℂ)) γ * Zeta23.paperFT (fun x => (f x : ℂ)) (-γ) :=
    paperFT_autocorr (twoBump_integrable (phiN_contDiff n) hsupp hu0)
      (support_twoBump_subset hsupp hu0) γ
  rw [hkFT, norm_mul]
  have hΦ : ∀ z : ℂ, z ≠ 0 → |z.im| ≤ 1 / 2 →
      ‖Zeta23.paperFT (fun x => (f x : ℂ)) z‖ ≤
        (Real.exp (1 / 5) * ((1081 / 780) / ‖z‖) ^ (n + 1)) * (2 * Real.cosh (u₀ / 2 * z.im)) := by
    intro z hz hzim
    refine (norm_paperFT_twoBump_le (integrable_phiN n) hsupp u₀ z).trans ?_
    gcongr
    exact norm_paperFT_phiN_le n hz hzim
  have hγ' : -γ ≠ 0 := neg_ne_zero.mpr hγ0
  have hγim' : |(-γ).im| ≤ 1 / 2 := by rw [Complex.neg_im, abs_neg]; exact hγim
  have hcosh : ∀ t : ℝ, |t| ≤ 1 / 2 → 2 * Real.cosh (u₀ / 2 * t) ≤ 2 * Real.exp (u₀ / 4) := by
    intro t ht
    have := cosh_le_exp_abs (u₀ / 2 * t)
    have h2 : Real.exp |u₀ / 2 * t| ≤ Real.exp (u₀ / 4) := by
      apply Real.exp_le_exp.mpr
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u₀ / 2)]
      nlinarith [ht, abs_nonneg t]
    linarith
  have hA := hΦ γ hγ0 hγim
  have hB := hΦ (-γ) hγ' hγim'
  rw [norm_neg] at hB
  have hc1 := hcosh γ.im hγim
  have hc2 := hcosh (-γ).im hγim'
  set E := Real.exp (1 / 5) * ((1081 / 780) / ‖γ‖) ^ (n + 1) with hE
  have hEnn : 0 ≤ E := by positivity
  have hstep1 : ‖Zeta23.paperFT (fun x => (f x : ℂ)) γ‖ *
      ‖Zeta23.paperFT (fun x => (f x : ℂ)) (-γ)‖ ≤
      (E * (2 * Real.exp (u₀ / 4))) * (E * (2 * Real.exp (u₀ / 4))) := by
    calc ‖Zeta23.paperFT (fun x => (f x : ℂ)) γ‖ * ‖Zeta23.paperFT (fun x => (f x : ℂ)) (-γ)‖
        ≤ (E * (2 * Real.cosh (u₀ / 2 * γ.im))) * (E * (2 * Real.cosh (u₀ / 2 * (-γ).im))) :=
          mul_le_mul hA hB (norm_nonneg _) (by positivity)
      _ ≤ (E * (2 * Real.exp (u₀ / 4))) * (E * (2 * Real.exp (u₀ / 4))) := by
          gcongr
  have hexp2 : Real.exp (1 / 5) * Real.exp (1 / 5) = Real.exp (2 / 5) := by
    rw [← Real.exp_add]; norm_num
  have hexp4 : Real.exp (u₀ / 4) * Real.exp (u₀ / 4) = Real.sqrt p := by
    rw [← Real.exp_add, ← hexp_half]; congr 1; ring
  have hpow : ((1081 / 780 : ℝ) / ‖γ‖) ^ (n + 1) * ((1081 / 780 : ℝ) / ‖γ‖) ^ (n + 1) =
      (1081 / 780 : ℝ) ^ (2 * (n + 1)) * (1 / ‖γ‖ ^ (2 * (n + 1))) := by
    rw [← pow_add, div_pow, mul_one_div]
    congr 2 <;> ring
  have hnorm : 1 / ‖γ‖ ^ (2 * (n + 1)) ≤ (2 / 41) ^ n * (1 / ‖γ‖ ^ 2) := by
    have h : ‖γ‖ ^ (2 * (n + 1)) = ‖γ‖ ^ 2 * (‖γ‖ ^ 2) ^ n := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    rw [h, one_div, mul_inv, ← one_div, ← one_div, mul_comm]
    gcongr
    rw [div_le_iff₀ (by positivity)]
    rw [show (2 / 41 : ℝ) ^ n * (‖γ‖ ^ 2) ^ n = ((2 / 41) * ‖γ‖ ^ 2) ^ n by rw [mul_pow]]
    have : (1 : ℝ) ≤ (2 / 41) * ‖γ‖ ^ 2 := by nlinarith
    exact one_le_pow₀ this
  have hstep2 : (E * (2 * Real.exp (u₀ / 4))) * (E * (2 * Real.exp (u₀ / 4))) =
      4 * Real.sqrt p * Real.exp (2 / 5) *
        ((1081 / 780) ^ (2 * (n + 1)) * (1 / ‖γ‖ ^ (2 * (n + 1)))) := by
    rw [hE, ← hexp2, ← hexp4, ← hpow]
    ring
  have hstep3 : 4 * Real.sqrt p * Real.exp (2 / 5) *
      ((1081 / 780) ^ (2 * (n + 1)) * (1 / ‖γ‖ ^ (2 * (n + 1)))) ≤
      4 * Real.sqrt p * (3 / 2) * ((1081 / 780) ^ (2 * (n + 1)) * ((2 / 41) ^ n * (1 / ‖γ‖ ^ 2))) := by
    gcongr
    exact exp_two_fifths_le
  calc ‖Zeta23.paperFT (fun x => (f x : ℂ)) γ‖ * ‖Zeta23.paperFT (fun x => (f x : ℂ)) (-γ)‖
      ≤ _ := hstep1
    _ = _ := hstep2
    _ ≤ _ := hstep3
    _ = (4 * Real.sqrt p * (3 / 2) * ((1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n)) *
        (1 / ‖γ‖ ^ 2) := by ring

/-- The real part of the zero side is at most `C·(33/100)` whenever every term is dominated by
`C/‖γ_ρ‖²`. -/
theorem re_literatureRHS_le {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {C : ℝ} (hC : 0 ≤ C)
    (hterm : ∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ →
      ‖Zeta23.paperFT k (Zeta23.gammaOf ρ)‖ ≤ C * (1 / ‖Zeta23.gammaOf ρ‖ ^ 2)) :
    (Zeta23.EF.literatureRHS k).re ≤ C * (33 / 100) := by
  obtain ⟨hsumm, hEF⟩ := Zeta23.WeilEF.EF_lit_zeta Zeta23.zetaSeam k hk hkc
  have hg_nonneg : ∀ q : XiZeroCopy, 0 ≤ C * (1 / ‖Zeta23.gammaOf (q.1 : ℂ)‖ ^ 2) := fun q => by
    positivity
  have hg_summ : Summable (fun q : XiZeroCopy => C * (1 / ‖Zeta23.gammaOf (q.1 : ℂ)‖ ^ 2)) := by
    have : (fun q : XiZeroCopy => C * (1 / ‖Zeta23.gammaOf (q.1 : ℂ)‖ ^ 2)) =
        fun q => C * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      funext q; rw [gammaOf_eq_xiSpectralPoint]
    rw [this]
    exact xiSpectralPoint_inv_sq_summable.mul_left _
  have hterm' : ∀ ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
      ‖((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)‖ ≤
        ((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℝ) *
          (C * (1 / ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2)) := by
    intro ρ
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hterm ρ ρ.2) (Nat.cast_nonneg _)
  rw [← hEF, Complex.re_tsum hsumm]
  have hnormsumm : Summable (fun ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
      ‖((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)‖) :=
    summable_norm_iff.mpr hsumm
  calc ∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        (((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)).re
      ≤ ∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
        ‖((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)‖ :=
        (hsumm.mapL Complex.reCLM).tsum_le_tsum (fun ρ => Complex.re_le_norm _) hnormsumm
    _ ≤ ∑' q : XiZeroCopy, C * (1 / ‖Zeta23.gammaOf (q.1 : ℂ)‖ ^ 2) :=
        carrier_tsum_le Zeta23.zetaSeam (fun z => C * (1 / ‖Zeta23.gammaOf z‖ ^ 2)) hg_nonneg
          hg_summ _ hterm'
    _ = C * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
        rw [← tsum_mul_left]
        congr 1
        funext q
        rw [gammaOf_eq_xiSpectralPoint]
    _ ≤ C * (33 / 100) := by
        gcongr
        exact tsum_inv_normSq_spectralPoint_lt.le

/-- The exponent estimate `p·X ≤ 1`. -/
theorem exp_mul_X_le_one {u₀ : ℝ} (n : ℕ)
    (hexpo : u₀ + (33 / 100) * (2 * (n : ℝ) + 2) - 3 * n ≤ 0) :
    Real.exp u₀ * ((1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n) ≤ 1 := by
  have ha : (1081 / 780 : ℝ) ^ (2 * (n + 1)) ≤ Real.exp ((33 / 100) * (2 * (n : ℝ) + 2)) := by
    calc (1081 / 780 : ℝ) ^ (2 * (n + 1)) ≤ (Real.exp (33 / 100)) ^ (2 * (n + 1)) :=
          pow_le_pow_left₀ (by norm_num) rat_le_exp_third _
      _ = Real.exp ((33 / 100) * (2 * (n : ℝ) + 2)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
  have hb : (2 / 41 : ℝ) ^ n ≤ Real.exp (-3 * (n : ℝ)) := by
    calc (2 / 41 : ℝ) ^ n ≤ (Real.exp (-3)) ^ n :=
          pow_le_pow_left₀ (by norm_num) two_div_fortyOne_le_exp _
      _ = Real.exp (-3 * (n : ℝ)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hX : (1081 / 780 : ℝ) ^ (2 * (n + 1)) * (2 / 41) ^ n ≤
      Real.exp ((33 / 100) * (2 * (n : ℝ) + 2)) * Real.exp (-3 * (n : ℝ)) :=
    mul_le_mul ha hb (by positivity) (Real.exp_pos _).le
  calc Real.exp u₀ * ((1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n)
      ≤ Real.exp u₀ * (Real.exp ((33 / 100) * (2 * (n : ℝ) + 2)) * Real.exp (-3 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le
    _ = Real.exp (u₀ + (33 / 100) * (2 * (n : ℝ) + 2) - 3 * n) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr hexpo

/-- The real part of the deleted functional on a two-bump autocorrelation. -/
theorem deletedRHS_re_eq {p : ℕ} (hp : p.Prime) (φ : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hsupp : Function.support φ ⊆ Icc (-s) s) (h2s : 2 * s < Real.log p) :
    (deletedRHS p (fun x => (autocorr (twoBump φ (Real.log p)) x : ℂ))).re =
      (Zeta23.EF.literatureRHS (fun x => (autocorr (twoBump φ (Real.log p)) x : ℂ))).re +
        (Real.log p / Real.sqrt p) * (-2 * ∫ x, φ x ^ 2) := by
  unfold deletedRHS
  dsimp only
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp, autocorr_twoBump_apply hs hsupp h2s,
    autocorr_twoBump_apply_neg hs hsupp h2s, Complex.add_re, ← Complex.ofReal_add,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- **Every prime `p ≥ e^{18}` is load-bearing for Weil positivity:** deleting `p` from the prime
side of the explicit formula gives a functional that is negative on the autocorrelation of an
explicit real `C²` compactly supported test. -/
theorem deletedRHS_re_neg_of_large {p : ℕ} (hp : p.Prime) (hp18 : Real.exp 18 ≤ p) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
      (deletedRHS p (fun x => (autocorr f x : ℂ))).re < 0 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (Real.exp_pos _) hp18
  have hu18 : 18 ≤ Real.log p := by
    rw [Real.le_log_iff_exp_le hp0]
    exact hp18
  have hu0 : 0 ≤ Real.log p := by linarith
  have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hexp_half : Real.exp (Real.log p / 2) = Real.sqrt p := by
    have hsq : Real.exp (Real.log p / 2) ^ 2 = p := by
      rw [← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (Real.log p / 2) = Real.log p by ring, Real.exp_log hp0]
    have h := Real.sqrt_sq (Real.exp_pos (Real.log p / 2)).le
    rw [hsq] at h
    exact h.symm
  obtain ⟨h2s, hexpo⟩ := params_ok hu18
  set n : ℕ := ⌊(Real.log p - 4 / 5) / (39 / 25)⌋₊ - 2 with hn
  have hsupp := support_phiN_subset n
  refine ⟨twoBump (phiN n) (Real.log p), twoBump_contDiff (phiN_contDiff n) _,
    twoBump_hasCompactSupport hsupp hu0, ?_⟩
  have hkC : ContDiff ℝ 2 (fun x => (autocorr (twoBump (phiN n) (Real.log p)) x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (autocorr_contDiff (phiN_contDiff n) hsupp hu0)
  have hkcs : HasCompactSupport (fun x => (autocorr (twoBump (phiN n) (Real.log p)) x : ℂ)) :=
    (autocorr_hasCompactSupport hsupp hu0).comp_left Complex.ofReal_zero
  set X : ℝ := (1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  have hzero := re_literatureRHS_le hkC hkcs (C := 4 * Real.sqrt p * (3 / 2) * X) (by positivity)
    (fun ρ hρ => norm_paperFT_autocorr_twoBump_le n hu0 hexp_half
      (gammaOf_ne_zero_of_nontrivialZero hρ) (abs_im_gammaOf_le_half_of_nontrivialZero hρ)
      (fortyOne_div_two_lt_normSq_gammaOf_of_nontrivialZero hρ))
  rw [deletedRHS_re_eq hp (phiN n) (sN_pos n).le hsupp h2s]
  have hint : 1 / (2 * sN n) ≤ ∫ x, phiN n x ^ 2 := integral_phiN_sq_ge n
  have hint' : 1 / Real.log p ≤ ∫ x, phiN n x ^ 2 := by
    refine le_trans ?_ hint
    have := sN_pos n
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    linarith
  have hprod : (Real.log p / Real.sqrt p) * (-2 * ∫ x, phiN n x ^ 2) ≤ -(2 / Real.sqrt p) := by
    have h1 : (Real.log p / Real.sqrt p) * (-2 * ∫ x, phiN n x ^ 2) ≤
        (Real.log p / Real.sqrt p) * (-2 * (1 / Real.log p)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : (Real.log p / Real.sqrt p) * (-2 * (1 / Real.log p)) = -(2 / Real.sqrt p) := by
      field_simp
    linarith
  have hpX : (p : ℝ) * X ≤ 1 := by
    have := exp_mul_X_le_one n hexpo
    rwa [Real.exp_log hp0] at this
  have hC : 4 * Real.sqrt p * (3 / 2) * X * (33 / 100) < 2 / Real.sqrt p := by
    have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
    rw [lt_div_iff₀ hsqrt_pos]
    calc 4 * Real.sqrt p * (3 / 2) * X * (33 / 100) * Real.sqrt p
        = (99 / 50) * ((Real.sqrt p * Real.sqrt p) * X) := by ring
      _ = (99 / 50) * ((p : ℝ) * X) := by rw [hsq]
      _ ≤ 99 / 50 := by linarith
      _ < 2 := by norm_num
  linarith

/-- **Corollary in the form of a statement about primes:** for every prime `p ≥ 7·10⁷` the
prime-deleted explicit-formula functional is indefinite. -/
theorem deletedRHS_re_neg_of_ge {p : ℕ} (hp : p.Prime) (hp7 : 70000000 ≤ p) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
      (deletedRHS p (fun x => (autocorr f x : ℂ))).re < 0 := by
  apply deletedRHS_re_neg_of_large hp
  have h1 : Real.exp 18 < 70000000 := by
    have h := Real.exp_one_lt_d9
    rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    calc Real.exp 1 ^ 18 < 2.7182818286 ^ 18 := by gcongr
      _ < 70000000 := by norm_num
  have h2 : (70000000 : ℝ) ≤ p := by exact_mod_cast hp7
  linarith

end

end RHTower.WeilDeletion
