import GaloisForLFunctions.RHTower.WeilDeletionZeroSide

/-!
# Weil positivity is destroyed by deleting one large prime

Let `Λ' := Λ − (log p₀)·1_{p₀}` be the von Mangoldt function with one prime `p₀ > 3 594 641`
deleted, and let `W'[k]` be the right-hand side of the Weil explicit formula with the prime side
taken for `Λ'` instead of `Λ`:

  `W'[k] = literatureRHS k + (log p₀/√p₀)·(k(log p₀) + k(−log p₀))`.

For the autocorrelation `k = f ⋆ f̃` of the real test `f(y) = φ(y − u₀/2) − φ(y + u₀/2)`,
`u₀ = log p₀`, `φ` a smooth probability density supported in `[−7.42, 7.42]` with the Fourier
bound of `WeilDeletionTestKit`, one has

* `literatureRHS k = Σ_ρ m_ρ k̂(γ_ρ)` (Zeta23's unconditional explicit formula), whose real part is
  at most `4√p₀·(3/2)·360·(2/41)⁸·Σ_ρ m_ρ‖γ_ρ‖⁻² < 7·10⁻⁵`, because
  `‖k̂(γ_ρ)‖ ≤ 4e^{u₀|Im γ_ρ|}·e^{r}·(cosh(w/2)/(w‖γ_ρ‖))^{18}` and every zero has `‖γ_ρ‖² > 41/2`;
* `k(±u₀) = −∫φ² ≤ −1/14.84`, so the deleted prime contributes `−2(log p₀/√p₀)∫φ² < −7·10⁻⁴`.

Hence `Re W'[k] < 0`: the explicit-formula functional of `Λ'` is not positive semidefinite on real
compactly supported tests.  Consequently no proof of Weil positivity for `ζ` can use the primes
beyond `3 594 641` only through bounds that `Λ'` also satisfies (Chebyshev-type capacities, `Λ ≤ log`,
nonnegativity): every such argument would prove the false statement `W' ⪰ 0`.
-/

open Complex MeasureTheory Set
open scoped Convolution

namespace RHTower.WeilDeletion

noncomputable section

/-- The explicit-formula functional with the prime `p₀` deleted from the prime side. -/
def deletedRHS (p₀ : ℕ) (k : ℝ → ℂ) : ℂ :=
  Zeta23.EF.literatureRHS k +
    ((ArithmeticFunction.vonMangoldt p₀ / Real.sqrt p₀ : ℝ) : ℂ) *
      (k (Real.log p₀) + k (-Real.log p₀))

/-! ## Numerical facts -/

theorem exp_fifteen_lt : Real.exp 15 < 3594641 := by
  have h := Real.exp_one_lt_d9
  rw [show (15 : ℝ) = ((15 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
  calc Real.exp 1 ^ (15 : ℕ) < 2.7182818286 ^ (15 : ℕ) := by gcongr
    _ < 3594641 := by norm_num

theorem exp_two_fifths_le : Real.exp (2 / 5) ≤ 3 / 2 := by
  have h := Real.exp_bound (x := 2 / 5) (by norm_num) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  rw [abs_le] at h
  linarith [h.2]

theorem cosh_le_bound : Real.cosh (39 / 100) ≤ 1081 / 1000 := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_bound (x := 39 / 100) (by norm_num) (n := 4) (by norm_num)
  have h2 := Real.exp_bound (x := -(39 / 100)) (by norm_num) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1 h2
  norm_num at h1 h2
  rw [abs_le] at h1 h2
  linarith [h1.2, h2.2]

theorem cosh_le_exp_abs (t : ℝ) : Real.cosh t ≤ Real.exp |t| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.mpr (le_abs_self t)
  have h2 : Real.exp (-t) ≤ Real.exp |t| := Real.exp_le_exp.mpr (neg_le_abs t)
  linarith

/-! ## The test function -/

/-- The bump: radius `2/5` smoothing, nine uniform factors of half-width `39/50`. -/
def bumpPhi : ℝ → ℝ := phi (2 / 5) (by norm_num) (39 / 50) 8

/-- Half-width of the support of `bumpPhi`. -/
def bumpS : ℝ := 371 / 50

theorem bumpPhi_contDiff : ContDiff ℝ 2 bumpPhi := phi_contDiff _ _ _

theorem bumpPhi_hasCompactSupport : HasCompactSupport bumpPhi := phi_hasCompactSupport _ _ _

theorem bumpPhi_nonneg (x : ℝ) : 0 ≤ bumpPhi x := phi_nonneg _ (by norm_num) _ x

theorem integrable_bumpPhi : Integrable bumpPhi := integrable_phi _ _ _

theorem integral_bumpPhi : ∫ x, bumpPhi x = 1 := integral_phi _ (by norm_num) _

theorem support_bumpPhi_subset : Function.support bumpPhi ⊆ Icc (-bumpS) bumpS := by
  have := support_phi_subset (r := 2 / 5) (by norm_num) (w := 39 / 50) (by norm_num) 8
  have hs : (2 / 5 : ℝ) + ((8 : ℕ) + 1) * (39 / 50) = bumpS := by
    unfold bumpS; norm_num
  rw [hs] at this
  exact this

theorem integrable_bumpPhi_sq : Integrable (fun x => bumpPhi x ^ (2 : ℕ)) := by
  have hc : Continuous (fun x => bumpPhi x ^ (2 : ℕ)) := bumpPhi_contDiff.continuous.pow 2
  have hcs : HasCompactSupport (fun x => bumpPhi x ^ (2 : ℕ)) := by
    have h := bumpPhi_hasCompactSupport.mul_right (f' := bumpPhi)
    have e : (bumpPhi * bumpPhi) = fun x => bumpPhi x ^ (2 : ℕ) := by
      funext x
      simp [sq]
    rw [← e]
    exact h
  exact hc.integrable_of_hasCompactSupport hcs

theorem integral_bumpPhi_sq_ge : 1 / (2 * bumpS) ≤ ∫ x, bumpPhi x ^ (2 : ℕ) :=
  integral_sq_ge_of_support (by unfold bumpS; norm_num) bumpPhi_nonneg support_bumpPhi_subset
    integrable_bumpPhi integral_bumpPhi integrable_bumpPhi_sq

/-- The Fourier bound of `bumpPhi` on the strip `|Im z| ≤ 1/2`. -/
theorem norm_paperFT_bumpPhi_le {z : ℂ} (hz : z ≠ 0) (him : |z.im| ≤ 1 / 2) :
    ‖Zeta23.paperFT (fun x => (bumpPhi x : ℂ)) z‖ ≤
      Real.exp (1 / 5) * ((1081 / 780) / ‖z‖) ^ (9 : ℕ) := by
  have h := norm_paperFT_phi_le (r := 2 / 5) (by norm_num) (w := 39 / 50) (by norm_num) 8 hz
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
  calc Real.exp (2 / 5 * |z.im|) * (Real.cosh (39 / 50 * z.im) / (39 / 50 * ‖z‖)) ^ (8 + 1)
      ≤ Real.exp (1 / 5) * ((1081 / 780) / ‖z‖) ^ (8 + 1) := by
        gcongr
    _ = Real.exp (1 / 5) * ((1081 / 780) / ‖z‖) ^ (9 : ℕ) := by norm_num

/-! ## The deleted functional on the two-bump autocorrelation -/

/-- **Deleting one prime above `3 594 641` makes the explicit-formula functional negative** on the
autocorrelation of an explicit real `C²` compactly supported test. -/
theorem exists_deletedRHS_re_neg :
    ∃ p₀ : ℕ, p₀.Prime ∧ 3594641 < p₀ ∧ p₀ ≤ 2 * 3594641 ∧
      ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
        (deletedRHS p₀ (fun x => (autocorr f x : ℂ))).re < 0 := by
  classical
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul 3594641 (by norm_num)
  refine ⟨p, hp, hlt, hle, ?_⟩
  -- real bounds on the prime
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpR : (3594641 : ℝ) < p := by exact_mod_cast hlt
  have hpR' : (p : ℝ) ≤ 7189282 := by exact_mod_cast hle
  set u₀ : ℝ := Real.log p with hu₀
  have hu15 : 15 < u₀ := by
    rw [hu₀, Real.lt_log_iff_exp_lt hp0]
    exact exp_fifteen_lt.trans hpR
  have hu0 : 0 ≤ u₀ := by linarith
  have hsqrt_le : Real.sqrt p ≤ 2682 := by
    calc Real.sqrt p ≤ Real.sqrt (2682 ^ (2 : ℕ)) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2682 := Real.sqrt_sq (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hexp_half : Real.exp (u₀ / 2) = Real.sqrt p := by
    have hsq : Real.exp (u₀ / 2) ^ (2 : ℕ) = p := by
      rw [← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (u₀ / 2) = u₀ by ring, hu₀, Real.exp_log hp0]
    rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]
  -- the test
  set φ := bumpPhi with hφ
  have hsupp := support_bumpPhi_subset
  have hs0 : (0 : ℝ) ≤ bumpS := by unfold bumpS; norm_num
  have h2s : 2 * bumpS < u₀ := by unfold bumpS; linarith
  set f := twoBump φ u₀ with hf
  set k : ℝ → ℂ := fun x => (autocorr f x : ℂ) with hk
  have hfC : ContDiff ℝ 2 f := twoBump_contDiff bumpPhi_contDiff u₀
  have hfcs : HasCompactSupport f := twoBump_hasCompactSupport hsupp hu0
  refine ⟨f, hfC, hfcs, ?_⟩
  have hkC : ContDiff ℝ 2 k :=
    Complex.ofRealCLM.contDiff.comp (autocorr_contDiff bumpPhi_contDiff hsupp hu0)
  have hkcs : HasCompactSupport k :=
    (autocorr_hasCompactSupport hsupp hu0).comp_left Complex.ofReal_zero
  -- the explicit formula
  obtain ⟨hsumm, hEF⟩ := Zeta23.WeilEF.EF_lit_zeta Zeta23.zetaSeam k hkC hkcs
  -- the value of `k` at `±u₀`
  have hku : k u₀ = ((-∫ x, φ x ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp only [hk]
    rw [autocorr_twoBump_apply hs0 hsupp h2s]
  have hku' : k (-u₀) = ((-∫ x, φ x ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp only [hk]
    rw [autocorr_twoBump_apply_neg hs0 hsupp h2s]
  -- the zero-side majorant
  set C₁ : ℝ := 4 * 2682 * (3 / 2) * 360 * (2 / 41) ^ (8 : ℕ) with hC₁
  have hC₁pos : 0 < C₁ := by rw [hC₁]; norm_num
  have hterm : ∀ ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
      ‖((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)‖ ≤
        ((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℝ) *
          (C₁ * (1 / ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ (2 : ℕ))) := by
    intro ρ
    have hρ : Zeta23.IsNontrivialZero (ρ : ℂ) := ρ.2
    set γ := Zeta23.gammaOf (ρ : ℂ) with hγ
    have hγ0 : γ ≠ 0 := gammaOf_ne_zero_of_nontrivialZero hρ
    have hγim : |γ.im| ≤ 1 / 2 := abs_im_gammaOf_le_half_of_nontrivialZero hρ
    have hγsq : (41 / 2 : ℝ) < ‖γ‖ ^ (2 : ℕ) := fortyOne_div_two_lt_normSq_gammaOf_of_nontrivialZero hρ
    have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hγ0
    rw [norm_mul, Complex.norm_natCast]
    gcongr
    -- `k̂(γ) = f̂(γ) f̂(−γ)`
    have hkFT : Zeta23.paperFT k γ = Zeta23.paperFT (fun x => (f x : ℂ)) γ *
        Zeta23.paperFT (fun x => (f x : ℂ)) (-γ) :=
      paperFT_autocorr (twoBump_integrable bumpPhi_contDiff hsupp hu0)
        (support_twoBump_subset hsupp hu0) γ
    rw [hkFT, norm_mul]
    -- each factor
    have hΦ : ∀ z : ℂ, z ≠ 0 → |z.im| ≤ 1 / 2 →
        ‖Zeta23.paperFT (fun x => (f x : ℂ)) z‖ ≤
          (Real.exp (1 / 5) * ((1081 / 780) / ‖z‖) ^ (9 : ℕ)) * (2 * Real.cosh (u₀ / 2 * z.im)) := by
      intro z hz hzim
      refine (norm_paperFT_twoBump_le integrable_bumpPhi hsupp u₀ z).trans ?_
      gcongr
      exact norm_paperFT_bumpPhi_le hz hzim
    have hγ' : -γ ≠ 0 := neg_ne_zero.mpr hγ0
    have hγim' : |(-γ).im| ≤ 1 / 2 := by rw [Complex.neg_im, abs_neg]; exact hγim
    have hnormneg : ‖-γ‖ = ‖γ‖ := norm_neg γ
    have hc1 : 2 * Real.cosh (u₀ / 2 * γ.im) ≤ 2 * Real.exp (u₀ / 4) := by
      have := cosh_le_exp_abs (u₀ / 2 * γ.im)
      have h2 : Real.exp |u₀ / 2 * γ.im| ≤ Real.exp (u₀ / 4) := by
        apply Real.exp_le_exp.mpr
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u₀ / 2)]
        nlinarith [hγim, abs_nonneg γ.im]
      linarith
    have hc2 : 2 * Real.cosh (u₀ / 2 * (-γ).im) ≤ 2 * Real.exp (u₀ / 4) := by
      have := cosh_le_exp_abs (u₀ / 2 * (-γ).im)
      have h2 : Real.exp |u₀ / 2 * (-γ).im| ≤ Real.exp (u₀ / 4) := by
        apply Real.exp_le_exp.mpr
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u₀ / 2)]
        nlinarith [hγim', abs_nonneg (-γ).im]
      linarith
    have hA := hΦ γ hγ0 hγim
    have hB := hΦ (-γ) hγ' hγim'
    rw [hnormneg] at hB
    -- assemble
    have hpow : ((1081 / 780 : ℝ) / ‖γ‖) ^ (9 : ℕ) * ((1081 / 780 : ℝ) / ‖γ‖) ^ (9 : ℕ) =
        (1081 / 780 : ℝ) ^ (18 : ℕ) / ‖γ‖ ^ (18 : ℕ) := by
      rw [← pow_add, div_pow]
    have hexp2 : Real.exp (1 / 5) * Real.exp (1 / 5) = Real.exp (2 / 5) := by
      rw [← Real.exp_add]; norm_num
    have hexp4 : Real.exp (u₀ / 4) * Real.exp (u₀ / 4) = Real.sqrt p := by
      rw [← Real.exp_add, ← hexp_half]; congr 1; ring
    have hpow18 : ((1081 / 780 : ℝ)) ^ (18 : ℕ) ≤ 360 := by norm_num
    have hnorm18 : 1 / ‖γ‖ ^ (18 : ℕ) ≤ (2 / 41) ^ (8 : ℕ) * (1 / ‖γ‖ ^ (2 : ℕ)) := by
      have h : ‖γ‖ ^ (18 : ℕ) = ‖γ‖ ^ (2 : ℕ) * (‖γ‖ ^ (2 : ℕ)) ^ (8 : ℕ) := by ring
      rw [h, one_div, mul_inv, ← one_div, ← one_div, mul_comm]
      gcongr
      rw [div_le_iff₀ (by positivity)]
      rw [show (2 / 41 : ℝ) ^ (8 : ℕ) * (‖γ‖ ^ (2 : ℕ)) ^ (8 : ℕ) = ((2 / 41) * ‖γ‖ ^ (2 : ℕ)) ^ (8 : ℕ) by rw [mul_pow]]
      have : (1 : ℝ) ≤ (2 / 41) * ‖γ‖ ^ (2 : ℕ) := by nlinarith
      exact one_le_pow₀ this
    have hn18 : 0 < ‖γ‖ ^ (18 : ℕ) := by positivity
    calc ‖Zeta23.paperFT (fun x => (f x : ℂ)) γ‖ * ‖Zeta23.paperFT (fun x => (f x : ℂ)) (-γ)‖
        ≤ ((Real.exp (1 / 5) * ((1081 / 780) / ‖γ‖) ^ (9 : ℕ)) * (2 * Real.exp (u₀ / 4))) *
          ((Real.exp (1 / 5) * ((1081 / 780) / ‖γ‖) ^ (9 : ℕ)) * (2 * Real.exp (u₀ / 4))) := by
          calc ‖Zeta23.paperFT (fun x => (f x : ℂ)) γ‖ * ‖Zeta23.paperFT (fun x => (f x : ℂ)) (-γ)‖
              ≤ ((Real.exp (1 / 5) * ((1081 / 780) / ‖γ‖) ^ (9 : ℕ)) * (2 * Real.cosh (u₀ / 2 * γ.im))) *
                ((Real.exp (1 / 5) * ((1081 / 780) / ‖γ‖) ^ (9 : ℕ)) *
                  (2 * Real.cosh (u₀ / 2 * (-γ).im))) :=
                mul_le_mul hA hB (norm_nonneg _) (by positivity)
            _ ≤ _ := by
                gcongr
        _ = 4 * Real.sqrt p * Real.exp (2 / 5) * ((1081 / 780) ^ (18 : ℕ) / ‖γ‖ ^ (18 : ℕ)) := by
          rw [← hexp2, ← hexp4, ← hpow]
          ring
        _ ≤ 4 * 2682 * (3 / 2) * (360 * ((2 / 41) ^ (8 : ℕ) * (1 / ‖γ‖ ^ (2 : ℕ)))) := by
          have hq : (1081 / 780 : ℝ) ^ (18 : ℕ) / ‖γ‖ ^ (18 : ℕ) ≤ 360 * ((2 / 41) ^ (8 : ℕ) * (1 / ‖γ‖ ^ (2 : ℕ))) := by
            calc (1081 / 780 : ℝ) ^ (18 : ℕ) / ‖γ‖ ^ (18 : ℕ) = (1081 / 780) ^ (18 : ℕ) * (1 / ‖γ‖ ^ (18 : ℕ)) := by
                  rw [mul_one_div]
              _ ≤ 360 * ((2 / 41) ^ (8 : ℕ) * (1 / ‖γ‖ ^ (2 : ℕ))) := by
                  gcongr
          gcongr
          exact exp_two_fifths_le
        _ = C₁ * (1 / ‖γ‖ ^ (2 : ℕ)) := by rw [hC₁]; ring
  -- the zero side is small
  have hg_nonneg : ∀ q : XiZeroCopy, 0 ≤ C₁ * (1 / ‖Zeta23.gammaOf (q.1 : ℂ)‖ ^ (2 : ℕ)) := fun q => by
    positivity
  have hg_summ : Summable (fun q : XiZeroCopy => C₁ * (1 / ‖Zeta23.gammaOf (q.1 : ℂ)‖ ^ (2 : ℕ))) := by
    have : (fun q : XiZeroCopy => C₁ * (1 / ‖Zeta23.gammaOf (q.1 : ℂ)‖ ^ (2 : ℕ))) =
        fun q => C₁ * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
      funext q; rw [gammaOf_eq_xiSpectralPoint]
    rw [this]
    exact xiSpectralPoint_inv_sq_summable.mul_left _
  have hzero : (Zeta23.EF.literatureRHS k).re ≤ C₁ * (33 / 100) := by
    rw [← hEF, Complex.re_tsum hsumm]
    have hnormsumm : Summable (fun ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
        ‖((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)‖) :=
      summable_norm_iff.mpr hsumm
    calc ∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
          (((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)).re
        ≤ ∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
          ‖((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)‖ :=
          (hsumm.mapL Complex.reCLM).tsum_le_tsum (fun ρ => Complex.re_le_norm _) hnormsumm
      _ ≤ ∑' q : XiZeroCopy, C₁ * (1 / ‖Zeta23.gammaOf (q.1 : ℂ)‖ ^ (2 : ℕ)) :=
          carrier_tsum_le Zeta23.zetaSeam (fun z => C₁ * (1 / ‖Zeta23.gammaOf z‖ ^ (2 : ℕ))) hg_nonneg
            hg_summ _ hterm
      _ = C₁ * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
          rw [← tsum_mul_left]
          congr 1
          funext q
          rw [gammaOf_eq_xiSpectralPoint]
      _ ≤ C₁ * (33 / 100) := by
          gcongr
          exact tsum_inv_normSq_spectralPoint_lt.le
  -- the deleted prime contributes a negative amount
  have hΛ : ArithmeticFunction.vonMangoldt p = u₀ := by
    rw [hu₀]; exact ArithmeticFunction.vonMangoldt_apply_prime hp
  have hdel : (deletedRHS p k).re =
      (Zeta23.EF.literatureRHS k).re + (u₀ / Real.sqrt p) * (-2 * ∫ x, φ x ^ (2 : ℕ)) := by
    unfold deletedRHS
    rw [hΛ, hku, hku', Complex.add_re, ← Complex.ofReal_add, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  have hint : 1 / (2 * bumpS) ≤ ∫ x, φ x ^ (2 : ℕ) := integral_bumpPhi_sq_ge
  have hratio : 15 / 2682 ≤ u₀ / Real.sqrt p := by
    rw [div_le_div_iff₀ (by norm_num) hsqrt_pos]
    nlinarith [hsqrt_le, hu15, hsqrt_pos]
  have hprod : (u₀ / Real.sqrt p) * (-2 * ∫ x, φ x ^ (2 : ℕ)) ≤ (15 / 2682) * (-2 * (1 / (2 * bumpS))) := by
    have h1 : (u₀ / Real.sqrt p) * (-2 * ∫ x, φ x ^ (2 : ℕ)) ≤ (u₀ / Real.sqrt p) * (-2 * (1 / (2 * bumpS))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : (u₀ / Real.sqrt p) * (-2 * (1 / (2 * bumpS))) ≤ (15 / 2682) * (-2 * (1 / (2 * bumpS))) := by
      apply mul_le_mul_of_nonpos_right hratio
      unfold bumpS; norm_num
    exact h1.trans h2
  rw [hdel]
  have hnum : C₁ * (33 / 100) + (15 / 2682) * (-2 * (1 / (2 * bumpS))) < 0 := by
    rw [hC₁]; unfold bumpS; norm_num
  linarith

end

end RHTower.WeilDeletion
