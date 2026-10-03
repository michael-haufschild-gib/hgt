import GaloisForLFunctions.RHTower.Sieve.VinogradovZetaGrowthLemmas
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSigma

/-!
# Block bounds for `ζ` near `σ = 1` at the Vinogradov–Korobov width

Let `L = log τ` and `θ = L^{-2/3} (log L)^{-2/3} / 100` (`vinogradovKorobovWidth`).  For
`1 - θ ≤ σ ≤ 2` and a dyadic block `(Y, 2Y]`:

* middle blocks, `e^{L^{2/3}} ≤ Y`, `Y^{22} ≤ τ`: `‖Σ n^{-σ-iτ}‖ ≤ 12e^{21} + 201`
  (`norm_block_le_middle`), from the dyadic Vinogradov estimate and
  `log Y · (θ - δ_R/4) ≤ θ^{3/2}√A = 864/1000`;
* large blocks, `τ < Y^{22}`, `8π(Y+1)^{1/3} ≤ τ`: `‖Σ n^{-σ-iτ}‖ ≤ 2560`
  (`norm_block_le_large`), from
  the `24`-th derivative test (`dirichlet_block_sigma_saving_of_small_factorial`) since
  `θ ≤ 1/(3·2^{24})`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The Vinogradov–Korobov width `θ(L) = L^{-2/3} (log L)^{-2/3} / 100`. -/
def vinogradovKorobovWidth (L : ℝ) : ℝ :=
  1 / 100 * L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(2 : ℝ) / 3)

theorem one_le_log_of_exp_thirty_le {L : ℝ} (hL : Real.exp 30 ≤ L) : 30 ≤ Real.log L := by
  rw [← Real.log_exp 30]; exact Real.log_le_log (Real.exp_pos _) hL

theorem vinogradovKorobovWidth_pos {L : ℝ} (hL : Real.exp 30 ≤ L) :
    0 < vinogradovKorobovWidth L := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl := one_le_log_of_exp_thirty_le hL
  unfold vinogradovKorobovWidth
  have : 0 < Real.log L := by linarith
  positivity

/-- `θ√θ√(746496 L²(log L)²) = 864/1000`. -/
theorem vinogradovKorobovWidth_cube {L : ℝ} (hL : Real.exp 30 ≤ L) :
    vinogradovKorobovWidth L * Real.sqrt (vinogradovKorobovWidth L) *
        Real.sqrt (746496 * L ^ 2 * Real.log L ^ 2) = 864 / 1000 := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl := one_le_log_of_exp_thirty_le hL
  set M := Real.log L with hM
  have hM0 : 0 < M := by linarith
  have hsq : Real.sqrt (vinogradovKorobovWidth L) =
      1 / 10 * L ^ (-(1 : ℝ) / 3) * M ^ (-(1 : ℝ) / 3) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (vinogradovKorobovWidth_pos hL).le (by positivity)]
    unfold vinogradovKorobovWidth
    rw [← hM]
    have e1 : L ^ (-(1 : ℝ) / 3) * L ^ (-(1 : ℝ) / 3) = L ^ (-(2 : ℝ) / 3) := by
      rw [← Real.rpow_add hL0]; norm_num
    have e2 : M ^ (-(1 : ℝ) / 3) * M ^ (-(1 : ℝ) / 3) = M ^ (-(2 : ℝ) / 3) := by
      rw [← Real.rpow_add hM0]; norm_num
    have h : 1 / 10 * L ^ (-(1 : ℝ) / 3) * M ^ (-(1 : ℝ) / 3) *
          (1 / 10 * L ^ (-(1 : ℝ) / 3) * M ^ (-(1 : ℝ) / 3)) =
        1 / 100 * L ^ (-(2 : ℝ) / 3) * M ^ (-(2 : ℝ) / 3) := by
      calc 1 / 10 * L ^ (-(1 : ℝ) / 3) * M ^ (-(1 : ℝ) / 3) *
            (1 / 10 * L ^ (-(1 : ℝ) / 3) * M ^ (-(1 : ℝ) / 3))
          = 1 / 100 * (L ^ (-(1 : ℝ) / 3) * L ^ (-(1 : ℝ) / 3)) *
            (M ^ (-(1 : ℝ) / 3) * M ^ (-(1 : ℝ) / 3)) := by ring
        _ = _ := by rw [e1, e2]
    exact h.symm
  have hsA : Real.sqrt (746496 * L ^ 2 * M ^ 2) = 864 * L * M := by
    rw [show (746496 : ℝ) * L ^ 2 * M ^ 2 = (864 * L * M) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq, hsA]
  unfold vinogradovKorobovWidth
  rw [← hM]
  have eL : L ^ (-(2 : ℝ) / 3) * L ^ (-(1 : ℝ) / 3) * L = 1 := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add_one hL0.ne']; norm_num
  have eM : M ^ (-(2 : ℝ) / 3) * M ^ (-(1 : ℝ) / 3) * M = 1 := by
    rw [← Real.rpow_add hM0, ← Real.rpow_add_one hM0.ne']; norm_num
  calc 1 / 100 * L ^ (-(2 : ℝ) / 3) * M ^ (-(2 : ℝ) / 3) *
        (1 / 10 * L ^ (-(1 : ℝ) / 3) * M ^ (-(1 : ℝ) / 3)) * (864 * L * M)
      = 864 / 1000 * (L ^ (-(2 : ℝ) / 3) * L ^ (-(1 : ℝ) / 3) * L) *
        (M ^ (-(2 : ℝ) / 3) * M ^ (-(1 : ℝ) / 3) * M) := by ring
    _ = 864 / 1000 := by rw [eL, eM]; ring

/-- `θ L^{2/3} ≤ 1/100`. -/
theorem vinogradovKorobovWidth_mul_le {L : ℝ} (hL : Real.exp 30 ≤ L) :
    vinogradovKorobovWidth L * L ^ ((2 : ℝ) / 3) ≤ 1 / 100 := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl := one_le_log_of_exp_thirty_le hL
  unfold vinogradovKorobovWidth
  have eL : L ^ (-(2 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hL0]; norm_num
  have hM : Real.log L ^ (-(2 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  calc 1 / 100 * L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(2 : ℝ) / 3) * L ^ ((2 : ℝ) / 3)
      = 1 / 100 * (L ^ (-(2 : ℝ) / 3) * L ^ ((2 : ℝ) / 3)) * Real.log L ^ (-(2 : ℝ) / 3) := by
        ring
    _ ≤ 1 / 100 * 1 * 1 := by rw [eL]; gcongr
    _ = 1 / 100 := by ring

/-- `θ ≤ 1/(3·2^{24})`. -/
theorem vinogradovKorobovWidth_le {L : ℝ} (hL : Real.exp 30 ≤ L) :
    vinogradovKorobovWidth L ≤ 1 / (3 * (2 : ℝ) ^ (24 : ℕ)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have h := vinogradovKorobovWidth_mul_le hL
  have hθ := (vinogradovKorobovWidth_pos hL).le
  have hL23 : (2 : ℝ) ^ (24 : ℕ) * 3 / 100 ≤ L ^ ((2 : ℝ) / 3) := by
    have he : (2 : ℝ) ^ (36 : ℕ) ≤ Real.exp 30 := by
      have h2 : Real.exp 30 = Real.exp 1 ^ 30 := by rw [← Real.exp_nat_mul]; norm_num
      have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have : (2.7 : ℝ) ^ 30 ≤ Real.exp 1 ^ 30 := pow_le_pow_left₀ (by norm_num) he 30
      rw [h2]; norm_num at this ⊢; linarith
    have hL36 : (2 : ℝ) ^ (36 : ℕ) ≤ L := he.trans hL
    have : ((2 : ℝ) ^ (36 : ℕ)) ^ ((2 : ℝ) / 3) ≤ L ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hL36 (by norm_num)
    have e : ((2 : ℝ) ^ (36 : ℕ)) ^ ((2 : ℝ) / 3) = (2 : ℝ) ^ (24 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]; norm_num
    rw [e] at this
    have : (2 : ℝ) ^ (24 : ℕ) * 3 / 100 ≤ (2 : ℝ) ^ (24 : ℕ) := by
      have : (0 : ℝ) < 2 ^ (24 : ℕ) := by positivity
      linarith
    linarith
  rw [le_div_iff₀ (by positivity)]
  have hpos : 0 < L ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hL0 _
  have : vinogradovKorobovWidth L * ((2 : ℝ) ^ (24 : ℕ) * 3 / 100) ≤ 1 / 100 :=
    le_trans (mul_le_mul_of_nonneg_left hL23 hθ) h
  nlinarith

/-- `(n : ℂ)^{-iτ}` is the conjugate of `n^{iτ}`. -/
theorem natCast_cpow_neg_I_mul_eq_conj (τ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-(Complex.I * (τ : ℂ))) = starRingEnd ℂ (vinogradovLogPhase τ n) := by
  rw [natCast_cpow_neg_I_mul τ n hn, vinogradovLogPhase, ← finitePhaseChar_neg]
  unfold finitePhaseChar logPhase
  congr 1
  push_cast
  ring_nf

/-- `Ico (Y+1) m = Ioc Y (m - 1)` and the sum of `n^{-iτ}` is the conjugate. -/
theorem norm_sum_Ico_cpow_eq {τ : ℝ} {Y m : ℕ} (hm : Y + 1 ≤ m) :
    ‖∑ n ∈ Finset.Ico (Y + 1) m, (n : ℂ) ^ (-(Complex.I * (τ : ℂ)))‖ =
      ‖∑ n ∈ Finset.Ioc Y (Y + (m - 1 - Y)), vinogradovLogPhase τ n‖ := by
  have hset : Finset.Ico (Y + 1) m = Finset.Ioc Y (Y + (m - 1 - Y)) := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
  rw [hset, ← RCLike.norm_conj, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
  rw [natCast_cpow_neg_I_mul_eq_conj τ hn1, RCLike.conj_conj]

theorem hundred_le_rpow_third {L : ℝ} (hL : Real.exp 30 ≤ L) : (100 : ℝ) ≤ L ^ ((1 : ℝ) / 3) := by
  have h6 : (10 : ℝ) ^ 6 ≤ L := by
    have h2 : Real.exp 30 = Real.exp 1 ^ 30 := by rw [← Real.exp_nat_mul]; norm_num
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have : (2.7 : ℝ) ^ 30 ≤ Real.exp 1 ^ 30 := pow_le_pow_left₀ (by norm_num) he 30
    rw [h2] at hL; norm_num at this; linarith
  have : ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 3) ≤ L ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by norm_num) h6 (by norm_num)
  have e : ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 3) = 100 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  linarith

theorem rpow_two_thirds_eq_sq {L : ℝ} (hL0 : 0 < L) :
    L ^ ((2 : ℝ) / 3) = L ^ ((1 : ℝ) / 3) * L ^ ((1 : ℝ) / 3) := by
  rw [← Real.rpow_add hL0]; norm_num

/-- **Middle blocks.** -/
theorem norm_block_le_middle {τ σ : ℝ} {Y : ℕ} (hL : Real.exp 30 ≤ Real.log τ)
    (hY : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y) (hYτ : (Y : ℝ) ^ 22 ≤ τ)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) :
    ‖∑ n ∈ Finset.Ico (Y + 1) (2 * Y + 1), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
      12 * Real.exp 21 + 201 := by
  set L := Real.log τ with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hlogL := one_le_log_of_exp_thirty_le hL
  set θ := vinogradovKorobovWidth L with hθ
  have hθ0 := vinogradovKorobovWidth_pos hL
  have hθsmall := vinogradovKorobovWidth_le hL
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hY1 : (1 : ℝ) ≤ Y := by
    have : (1 : ℝ) ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := Real.one_le_exp (by positivity)
    linarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hYτ
  set ℓ := Real.log Y with hℓ
  have hℓlow : L ^ ((2 : ℝ) / 3) ≤ ℓ := by
    rw [hℓ, ← Real.log_exp (L ^ ((2 : ℝ) / 3))]
    exact Real.log_le_log (Real.exp_pos _) hY
  have hℓL : 22 * ℓ ≤ L := by
    have := Real.log_le_log (by positivity) hYτ
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.rpow_pos_of_pos hL0 _) hℓlow
  set R := vinogradovBlockOrder L ℓ with hR
  have hR22 : 22 ≤ R := vinogradovBlockOrder_ge hℓ0 hℓL
  -- hypotheses of the dyadic estimate
  have hY38 : 3 ^ 8 ≤ Y := by
    have h1 : (3 : ℝ) ^ 8 ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := by
      have h30 : (30 : ℝ) ≤ L ^ ((2 : ℝ) / 3) := by
        have h100 := hundred_le_rpow_third hL
        rw [rpow_two_thirds_eq_sq hL0]
        have := mul_le_mul h100 h100 (by norm_num) (by linarith)
        linarith
      calc (3 : ℝ) ^ 8 ≤ Real.exp 30 := by
            have h2 : Real.exp 30 = Real.exp 1 ^ 30 := by rw [← Real.exp_nat_mul]; norm_num
            have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
            have : (2.7 : ℝ) ^ 30 ≤ Real.exp 1 ^ 30 := pow_le_pow_left₀ (by norm_num) he 30
            rw [h2]; norm_num at this ⊢; linarith
        _ ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := Real.exp_le_exp.mpr h30
    have : ((3 ^ 8 : ℕ) : ℝ) ≤ Y := by push_cast; linarith
    exact_mod_cast this
  have hroot : (Y : ℝ) ^ ((1 : ℝ) / 8) ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) / 3 := by
    have h3 : (3 : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 8) := by
      have : ((3 : ℝ) ^ 8) ^ ((1 : ℝ) / 8) ≤ (Y : ℝ) ^ ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hY38) (by norm_num)
      have e : ((3 : ℝ) ^ 8) ^ ((1 : ℝ) / 8) = 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith
    have e : (Y : ℝ) ^ ((1 : ℝ) / 4) = (Y : ℝ) ^ ((1 : ℝ) / 8) * (Y : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_add hY0]; norm_num
    rw [e, le_div_iff₀ (by norm_num)]
    have : 0 ≤ (Y : ℝ) ^ ((1 : ℝ) / 8) := by positivity
    nlinarith
  have htR : τ ≤ ((Y : ℝ) ^ ((1 : ℝ) / 4) / 3) ^ (4 * R) := by
    calc τ = Real.exp L := (Real.exp_log hτ0).symm
      _ ≤ Real.exp (R / 2 * ℓ) := by
          apply Real.exp_le_exp.mpr
          have := two_mul_div_le_vinogradovBlockOrder L ℓ
          rw [← hR] at this
          rw [div_le_iff₀ hℓ0] at this
          linarith
      _ = ((Y : ℝ) ^ ((1 : ℝ) / 8)) ^ (4 * R) := by
          rw [hℓ, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le, Real.rpow_def_of_pos hY0]
          congr 1; push_cast; ring
      _ ≤ ((Y : ℝ) ^ ((1 : ℝ) / 4) / 3) ^ (4 * R) :=
          pow_le_pow_left₀ (by positivity) hroot _
  have hthr : (vinogradovWeylThreshold R : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) / 3 := by
    have h1 := vinogradovWeylThreshold_le_pow R (by omega)
    have hRL : (R : ℝ) ≤ 3 * L ^ ((1 : ℝ) / 3) := by
      have h := vinogradovBlockOrder_le hℓ0 hℓL
      rw [← hR] at h
      calc (R : ℝ) ≤ 3 * L / ℓ := h
        _ ≤ 3 * L / L ^ ((2 : ℝ) / 3) := by
            apply div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hL0 _) hℓlow
        _ = 3 * L ^ ((1 : ℝ) / 3) := by
            rw [mul_div_assoc]
            congr 1
            rw [div_eq_iff (Real.rpow_pos_of_pos hL0 _).ne', ← Real.rpow_add hL0]
            norm_num
    have hR18 : ((2 ^ 54 * R ^ 18 : ℕ) : ℝ) ≤ 2 ^ 54 * (3 * L ^ ((1 : ℝ) / 3)) ^ 18 := by
      have e : ((2 ^ 54 * R ^ 18 : ℕ) : ℝ) = (2 : ℝ) ^ 54 * (R : ℝ) ^ 18 := by push_cast; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hRL 18)
        (by positivity)
    have hpoly : (2 : ℝ) ^ 54 * (3 * L ^ ((1 : ℝ) / 3)) ^ 18 * 3 ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) := by
      -- `log` of the left side is at most `L^{2/3}/4 ≤ ℓ/4`
      have hlhs : 0 < (2 : ℝ) ^ 54 * (3 * L ^ ((1 : ℝ) / 3)) ^ 18 * 3 := by positivity
      rw [← Real.exp_log hlhs, ← Real.exp_log (Real.rpow_pos_of_pos hY0 _),
        Real.exp_le_exp, Real.log_rpow hY0, ← hℓ]
      rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) (by positivity),
        Real.log_rpow hL0]
      have hl3 : Real.log 3 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.add_one_le_exp (2 : ℝ); linarith
      have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      have hlogL3 : Real.log L ≤ 3 * L ^ ((1 : ℝ) / 3) := by
        have h := Real.log_le_rpow_div (x := L) (ε := 1 / 3) hL0.le (by norm_num)
        linarith
      have hL13 := hundred_le_rpow_third hL
      set u := L ^ ((1 : ℝ) / 3) with hu
      have hℓu : u * u ≤ ℓ := by rw [← rpow_two_thirds_eq_sq hL0]; exact hℓlow
      have huu : 100 * u ≤ u * u := mul_le_mul_of_nonneg_right hL13 (by linarith)
      push_cast
      linarith [hl2, hl3, hlogL3, hℓu, huu, hL13]
    calc (vinogradovWeylThreshold R : ℝ) ≤ ((2 ^ 54 * R ^ 18 : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ 2 ^ 54 * (3 * L ^ ((1 : ℝ) / 3)) ^ 18 := hR18
      _ ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) / 3 := by rw [le_div_iff₀ (by norm_num)]; exact hpoly
  -- the prefix bound
  set δ := vinogradovDyadicSaving R with hδ
  set Pb : ℝ := 12 * Real.exp 20 * Y * (Y : ℝ) ^ (-(δ / 4)) + 200 * (Y : ℝ) ^ ((1 : ℝ) / 2)
    with hPb
  have hprefix : ∀ m, Y + 1 ≤ m → m ≤ 2 * Y + 1 →
      ‖∑ n ∈ Finset.Ico (Y + 1) m, (n : ℂ) ^ (-(Complex.I * (τ : ℂ)))‖ ≤ Pb := by
    intro m hm1 hm2
    rw [norm_sum_Ico_cpow_eq hm1]
    have h := norm_sum_logPhase_le_dyadic (N := Y) (A := Y) (L := m - 1 - Y) hR22 hY38 hYτ htR hthr
      le_rfl (by omega)
    refine h.trans ?_
    have hLm : ((m - 1 - Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast (by omega : m - 1 - Y ≤ Y)
    have : (0 : ℝ) ≤ 12 * Real.exp 20 * (Y : ℝ) ^ (-(δ / 4)) := by positivity
    rw [hPb]
    nlinarith
  have hσ0 : 0 ≤ σ := by linarith
  have hsig := dirichlet_block_sigma_bound hσ0 τ (Y + 1) (2 * Y + 1) (by omega) (by omega) Pb
    hprefix
  refine hsig.trans ?_
  -- `Pb (Y+1)^{-σ} ≤ 12 e^{21} + 201`
  have hYσ : ((Y + 1 : ℕ) : ℝ) ^ (-σ) ≤ (Y : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hY0 (by push_cast; linarith) (by linarith)
  have hexp : (Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-σ) ≤ Real.exp 1 := by
    have e : (Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-σ) = Real.exp (ℓ * (1 - σ - δ / 4)) := by
      have e1 : (Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-σ) =
          (Y : ℝ) ^ (1 + -(δ / 4) + -σ) := by
        rw [Real.rpow_add hY0, Real.rpow_add hY0, Real.rpow_one]
      rw [e1, Real.rpow_def_of_pos hY0, hℓ]
      congr 1
      ring
    exact le_of_eq_of_le e (by
      apply Real.exp_le_exp.mpr
      have hδl := vinogradovDyadicSaving_div_four_ge hL hℓlow hℓL
      rw [← hR, ← hδ] at hδl
      have hA : (0 : ℝ) < 746496 * L ^ 2 * Real.log L ^ 2 := by positivity
      have hcube := mul_sub_cube_div_le hθ0.le hℓ0.le hA
      rw [vinogradovKorobovWidth_cube hL] at hcube
      have h1 : ℓ * (1 - σ - δ / 4) ≤ θ * ℓ - ℓ * δ / 4 := by nlinarith
      have h2 : ℓ ^ 3 / (746496 * L ^ 2 * Real.log L ^ 2) ≤ ℓ * (δ / 4) := by
        have : ℓ ^ 3 / (746496 * L ^ 2 * Real.log L ^ 2) =
            ℓ * (ℓ ^ 2 / (746496 * L ^ 2 * Real.log L ^ 2)) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hδl hℓ0.le
      linarith)
  have hhalf : (Y : ℝ) ^ ((1 : ℝ) / 2) * (Y : ℝ) ^ (-σ) ≤ 1 := by
    rw [← Real.rpow_add hY0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
  have hPb0 : 0 ≤ Pb := by rw [hPb]; positivity
  calc Pb * ((Y + 1 : ℕ) : ℝ) ^ (-σ) ≤ Pb * (Y : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_left hYσ hPb0
    _ = 12 * Real.exp 20 * ((Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-σ)) +
        200 * ((Y : ℝ) ^ ((1 : ℝ) / 2) * (Y : ℝ) ^ (-σ)) := by rw [hPb]; ring
    _ ≤ 12 * Real.exp 20 * Real.exp 1 + 200 * 1 := by gcongr
    _ ≤ 12 * Real.exp 21 + 201 := by
        rw [show (21 : ℝ) = 20 + 1 by norm_num, Real.exp_add]; linarith


/-- `23! ≤ e^{200}`. -/
theorem factorial_twentythree_le_exp : ((Nat.factorial 23 : ℕ) : ℝ) ≤ Real.exp 200 := by
  have h1 : Nat.factorial 23 ≤ 2 ^ 115 := by
    calc Nat.factorial 23 ≤ 23 ^ 23 := Nat.factorial_le_pow 23
      _ ≤ 32 ^ 23 := Nat.pow_le_pow_left (by norm_num) 23
      _ = 2 ^ 115 := by norm_num
  have h2 : (2 : ℝ) ^ (115 : ℕ) ≤ Real.exp 200 := by
    have : (2 : ℝ) ^ (115 : ℕ) ≤ Real.exp 1 ^ (115 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 115
    rw [← Real.exp_nat_mul] at this
    calc (2 : ℝ) ^ (115 : ℕ) ≤ Real.exp ((115 : ℕ) * 1) := this
      _ ≤ Real.exp 200 := Real.exp_le_exp.mpr (by norm_num)
  calc ((Nat.factorial 23 : ℕ) : ℝ) ≤ ((2 ^ 115 : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (2 : ℝ) ^ (115 : ℕ) := by push_cast; ring
    _ ≤ Real.exp 200 := h2

/-- **Large blocks.** -/
theorem norm_block_le_large {τ σ : ℝ} {Y : ℕ} (hL : Real.exp 30 ≤ Real.log τ)
    (hY : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y) (hYτ : τ < (Y : ℝ) ^ 22)
    (hYup : 8 * Real.pi * ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ τ)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) :
    ‖∑ n ∈ Finset.Ico (Y + 1) (2 * Y + 1), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
      2560 := by
  set L := Real.log τ with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hθ := vinogradovKorobovWidth_le hL
  have hθ0 := vinogradovKorobovWidth_pos hL
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hYup
  have hY1 : (1 : ℝ) ≤ ((Y + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg Y : (0:ℝ) ≤ Y)]
  have hY0 : (0 : ℝ) < ((Y + 1 : ℕ) : ℝ) := by linarith
  have hfac : Nat.factorial (24 - 1) ≤ Y + 1 := by
    have h200 : (200 : ℝ) ≤ L ^ ((2 : ℝ) / 3) := by
      have h100 := hundred_le_rpow_third hL
      rw [rpow_two_thirds_eq_sq hL0]
      have := mul_le_mul h100 h100 (by norm_num) (by linarith)
      linarith
    have : ((Nat.factorial 23 : ℕ) : ℝ) ≤ ((Y + 1 : ℕ) : ℝ) := by
      calc ((Nat.factorial 23 : ℕ) : ℝ) ≤ Real.exp 200 := factorial_twentythree_le_exp
        _ ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := Real.exp_le_exp.mpr h200
        _ ≤ Y := hY
        _ ≤ ((Y + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hhigh : τ ≤ 2 * Real.pi * 2 ^ 24 * ((Y + 1 : ℕ) : ℝ) ^ (24 - 1) *
      ((Y + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by
    have h1 : τ ≤ ((Y + 1 : ℕ) : ℝ) ^ 22 := by
      have : (Y : ℝ) ^ 22 ≤ ((Y + 1 : ℕ) : ℝ) ^ 22 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast; linarith) 22
      linarith
    have h2 : ((Y + 1 : ℕ) : ℝ) ^ 22 ≤ ((Y + 1 : ℕ) : ℝ) ^ (24 - 1) *
        ((Y + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by
      rw [← Real.rpow_natCast _ (24 - 1), ← Real.rpow_add hY0, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hY1
      norm_num
    have h3 : (1 : ℝ) ≤ 2 * Real.pi * 2 ^ 24 := by
      have hpi := Real.pi_gt_three
      have h24 : (1 : ℝ) ≤ 2 ^ 24 := one_le_pow₀ (by norm_num)
      have : (1 : ℝ) ≤ 2 * Real.pi := by linarith
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 * Real.pi * 2 ^ 24 := mul_le_mul this h24 (by norm_num) (by positivity)
    have h4 : 0 ≤ ((Y + 1 : ℕ) : ℝ) ^ (24 - 1) * ((Y + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by
      positivity
    calc τ ≤ ((Y + 1 : ℕ) : ℝ) ^ (24 - 1) * ((Y + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := h1.trans h2
      _ ≤ 2 * Real.pi * 2 ^ 24 * (((Y + 1 : ℕ) : ℝ) ^ (24 - 1) *
          ((Y + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) := le_mul_of_one_le_left h4 h3
      _ = _ := by ring
  have hσ0 : 0 ≤ σ := by
    have : vinogradovKorobovWidth L ≤ 1 := hθ.trans (by norm_num)
    linarith
  have h := dirichlet_block_sigma_saving_of_small_factorial hσ0 hτ0 (N := Y + 1) (M := 2 * Y + 1)
    (by omega) (by omega) (by omega) (by norm_num : 2 ≤ 24) hfac hYup hhigh
  refine h.trans ?_
  have hexp : ((Y + 1 : ℕ) : ℝ) ^ (1 - σ) *
      ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24))) ≤ 1 := by
    rw [← Real.rpow_add hY0]
    apply Real.rpow_le_one_of_one_le_of_nonpos hY1
    have : (1 : ℝ) / (3 * (2 : ℝ) ^ 24) = 1 / (3 * (2 : ℝ) ^ (24 : ℕ)) := by norm_num
    linarith
  calc 2560 * ((Y + 1 : ℕ) : ℝ) ^ (1 - σ) * ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24)))
      = 2560 * (((Y + 1 : ℕ) : ℝ) ^ (1 - σ) *
        ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24))))  := by ring
    _ ≤ 2560 * 1 := by gcongr
    _ = 2560 := by ring

/-- **Short initial segment.** `‖Σ_{k ≤ N₀} k^{-w}‖ ≤ e^{1/50}(1 + log N₀)` when
`θ log N₀ ≤ 1/50`. -/
theorem norm_sum_initial_le {σ τ θ : ℝ} {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hθ0 : 0 ≤ θ)
    (hθN : θ * Real.log N₀ ≤ 1 / 50) (hσ1 : 1 - θ ≤ σ) :
    ‖∑ k ∈ Finset.Icc 1 N₀, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      Real.exp (1 / 50) * (1 + Real.log N₀) := by
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast (by omega : 0 < N₀)
  have hterm : ∀ k ∈ Finset.Icc 1 N₀,
      ‖((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤ Real.exp (1 / 50) * (1 / (k : ℝ)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N₀ := (Finset.mem_Icc.mp hk).2
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hk0]
    have hre : (-((σ : ℂ) + (τ : ℂ) * Complex.I)).re = -σ := by simp
    rw [hre]
    have h1 : (k : ℝ) ^ (-σ) ≤ (k : ℝ) ^ (θ - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk1) (by linarith)
    have h2 : (k : ℝ) ^ (θ - 1) = (k : ℝ) ^ θ * (1 / (k : ℝ)) := by
      rw [Real.rpow_sub hk0, Real.rpow_one]; ring
    have h3 : (k : ℝ) ^ θ ≤ Real.exp (1 / 50) := by
      rw [Real.rpow_def_of_pos hk0, Real.exp_le_exp]
      have := Real.log_le_log hk0 (by exact_mod_cast hkN : (k : ℝ) ≤ N₀)
      nlinarith
    calc (k : ℝ) ^ (-σ) ≤ (k : ℝ) ^ θ * (1 / (k : ℝ)) := h1.trans h2.le
      _ ≤ Real.exp (1 / 50) * (1 / (k : ℝ)) := by gcongr
  calc ‖∑ k ∈ Finset.Icc 1 N₀, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖
      ≤ ∑ k ∈ Finset.Icc 1 N₀, ‖((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 N₀, Real.exp (1 / 50) * (1 / (k : ℝ)) := Finset.sum_le_sum hterm
    _ = Real.exp (1 / 50) * (harmonic N₀ : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        push_cast
        simp [one_div]
    _ ≤ Real.exp (1 / 50) * (1 + Real.log N₀) := by
        gcongr
        exact harmonic_le_one_add_log N₀

end

end RHTower.Sieve
