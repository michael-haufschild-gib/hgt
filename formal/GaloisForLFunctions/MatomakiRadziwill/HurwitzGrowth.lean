import GaloisForLFunctions.MatomakiRadziwill.ShiftedVinogradov
import GaloisForLFunctions.MatomakiRadziwill.ShiftedPhaseBlocks
import GaloisForLFunctions.RHTower.Sieve.VinogradovZetaGrowth

/-!
# Vinogradov–Korobov growth of Hurwitz partial sums

For `0 ≤ α ≤ 1`, `L = log τ ≥ e^{30}`, `1 − θ(L) ≤ σ ≤ 2` (`θ` the Vinogradov–Korobov width of
`Sieve.vinogradovKorobovWidth`) and every `K ≤ 2τ²`,

`‖Σ_{k=1}^{K} (k+α)^{-σ-iτ}‖ ≤ C log τ`   (`norm_hurwitzPartial_le`),

with an absolute constant `C`.  As for `ζ` (`Sieve.norm_riemannZeta_le_vinogradovKorobov`): the
segment `k ≤ e^{L^{2/3}}` is bounded termwise, every dyadic block `(Y, 2Y]` costs `O(1)` — by the
shifted Vinogradov estimate when `Y^{22} ≤ τ` (`hurwitz_block_le_middle`) and by the shifted
`24`-th derivative test otherwise (`hurwitz_block_le_large`) — and there are `O(L)` blocks.
-/

open Finset RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- `x^{-iτ}` is the conjugate of `e((τ/2π) log x)` for real `x > 0`. -/
theorem ofReal_cpow_neg_I_mul_eq_conj (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    ((x : ℝ) : ℂ) ^ (-(Complex.I * (τ : ℂ))) =
      starRingEnd ℂ (finitePhaseChar (τ / (2 * Real.pi) * Real.log x)) := by
  rw [ofReal_cpow_neg_I_mul τ hx, ← finitePhaseChar_neg]
  unfold finitePhaseChar logPhase
  congr 1
  push_cast
  ring_nf

/-- `Ico (Y+1) m = Ioc Y (m − 1)`, and the shifted sum of `(n+α)^{-iτ}` is the conjugate of the sum
of shifted phases. -/
theorem norm_sum_Ico_shifted_eq {τ α : ℝ} (hα : 0 ≤ α) {Y m : ℕ} (hm : Y + 1 ≤ m) :
    ‖∑ n ∈ Finset.Ico (Y + 1) m, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(Complex.I * (τ : ℂ)))‖ =
      ‖∑ n ∈ Finset.Ioc Y (Y + (m - 1 - Y)), shiftedLogPhase τ α n‖ := by
  have hset : Finset.Ico (Y + 1) m = Finset.Ioc Y (Y + (m - 1 - Y)) := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
  rw [hset, ← RCLike.norm_conj, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
  have hpos : (0 : ℝ) < (n : ℝ) + α := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  rw [ofReal_cpow_neg_I_mul_eq_conj τ hpos, RCLike.conj_conj, shiftedLogPhase]

/-- **Middle Hurwitz blocks**, `M ≤ 2Y`. -/
theorem hurwitz_block_le_middle_aux {τ σ α : ℝ} {Y M : ℕ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hL : Real.exp 30 ≤ Real.log τ)
    (hY : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y) (hYτ : (Y : ℝ) ^ 22 ≤ τ)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) (hM1 : Y + 1 ≤ M) (hM : M ≤ 2 * Y) :
    ‖∑ n ∈ Finset.Ico (Y + 1) M, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
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
  have hprefix : ∀ m, Y + 1 ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico (Y + 1) m, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(Complex.I * (τ : ℂ)))‖ ≤ Pb := by
    intro m hm1 hm2
    rw [norm_sum_Ico_shifted_eq hα0 hm1]
    have h := norm_sum_shiftedLogPhase_le_dyadic (N := Y) (A := Y) (L := m - 1 - Y) hα0 hα1
      hR22 hY38 hYτ htR hthr le_rfl (by omega)
    refine h.trans ?_
    have hLm : ((m - 1 - Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast (by omega : m - 1 - Y ≤ Y)
    have : (0 : ℝ) ≤ 12 * Real.exp 20 * (Y : ℝ) ^ (-(δ / 4)) := by positivity
    rw [hPb]
    nlinarith
  have hσ0 : 0 ≤ σ := by linarith
  have hsig := shifted_block_sigma_bound hσ0 τ hα0 (Y + 1) M (by omega) hM1 Pb hprefix
  refine hsig.trans ?_
  -- `Pb (Y+1)^{-σ} ≤ 12 e^{21} + 201`
  have hYσ : (((Y + 1 : ℕ) : ℝ) + α) ^ (-σ) ≤ (Y : ℝ) ^ (-σ) :=
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
  calc Pb * (((Y + 1 : ℕ) : ℝ) + α) ^ (-σ) ≤ Pb * (Y : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_left hYσ hPb0
    _ = 12 * Real.exp 20 * ((Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-σ)) +
        200 * ((Y : ℝ) ^ ((1 : ℝ) / 2) * (Y : ℝ) ^ (-σ)) := by rw [hPb]; ring
    _ ≤ 12 * Real.exp 20 * Real.exp 1 + 200 * 1 := by gcongr
    _ ≤ 12 * Real.exp 21 + 201 := by
        rw [show (21 : ℝ) = 20 + 1 by norm_num, Real.exp_add]; linarith


/-- **Large Hurwitz blocks.** -/
theorem hurwitz_block_le_large {τ σ α : ℝ} {Y M : ℕ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hL : Real.exp 30 ≤ Real.log τ)
    (hY : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y) (hYτ : τ < (Y : ℝ) ^ 22)
    (hYup : 8 * Real.pi * ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ τ)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) (hM1 : Y + 1 ≤ M) (hM : M ≤ 2 * Y + 1) :
    ‖∑ n ∈ Finset.Ico (Y + 1) M, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
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
  have h := shifted_block_sigma_saving_of_small_factorial hσ0 hτ0 hα0 hα1 (N := Y + 1) (M := M)
    (by omega) hM1 (by omega) (by norm_num : 2 ≤ 24) hfac hYup hhigh
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


/-- `‖(x)^{-σ-iτ}‖ ≤ 1` for `x ≥ 1`, `σ ≥ 0`. -/
theorem norm_ofReal_cpow_le_one {σ τ x : ℝ} (hσ : 0 ≤ σ) (hx : 1 ≤ x) :
    ‖((x : ℝ) : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  have hre : (-(σ : ℂ) - Complex.I * (τ : ℂ)).re = -σ := by simp
  rw [hre]
  exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)

/-- **Middle Hurwitz blocks**, any `M ≤ 2Y + 1`. -/
theorem hurwitz_block_le_middle {τ σ α : ℝ} {Y M : ℕ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hL : Real.exp 30 ≤ Real.log τ)
    (hY : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y) (hYτ : (Y : ℝ) ^ 22 ≤ τ)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) (hM1 : Y + 1 ≤ M) (hM : M ≤ 2 * Y + 1) :
    ‖∑ n ∈ Finset.Ico (Y + 1) M, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
      12 * Real.exp 21 + 202 := by
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ Y :=
      le_trans (Real.one_le_exp (Real.rpow_nonneg (le_trans (Real.exp_pos _).le hL) _)) hY
    exact_mod_cast this
  have hθ := vinogradovKorobovWidth_le hL
  have hσ0 : 0 ≤ σ := by
    have : vinogradovKorobovWidth (Real.log τ) ≤ 1 := hθ.trans (by norm_num)
    linarith
  rcases Nat.lt_or_ge M (2 * Y + 1) with hlt | hge
  · have h := hurwitz_block_le_middle_aux hα0 hα1 hL hY hYτ hσ1 hM1 (by omega)
    linarith
  · have hMeq : M = 2 * Y + 1 := le_antisymm hM hge
    subst hMeq
    rw [Finset.sum_Ico_succ_top (by omega : Y + 1 ≤ 2 * Y)]
    have h := hurwitz_block_le_middle_aux hα0 hα1 hL hY hYτ hσ1 (M := 2 * Y) (by omega) le_rfl
    have hlast : ‖((((2 * Y : ℕ) : ℝ) + α : ℝ) : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤ 1 :=
      norm_ofReal_cpow_le_one hσ0 (by
        have : (1 : ℝ) ≤ ((2 * Y : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * Y)
        linarith)
    refine (norm_add_le _ _).trans ?_
    linarith

/-- The block constant `B = 12e^{21} + 2762`. -/
def hurwitzBlockConstant : ℝ := 12 * Real.exp 21 + 2762

/-- **Every Hurwitz block** `(Y, M − 1]`, `Y ≥ e^{L^{2/3}}`, `M ≤ 2Y + 1`, `Y < 2τ²`, costs at most
`B`. -/
theorem hurwitz_block_le {τ σ α : ℝ} {Y M : ℕ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hτbig : 2 * (8 * Real.pi) ^ 3 ≤ τ) (hL : Real.exp 30 ≤ Real.log τ)
    (hY : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y) (hYτ2 : ((Y + 1 : ℕ) : ℝ) ≤ 2 * τ ^ 2)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) (hM1 : Y + 1 ≤ M) (hM : M ≤ 2 * Y + 1) :
    ‖∑ n ∈ Finset.Ico (Y + 1) M, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
      hurwitzBlockConstant := by
  unfold hurwitzBlockConstant
  by_cases hmid : (Y : ℝ) ^ 22 ≤ τ
  · have h := hurwitz_block_le_middle hα0 hα1 hL hY hmid hσ1 hM1 hM
    linarith
  · rw [not_le] at hmid
    have hπ : 0 < 8 * Real.pi := by positivity
    have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτbig
    have hYup : 8 * Real.pi * ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ τ := by
      have hY1 : ((Y + 1 : ℕ) : ℝ) ≤ (τ / (8 * Real.pi)) ^ 3 := by
        have h1 : (1 : ℝ) ≤ τ ^ 2 := by
          have h8 : (1 : ℝ) ≤ 8 * Real.pi := by linarith [Real.pi_gt_three]
          have h83 : (1 : ℝ) ≤ (8 * Real.pi) ^ 3 := one_le_pow₀ h8
          have : (1 : ℝ) ≤ τ := le_trans (by linarith) hτbig
          exact one_le_pow₀ this
        have h2 : 2 * τ ^ 2 ≤ (τ / (8 * Real.pi)) ^ 3 := by
          rw [div_pow, le_div_iff₀ (by positivity)]
          have : 2 * (8 * Real.pi) ^ 3 * τ ^ 2 ≤ τ * τ ^ 2 :=
            mul_le_mul_of_nonneg_right hτbig (by positivity)
          nlinarith
        linarith
      have hroot : ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
          ((τ / (8 * Real.pi)) ^ 3) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) hY1 (by norm_num)
      have he : ((τ / (8 * Real.pi)) ^ 3) ^ ((1 : ℝ) / 3) = τ / (8 * Real.pi) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rw [he] at hroot
      calc 8 * Real.pi * ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ 8 * Real.pi * (τ / (8 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hroot hπ.le
        _ = τ := by field_simp
    have h := hurwitz_block_le_large hα0 hα1 hL hY hmid hYup hσ1 hM1 hM
    have : (0 : ℝ) ≤ 12 * Real.exp 21 := by positivity
    linarith

/-- **Short initial segment.** `‖Σ_{1≤k≤K} (k+α)^{-w}‖ ≤ e^{1/50}(1 + log N₀)` for `K ≤ N₀`,
`θ log N₀ ≤ 1/50`, `σ ≥ 1 − θ`. -/
theorem norm_sum_initial_shifted_le {σ τ θ α : ℝ} {K N₀ : ℕ} (hα0 : 0 ≤ α) (hKN : K ≤ N₀)
    (hN₀ : 1 ≤ N₀) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθN : θ * Real.log N₀ ≤ 1 / 50)
    (hσ1 : 1 - θ ≤ σ) :
    ‖∑ k ∈ Finset.Icc 1 K, ((((k : ℝ) + α : ℝ)) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      Real.exp (1 / 50) * (1 + Real.log N₀) := by
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast (by omega : 0 < N₀)
  have hσ0 : 0 ≤ σ := by linarith
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      ‖((((k : ℝ) + α : ℝ)) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
        Real.exp (1 / 50) * (1 / (k : ℝ)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N₀ := le_trans (Finset.mem_Icc.mp hk).2 hKN
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkα : (0 : ℝ) < (k : ℝ) + α := by linarith
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hkα]
    have hre : (-((σ : ℂ) + (τ : ℂ) * Complex.I)).re = -σ := by simp
    rw [hre]
    have h0 : ((k : ℝ) + α) ^ (-σ) ≤ (k : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hk0 (by linarith) (by linarith)
    have h1 : (k : ℝ) ^ (-σ) ≤ (k : ℝ) ^ (θ - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk1) (by linarith)
    have h2 : (k : ℝ) ^ (θ - 1) = (k : ℝ) ^ θ * (1 / (k : ℝ)) := by
      rw [Real.rpow_sub hk0, Real.rpow_one]; ring
    have h3 : (k : ℝ) ^ θ ≤ Real.exp (1 / 50) := by
      rw [Real.rpow_def_of_pos hk0, Real.exp_le_exp]
      have := Real.log_le_log hk0 (by exact_mod_cast hkN : (k : ℝ) ≤ N₀)
      nlinarith
    calc ((k : ℝ) + α) ^ (-σ) ≤ (k : ℝ) ^ θ * (1 / (k : ℝ)) := h0.trans (h1.trans h2.le)
      _ ≤ Real.exp (1 / 50) * (1 / (k : ℝ)) := by gcongr
  calc ‖∑ k ∈ Finset.Icc 1 K, ((((k : ℝ) + α : ℝ)) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖
      ≤ ∑ k ∈ Finset.Icc 1 K, ‖((((k : ℝ) + α : ℝ)) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, Real.exp (1 / 50) * (1 / (k : ℝ)) := Finset.sum_le_sum hterm
    _ = Real.exp (1 / 50) * (harmonic K : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        push_cast
        simp [one_div]
    _ ≤ Real.exp (1 / 50) * (1 + Real.log N₀) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rcases Nat.eq_zero_or_pos K with h0 | hpos
        · have := Real.log_nonneg (show (1:ℝ) ≤ N₀ by exact_mod_cast hN₀)
          rw [h0]
          simp
          linarith
        · have := harmonic_le_one_add_log K
          have hlog : Real.log K ≤ Real.log N₀ :=
            Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hKN)
          linarith

/-- The Hurwitz growth constant `C = 6 + 5B`. -/
def hurwitzGrowthConstant : ℝ := 6 + 5 * hurwitzBlockConstant

theorem hurwitzBlockConstant_nonneg : 0 ≤ hurwitzBlockConstant := by
  unfold hurwitzBlockConstant; positivity

/-- **Vinogradov–Korobov growth of Hurwitz partial sums.** For `τ ≥ e^{e^{30}}`,
`1 − θ(log τ) ≤ σ`, `0 ≤ α ≤ 1` and `K ≤ 2τ²`: `‖Σ_{k=1}^{K} (k+α)^{-σ-iτ}‖ ≤ C log τ`. -/
theorem norm_hurwitzPartial_le {τ σ α : ℝ} (hτ : Real.exp (Real.exp 30) ≤ τ)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {K : ℕ} (hK : (K : ℝ) ≤ 2 * τ ^ 2) :
    ‖∑ k ∈ Finset.Icc 1 K, ((((k : ℝ) + α : ℝ)) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      hurwitzGrowthConstant * Real.log τ := by
  classical
  set f : ℕ → ℂ := fun k => ((((k : ℝ) + α : ℝ)) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))
    with hfdef
  have hτ0 : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hτ
  have hL : Real.exp 30 ≤ Real.log τ := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) hτ
  set L := Real.log τ with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (Real.one_le_exp (by norm_num)) hL
  have hθ0 := vinogradovKorobovWidth_pos hL
  have hθ1 : vinogradovKorobovWidth L ≤ 1 / 100 :=
    (vinogradovKorobovWidth_le hL).trans (by norm_num)
  have hτbig : 2 * (8 * Real.pi) ^ 3 ≤ τ := by
    have h1 : 2 * (8 * Real.pi) ^ 3 ≤ Real.exp 30 := by
      have hpi := Real.pi_lt_d2
      have h2 : Real.exp 30 = Real.exp 1 ^ 30 := by rw [← Real.exp_nat_mul]; norm_num
      have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h3 : (2 : ℝ) ^ 30 ≤ Real.exp 1 ^ 30 := pow_le_pow_left₀ (by norm_num) he 30
      have h4 : (8 * Real.pi) ^ 3 ≤ (8 * 3.15) ^ 3 := pow_le_pow_left₀ (by positivity)
        (by linarith) 3
      rw [h2]; norm_num at h3 h4 ⊢; linarith
    have h2 : Real.exp 30 ≤ τ := le_trans (Real.exp_le_exp.mpr (by
      have := Real.add_one_le_exp (30 : ℝ); linarith)) hτ
    linarith
  -- the initial segment `k ≤ N₀ = ⌈e^{L^{2/3}}⌉`
  set N₀ : ℕ := ⌈Real.exp (L ^ ((2 : ℝ) / 3))⌉₊ with hN₀
  have hN₀low : Real.exp (L ^ ((2 : ℝ) / 3)) ≤ N₀ := Nat.le_ceil _
  have hN₀1 : 1 ≤ N₀ := by
    have : (1 : ℝ) ≤ N₀ := le_trans (Real.one_le_exp (by positivity)) hN₀low
    exact_mod_cast this
  have hlogN₀ : Real.log N₀ ≤ L ^ ((2 : ℝ) / 3) + 1 := by
    have hN₀up : (N₀ : ℝ) < Real.exp (L ^ ((2 : ℝ) / 3)) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h1 : (N₀ : ℝ) ≤ 2 * Real.exp (L ^ ((2 : ℝ) / 3)) := by
      have : (1 : ℝ) ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := Real.one_le_exp (by positivity)
      linarith
    have h2 := Real.log_le_log (by exact_mod_cast hN₀1) h1
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h2
    have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hθN : vinogradovKorobovWidth L * Real.log N₀ ≤ 1 / 50 := by
    have h1 := vinogradovKorobovWidth_mul_le hL
    calc vinogradovKorobovWidth L * Real.log N₀
        ≤ vinogradovKorobovWidth L * (L ^ ((2 : ℝ) / 3) + 1) :=
          mul_le_mul_of_nonneg_left hlogN₀ hθ0.le
      _ = vinogradovKorobovWidth L * L ^ ((2 : ℝ) / 3) + vinogradovKorobovWidth L := by ring
      _ ≤ 1 / 100 + 1 / 100 := add_le_add h1 hθ1
      _ = 1 / 50 := by norm_num
  have hL23 : L ^ ((2 : ℝ) / 3) ≤ L := by
    have h100 := hundred_le_rpow_third hL
    have e : L = L ^ ((1 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_add hL0]; norm_num
    have h0 : 0 ≤ L ^ ((2 : ℝ) / 3) := by positivity
    have : 1 * L ^ ((2 : ℝ) / 3) ≤ L ^ ((1 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right (by linarith) h0
    rw [← e] at this; linarith
  have hinit : ∀ K' : ℕ, K' ≤ N₀ → ‖∑ k ∈ Finset.Icc 1 K', f k‖ ≤ 2 * (2 + L) := by
    intro K' hK'
    have h := norm_sum_initial_shifted_le (τ := τ) hα0 hK' hN₀1 hθ0.le (by linarith) hθN hσ1
    have he : Real.exp (1 / 50) ≤ 2 := by
      have hl2 : (1 / 50 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      calc Real.exp (1 / 50) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hl2
        _ = 2 := Real.exp_log (by norm_num)
    have hlog0 : 0 ≤ 1 + Real.log N₀ := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ N₀ by exact_mod_cast hN₀1); linarith
    calc ‖∑ k ∈ Finset.Icc 1 K', f k‖ ≤ Real.exp (1 / 50) * (1 + Real.log N₀) := h
      _ ≤ 2 * (1 + Real.log N₀) := mul_le_mul_of_nonneg_right he hlog0
      _ ≤ 2 * (2 + L) := by linarith
  have hB0 := hurwitzBlockConstant_nonneg
  have hC : 2 * (2 + L) ≤ hurwitzGrowthConstant * L := by
    unfold hurwitzGrowthConstant
    nlinarith
  rcases le_or_gt K N₀ with hKN | hKN
  · exact (hinit K hKN).trans hC
  -- the dyadic blocks above `N₀`
  have hex : ∃ J : ℕ, K ≤ N₀ * 2 ^ J := ⟨K, by
    have h1 : K < 2 ^ K := Nat.lt_two_pow_self
    have h2 : 2 ^ K ≤ N₀ * 2 ^ K := Nat.le_mul_of_pos_left _ (by omega)
    omega⟩
  set J := Nat.find hex with hJdef
  have hJspec : K ≤ N₀ * 2 ^ J := Nat.find_spec hex
  have hJmin : ∀ r < J, N₀ * 2 ^ r < K := fun r hr => by
    have := Nat.find_min hex hr
    omega
  have hJpos : 1 ≤ J := by
    by_contra h
    have hJ0 : J = 0 := by omega
    rw [hJ0, pow_zero, mul_one] at hJspec
    omega
  have hJbound : (J : ℝ) ≤ 3 * L + 2 := by
    have h := hJmin (J - 1) (by omega)
    have h2 : ((2 : ℝ) ^ (J - 1)) < 2 * τ ^ 2 := by
      have hN : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
      have hc : ((N₀ * 2 ^ (J - 1) : ℕ) : ℝ) < K := by exact_mod_cast h
      push_cast at hc
      have : (0 : ℝ) < 2 ^ (J - 1) := by positivity
      nlinarith
    have hlog := Real.log_lt_log (by positivity) h2
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
    have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hl2' : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
    have hJ1 : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by rw [Nat.cast_sub hJpos]; norm_num
    rw [hJ1] at hlog
    push_cast at hlog
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) - 1 := by
      have : (1 : ℝ) ≤ J := by exact_mod_cast hJpos
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hl2 hJ0]
  have hsplit : ∑ k ∈ Finset.Icc 1 K, f k = ∑ k ∈ Finset.Icc 1 N₀, f k + ∑ k ∈ Finset.Ioc N₀ K, f k := by
    have h1 : Finset.Icc 1 K = Finset.Ioc 0 K := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have h2 : Finset.Icc 1 N₀ = Finset.Ioc 0 N₀ := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [h1, h2, Finset.sum_Ioc_consecutive f (Nat.zero_le N₀) hKN.le]
  set g : ℕ → ℂ := fun n => if n ≤ K then f n else 0 with hgdef
  have hgsum : ∑ k ∈ Finset.Ioc N₀ K, f k = ∑ k ∈ Finset.Ioc N₀ (N₀ * 2 ^ J), g k := by
    rw [hgdef, ← Finset.sum_filter]
    congr 1
    ext n; simp only [Finset.mem_filter, Finset.mem_Ioc]; omega
  have hblock : ∀ r ∈ Finset.range J,
      ‖∑ k ∈ Finset.Ioc (N₀ * 2 ^ r) (N₀ * 2 ^ (r + 1)), g k‖ ≤ hurwitzBlockConstant := by
    intro r hr
    have hrJ := Finset.mem_range.mp hr
    set Y := N₀ * 2 ^ r with hY
    have hYK : Y < K := hJmin r hrJ
    have hY2 : N₀ * 2 ^ (r + 1) = 2 * Y := by rw [hY, pow_succ]; ring
    rw [hY2]
    have hconv : ∑ k ∈ Finset.Ioc Y (2 * Y), g k =
        ∑ n ∈ Finset.Ico (Y + 1) (min K (2 * Y) + 1),
          ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ)) := by
      rw [hgdef, ← Finset.sum_filter]
      have hset : (Finset.Ioc Y (2 * Y)).filter (fun n => n ≤ K) =
          Finset.Ico (Y + 1) (min K (2 * Y) + 1) := by
        ext n; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]; omega
      rw [hset]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hfdef]
      congr 1
      ring
    rw [hconv]
    have hYlow : Real.exp (L ^ ((2 : ℝ) / 3)) ≤ Y := by
      have : (N₀ : ℝ) ≤ Y := by
        rw [hY]; push_cast
        exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ (by norm_num))
      linarith
    have hYτ2 : ((Y + 1 : ℕ) : ℝ) ≤ 2 * τ ^ 2 := by
      have : Y + 1 ≤ K := hYK
      have h' : ((Y + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast this
      linarith
    exact hurwitz_block_le hα0 hα1 hτbig hL hYlow hYτ2 hσ1 (by omega) (by omega)
  have hdy := norm_sum_Ioc_dyadic_le N₀ g J
  have hblocks : ‖∑ k ∈ Finset.Ioc N₀ K, f k‖ ≤ J * hurwitzBlockConstant := by
    rw [hgsum]
    refine hdy.trans ?_
    calc ∑ r ∈ Finset.range J, ‖∑ k ∈ Finset.Ioc (N₀ * 2 ^ r) (N₀ * 2 ^ (r + 1)), g k‖
        ≤ ∑ _r ∈ Finset.range J, hurwitzBlockConstant := Finset.sum_le_sum hblock
      _ = J * hurwitzBlockConstant := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsplit]
  calc ‖∑ k ∈ Finset.Icc 1 N₀, f k + ∑ k ∈ Finset.Ioc N₀ K, f k‖
      ≤ 2 * (2 + L) + J * hurwitzBlockConstant :=
        (norm_add_le _ _).trans (add_le_add (hinit N₀ le_rfl) hblocks)
    _ ≤ 2 * (2 + L) + (3 * L + 2) * hurwitzBlockConstant :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hJbound hB0)
    _ ≤ hurwitzGrowthConstant * L := by
        unfold hurwitzGrowthConstant
        nlinarith

end

end GaloisForLFunctions.MatomakiRadziwill
