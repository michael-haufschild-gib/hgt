import GaloisForLFunctions.RHTower.Sieve.VinogradovZetaGrowthBlocks
import GaloisForLFunctions.RHTower.Sieve.ZetaPartialSumTruncation
import GaloisForLFunctions.RHTower.Sieve.RouteTHybridZetaAssembly

/-!
# The Vinogradov–Korobov growth bound for `ζ`

For `τ ≥ exp(exp 30)`, `L = log τ` and `1 - θ(L) ≤ σ ≤ 2`, `θ(L) = L^{-2/3}(log L)^{-2/3}/100`,

`‖ζ(σ + iτ)‖ ≤ C L`

with an absolute constant `C` (`norm_riemannZeta_le_vinogradovKorobov`).

Proof: truncate at `X = N₀ 2^J ∈ [τ², 2τ²]`, `N₀ = ⌈e^{L^{2/3}}⌉`, `J` minimal
(`norm_riemannZeta_le_partialSum`).  The segment `k ≤ N₀` costs `e^{1/50}(1 + log N₀)`; each of the
`J ≤ 3L + 1` dyadic blocks `(Y, 2Y]` costs at most `12e^{21} + 2761`: Vinogradov's estimate when
`Y^{22} ≤ τ` (`norm_block_le_middle`), the `24`-th derivative test otherwise
(`norm_block_le_large`).
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The block constant `B = 12e^{21} + 2761`. -/
def vinogradovKorobovBlockConstant : ℝ := 12 * Real.exp 21 + 2761

/-- The growth constant `C = 11 + 4B`. -/
def vinogradovKorobovGrowthConstant : ℝ := 11 + 4 * vinogradovKorobovBlockConstant

theorem sum_Icc_one_eq_initial_add_dyadic (f : ℕ → ℂ) (N₀ J : ℕ) :
    ∑ k ∈ Finset.Icc 1 (N₀ * 2 ^ J), f k =
      ∑ k ∈ Finset.Icc 1 N₀, f k + ∑ k ∈ Finset.Ioc N₀ (N₀ * 2 ^ J), f k := by
  have h1 : Finset.Icc 1 (N₀ * 2 ^ J) = Finset.Ioc 0 (N₀ * 2 ^ J) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have h2 : Finset.Icc 1 N₀ = Finset.Ioc 0 N₀ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hle : N₀ ≤ N₀ * 2 ^ J := Nat.le_mul_of_pos_right _ (by positivity)
  rw [h1, h2, Finset.sum_Ioc_consecutive f (Nat.zero_le N₀) hle]

theorem block_sum_eq_Ico (σ τ : ℝ) (Y : ℕ) :
    ∑ k ∈ Finset.Ioc Y (Y * 2), ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)) =
      ∑ n ∈ Finset.Ico (Y + 1) (2 * Y + 1), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ)) := by
  have hset : Finset.Ioc Y (Y * 2) = Finset.Ico (Y + 1) (2 * Y + 1) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.ofReal_natCast]
  congr 1
  ring

/-- First tail: `X^{1-σ}/‖w-1‖ ≤ 1`. -/
theorem vk_tail_one {τ σ θ : ℝ} {X : ℕ} (hτ : 1 ≤ τ) (hθ0 : 0 ≤ θ)
    (hθL : θ * (1 + 2 * Real.log τ) ≤ Real.log τ) (hσ1 : 1 - θ ≤ σ) (hX1 : 1 ≤ X)
    (hXup : (X : ℝ) ≤ 2 * τ ^ 2) :
    (X : ℝ) ^ (1 - σ) / ‖(σ : ℂ) + (τ : ℂ) * Complex.I - 1‖ ≤ 1 := by
  have hτ0 : 0 < τ := by linarith
  have hnorm : τ ≤ ‖(σ : ℂ) + (τ : ℂ) * Complex.I - 1‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)
    rw [show ((σ : ℂ) + (τ : ℂ) * Complex.I - 1).im = τ by simp, abs_of_pos hτ0] at this
    exact this
  rw [div_le_one (lt_of_lt_of_le hτ0 hnorm)]
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  calc (X : ℝ) ^ (1 - σ) ≤ (X : ℝ) ^ θ := Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)
    _ ≤ (2 * τ ^ 2) ^ θ := Real.rpow_le_rpow (by positivity) hXup hθ0
    _ ≤ τ := by
        rw [Real.rpow_def_of_pos (by positivity)]
        conv_rhs => rw [← Real.exp_log hτ0]
        apply Real.exp_le_exp.mpr
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
        push_cast
        have hlogτ : 0 ≤ Real.log τ := Real.log_nonneg hτ
        calc (Real.log 2 + 2 * Real.log τ) * θ ≤ (1 + 2 * Real.log τ) * θ :=
              mul_le_mul_of_nonneg_right (by linarith) hθ0
          _ = θ * (1 + 2 * Real.log τ) := by ring
          _ ≤ Real.log τ := hθL
    _ ≤ _ := hnorm

/-- Second tail: `‖w‖ X^{-σ}/σ ≤ 4`. -/
theorem vk_tail_two {τ σ : ℝ} {X : ℕ} (hτ : 4 ≤ τ) (hσ0 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2)
    (hXlow : τ ^ 2 ≤ (X : ℝ)) :
    ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ * ((X : ℝ) ^ (-σ) / σ) ≤ 4 := by
  have hτ0 : 0 < τ := by linarith
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσ0
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by positivity) hXlow
  have hX1 : (1 : ℝ) ≤ X := le_trans (by nlinarith) hXlow
  have hwn : ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ≤ 2 + τ := by
    calc ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(τ : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |σ| + |τ| := by simp
      _ ≤ 2 + τ := by rw [abs_of_pos hτ0, abs_of_pos hσpos]; linarith
  have hXσ : (X : ℝ) ^ (-σ) ≤ 1 / τ := by
    calc (X : ℝ) ^ (-σ) ≤ (X : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ ≤ (τ ^ 2) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hXlow (by norm_num)
      _ = 1 / τ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hτ0.le,
            show ((2 : ℕ) : ℝ) * -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one, one_div]
  have hσ' : 1 / σ ≤ 2 := by
    calc 1 / σ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hσ0
      _ = 2 := by norm_num
  have hq : (X : ℝ) ^ (-σ) / σ ≤ (1 / τ) * 2 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hXσ hσ' (by positivity) (by positivity)
  calc ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ * ((X : ℝ) ^ (-σ) / σ) ≤ (2 + τ) * ((1 / τ) * 2) :=
        mul_le_mul hwn hq (div_nonneg (Real.rpow_nonneg hX0.le _) hσpos.le) (by positivity)
    _ = 4 / τ + 2 := by field_simp; ring
    _ ≤ 4 := by
        have : 4 / τ ≤ 2 := by rw [div_le_iff₀ hτ0]; linarith
        linarith

/-- The dyadic part: `J` blocks, each at most `B`. -/
theorem vk_dyadic_le {τ σ : ℝ} {N₀ J : ℕ} (hτbig : 2 * (8 * Real.pi) ^ 3 ≤ τ)
    (hL : Real.exp 30 ≤ Real.log τ)
    (hN₀ : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ N₀)
    (hJmin : ∀ r < J, (N₀ : ℝ) * 2 ^ r < τ ^ 2)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) :
    ‖∑ k ∈ Finset.Ioc N₀ (N₀ * 2 ^ J), ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      J * vinogradovKorobovBlockConstant := by
  have hdy := norm_sum_Ioc_dyadic_le N₀
    (fun k : ℕ => ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))) J
  refine hdy.trans ?_
  have hblock : ∀ r ∈ Finset.range J,
      ‖∑ k ∈ Finset.Ioc (N₀ * 2 ^ r) (N₀ * 2 ^ (r + 1)),
        ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤ vinogradovKorobovBlockConstant := by
    intro r hr
    have hrJ := Finset.mem_range.mp hr
    set Y := N₀ * 2 ^ r with hY
    have hY2 : N₀ * 2 ^ (r + 1) = Y * 2 := by rw [hY, pow_succ]; ring
    rw [hY2, block_sum_eq_Ico]
    have hYlow : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y := by
      have : (N₀ : ℝ) ≤ Y := by
        rw [hY]; push_cast
        exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ (by norm_num))
      linarith
    have hYτ2 : (Y : ℝ) < τ ^ 2 := by rw [hY]; push_cast; exact hJmin r hrJ
    unfold vinogradovKorobovBlockConstant
    by_cases hmid : (Y : ℝ) ^ 22 ≤ τ
    · have h := norm_block_le_middle hL hYlow hmid hσ1
      have : (0 : ℝ) ≤ 2560 := by norm_num
      linarith
    · push Not at hmid
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
          push_cast
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
      have h := norm_block_le_large hL hYlow hmid hYup hσ1
      have : (0 : ℝ) ≤ 12 * Real.exp 21 := by positivity
      linarith
  calc ∑ r ∈ Finset.range J, ‖∑ k ∈ Finset.Ioc (N₀ * 2 ^ r) (N₀ * 2 ^ (r + 1)),
        ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖
      ≤ ∑ _r ∈ Finset.range J, vinogradovKorobovBlockConstant := Finset.sum_le_sum hblock
    _ = J * vinogradovKorobovBlockConstant := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-- The initial segment for `N₀ = ⌈e^{L^{2/3}}⌉`: at most `2(2 + L)`. -/
theorem vk_initial_le {τ σ : ℝ} (hL : Real.exp 30 ≤ Real.log τ)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) :
    ‖∑ k ∈ Finset.Icc 1 ⌈Real.exp (Real.log τ ^ ((2 : ℝ) / 3))⌉₊,
        ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤ 2 * (2 + Real.log τ) := by
  set L := Real.log τ with hLdef
  set N₀ : ℕ := ⌈Real.exp (L ^ ((2 : ℝ) / 3))⌉₊ with hN₀
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hθ0 := vinogradovKorobovWidth_pos hL
  have hN₀low : Real.exp (L ^ ((2 : ℝ) / 3)) ≤ N₀ := Nat.le_ceil _
  have hN₀up : (N₀ : ℝ) < Real.exp (L ^ ((2 : ℝ) / 3)) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hN₀1 : 1 ≤ N₀ := by
    have : (1 : ℝ) ≤ N₀ := le_trans (Real.one_le_exp (by positivity)) hN₀low
    exact_mod_cast this
  have hlogN₀ : Real.log N₀ ≤ L ^ ((2 : ℝ) / 3) + 1 := by
    have h1 : (N₀ : ℝ) ≤ 2 * Real.exp (L ^ ((2 : ℝ) / 3)) := by
      have : (1 : ℝ) ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := Real.one_le_exp (by positivity)
      linarith
    have h2 := Real.log_le_log (by exact_mod_cast hN₀1) h1
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h2
    have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hθN : vinogradovKorobovWidth L * Real.log N₀ ≤ 1 / 50 := by
    have h1 := vinogradovKorobovWidth_mul_le hL
    have hθ1 : vinogradovKorobovWidth L ≤ 1 / 100 :=
      (vinogradovKorobovWidth_le hL).trans (by norm_num)
    calc vinogradovKorobovWidth L * Real.log N₀
        ≤ vinogradovKorobovWidth L * (L ^ ((2 : ℝ) / 3) + 1) :=
          mul_le_mul_of_nonneg_left hlogN₀ hθ0.le
      _ = vinogradovKorobovWidth L * L ^ ((2 : ℝ) / 3) + vinogradovKorobovWidth L := by ring
      _ ≤ 1 / 100 + 1 / 100 := add_le_add h1 hθ1
      _ = 1 / 50 := by norm_num
  have h := norm_sum_initial_le (τ := τ) hN₀1 hθ0.le hθN hσ1
  have he : Real.exp (1 / 50) ≤ 2 := by
    have hl2 : (1 / 50 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    calc Real.exp (1 / 50) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hl2
      _ = 2 := Real.exp_log (by norm_num)
  have h100 := hundred_le_rpow_third hL
  have hL23 : L ^ ((2 : ℝ) / 3) ≤ L := by
    have e : L = L ^ ((1 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_add hL0]; norm_num
    have h0 : 0 ≤ L ^ ((2 : ℝ) / 3) := by positivity
    have : 1 * L ^ ((2 : ℝ) / 3) ≤ L ^ ((1 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right (by linarith) h0
    rw [← e] at this; linarith
  have hlog0 : 0 ≤ 1 + Real.log N₀ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N₀ by exact_mod_cast hN₀1); linarith
  calc _ ≤ Real.exp (1 / 50) * (1 + Real.log N₀) := h
    _ ≤ 2 * (1 + Real.log N₀) := mul_le_mul_of_nonneg_right he hlog0
    _ ≤ 2 * (2 + L) := by linarith

/-- **The Vinogradov–Korobov growth bound.** -/
theorem norm_riemannZeta_le_vinogradovKorobov {τ σ : ℝ} (hτ : Real.exp (Real.exp 30) ≤ τ)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) (hσ2 : σ ≤ 2) :
    ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      vinogradovKorobovGrowthConstant * Real.log τ := by
  classical
  have hτ0 : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hτ
  have hL : Real.exp 30 ≤ Real.log τ := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) hτ
  have hL0 : 0 < Real.log τ := lt_of_lt_of_le (Real.exp_pos _) hL
  have hL1 : (1 : ℝ) ≤ Real.log τ := le_trans (Real.one_le_exp (by norm_num)) hL
  have hθ0 := vinogradovKorobovWidth_pos hL
  have hθsmall := vinogradovKorobovWidth_le hL
  have hθ1 : vinogradovKorobovWidth (Real.log τ) ≤ 1 / 100 := hθsmall.trans (by norm_num)
  have hσ0 : 1 / 2 ≤ σ := by linarith
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
  have hτ4 : (4 : ℝ) ≤ τ := by
    have hpi := Real.pi_gt_three
    have h8 : (1 : ℝ) ≤ 8 * Real.pi := by linarith
    have h83 : 8 * Real.pi ≤ (8 * Real.pi) ^ 3 := le_self_pow₀ h8 (by norm_num)
    linarith
  set N₀ : ℕ := ⌈Real.exp (Real.log τ ^ ((2 : ℝ) / 3))⌉₊ with hN₀
  have hN₀low : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ N₀ := Nat.le_ceil _
  have hN₀1 : 1 ≤ N₀ := by
    have : (1 : ℝ) ≤ N₀ := le_trans (Real.one_le_exp (by positivity)) hN₀low
    exact_mod_cast this
  have hN₀τ2 : (N₀ : ℝ) ≤ 2 * τ ^ 2 := by
    have hN₀up : (N₀ : ℝ) < Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h100 := hundred_le_rpow_third hL
    have hL23 : Real.log τ ^ ((2 : ℝ) / 3) ≤ Real.log τ := by
      have e : Real.log τ = Real.log τ ^ ((1 : ℝ) / 3) * Real.log τ ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_add hL0]; norm_num
      have h0 : 0 ≤ Real.log τ ^ ((2 : ℝ) / 3) := by positivity
      have : 1 * Real.log τ ^ ((2 : ℝ) / 3) ≤
          Real.log τ ^ ((1 : ℝ) / 3) * Real.log τ ^ ((2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right (by linarith) h0
      rw [← e] at this; linarith
    have h1 : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ τ := by
      calc Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Real.exp (Real.log τ) := Real.exp_le_exp.mpr hL23
        _ = τ := Real.exp_log hτ0
    nlinarith
  -- the number of blocks
  have hex : ∃ J : ℕ, τ ^ 2 ≤ (N₀ : ℝ) * 2 ^ J := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (τ ^ 2) (by norm_num : (1 : ℝ) < 2)
    refine ⟨J, le_trans hJ.le ?_⟩
    have : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
    have : (0 : ℝ) < 2 ^ J := by positivity
    nlinarith
  set J := Nat.find hex with hJdef
  have hJspec : τ ^ 2 ≤ (N₀ : ℝ) * 2 ^ J := Nat.find_spec hex
  have hJmin : ∀ r < J, (N₀ : ℝ) * 2 ^ r < τ ^ 2 := fun r hr => by
    have := Nat.find_min hex hr
    push Not at this
    exact this
  set X : ℕ := N₀ * 2 ^ J with hXdef
  have hXlow : τ ^ 2 ≤ (X : ℝ) := by rw [hXdef]; push_cast; exact hJspec
  have hXup : (X : ℝ) ≤ 2 * τ ^ 2 := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [hXdef, h0]; push_cast; linarith
    · have h := hJmin (J - 1) (by omega)
      have e2 : (2 : ℝ) ^ J = 2 * 2 ^ (J - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hXdef]; push_cast; rw [e2]
      nlinarith
  have hX1 : 1 ≤ X := le_trans hN₀1 (Nat.le_mul_of_pos_right _ (by positivity))
  have hJbound : (J : ℝ) ≤ 3 * Real.log τ + 1 := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [h0]; push_cast; linarith
    · have h := hJmin (J - 1) (by omega)
      have h2 : (2 : ℝ) ^ (J - 1) < τ ^ 2 := by
        have : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
        have : (0 : ℝ) < 2 ^ (J - 1) := by positivity
        nlinarith
      have hlog := Real.log_lt_log (by positivity) h2
      rw [Real.log_pow, Real.log_pow] at hlog
      have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have hJ1 : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [hJ1] at hlog
      push_cast at hlog
      have hJ0 : (0 : ℝ) ≤ (J : ℝ) - 1 := by
        have : (1 : ℝ) ≤ J := by exact_mod_cast hpos
        linarith
      nlinarith
  -- truncation and the four pieces
  have hwne : (σ : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hre : ((σ : ℂ) + (τ : ℂ) * Complex.I).re = σ := by simp
  have htrunc := norm_riemannZeta_le_partialSum (w := (σ : ℂ) + (τ : ℂ) * Complex.I)
    (by rw [hre]; linarith) hwne hX1
  rw [hre] at htrunc
  have ht1 := vk_tail_one (τ := τ) (σ := σ) (θ := vinogradovKorobovWidth (Real.log τ)) (X := X)
    (by linarith) hθ0.le (by nlinarith) hσ1 hX1 hXup
  have ht2 := vk_tail_two (τ := τ) (σ := σ) (X := X) hτ4 hσ0 hσ2 hXlow
  have hsplit := sum_Icc_one_eq_initial_add_dyadic
    (fun k : ℕ => ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))) N₀ J
  have hinit := vk_initial_le (τ := τ) (σ := σ) hL hσ1
  have hdy := vk_dyadic_le (σ := σ) (N₀ := N₀) (J := J) hτbig hL hN₀low hJmin hσ1
  have hsum : ‖∑ k ∈ Finset.Icc 1 X, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      2 * (2 + Real.log τ) + J * vinogradovKorobovBlockConstant := by
    rw [hXdef, hsplit]
    exact (norm_add_le _ _).trans (add_le_add hinit hdy)
  have hB : 0 ≤ vinogradovKorobovBlockConstant := by
    unfold vinogradovKorobovBlockConstant; positivity
  have hJB : (J : ℝ) * vinogradovKorobovBlockConstant ≤
      (3 * Real.log τ + 1) * vinogradovKorobovBlockConstant :=
    mul_le_mul_of_nonneg_right hJbound hB
  calc ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
      ≤ ‖∑ k ∈ Finset.Icc 1 X, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ +
          (X : ℝ) ^ (1 - σ) / ‖(σ : ℂ) + (τ : ℂ) * Complex.I - 1‖ +
          ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ * ((X : ℝ) ^ (-σ) / σ) := htrunc
    _ ≤ (2 * (2 + Real.log τ) + (3 * Real.log τ + 1) * vinogradovKorobovBlockConstant) + 1 + 4 := by
        gcongr
        exact hsum.trans (by linarith)
    _ ≤ vinogradovKorobovGrowthConstant * Real.log τ := by
        unfold vinogradovKorobovGrowthConstant
        nlinarith

end

end RHTower.Sieve
