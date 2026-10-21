import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovZeroFree
import GaloisForLFunctions.RHTower.XiZeroShortWeightDyadic

/-!
# The Vinogradov–Korobov width against the surrogate `(log T)^{-5/7}`

The Vinogradov–Korobov region excludes zeros of `ζ` with

`β > 1 - (log γ)^{-2/3} (log log γ)^{-5/3} / 10⁸`.

Short-interval applications only need a width of the shape `c (log T)^{-5/7}`, and the exponents
obey `2/3 < 5/7`, so the surrogate

`w(T) = (max 1 (log T))^{-5/7} / 10¹²`

is dominated by the true width at every height `γ` with `log γ ∈ [log T, 2 log T]`: writing
`L = log T`, the loss `(log log γ)^{-5/3} ≥ (1 + log L)^{-2}` and the gain `L^{5/7 - 2/3} = L^{1/21}`
beat each other by `(1 + log L)² ≤ 4096 L^{1/21}`.

Consequently every zero of `ξ` in the height box `T ≤ γ ≤ 2T` has `β ≤ 1 - w(T)` for `T` large
(`exists_zeroHeightBox_zeroFree_fiveSevenths`).  Everything here is unconditional.
-/

set_option autoImplicit false

namespace RHTower

noncomputable section

open Complex

/-- The surrogate zero-free width `w(T) = (max 1 (log T))^{-5/7} / 10¹²`. -/
def vinogradovKorobovSurrogateWidth (T : ℝ) : ℝ :=
  (max 1 (Real.log T)) ^ (-(5 : ℝ) / 7) / 10 ^ 12

theorem vinogradovKorobovSurrogateWidth_pos (T : ℝ) : 0 < vinogradovKorobovSurrogateWidth T := by
  have h : (0 : ℝ) < max 1 (Real.log T) := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [vinogradovKorobovSurrogateWidth]
  positivity

theorem vinogradovKorobovSurrogateWidth_nonneg (T : ℝ) :
    0 ≤ vinogradovKorobovSurrogateWidth T :=
  (vinogradovKorobovSurrogateWidth_pos T).le

/-- The surrogate is antitone above `1`. -/
theorem vinogradovKorobovSurrogateWidth_antitone {T T' : ℝ} (hT : 1 ≤ T) (hTT' : T ≤ T') :
    vinogradovKorobovSurrogateWidth T' ≤ vinogradovKorobovSurrogateWidth T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog : Real.log T ≤ Real.log T' := Real.log_le_log hT0 hTT'
  have hmax : max 1 (Real.log T) ≤ max 1 (Real.log T') := max_le_max le_rfl hlog
  have h1 : (0 : ℝ) < max 1 (Real.log T) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hpow := Real.rpow_le_rpow_of_nonpos h1 hmax (by norm_num : -(5 : ℝ) / 7 ≤ 0)
  rw [vinogradovKorobovSurrogateWidth, vinogradovKorobovSurrogateWidth]
  linarith

/-- `(max 1 (log T))^{-5/7} = (log T)^{-5/7}` once `log T ≥ 1`. -/
theorem vinogradovKorobovSurrogateWidth_eq {T : ℝ} (hT : 1 ≤ Real.log T) :
    vinogradovKorobovSurrogateWidth T = Real.log T ^ (-(5 : ℝ) / 7) / 10 ^ 12 := by
  rw [vinogradovKorobovSurrogateWidth, max_eq_right hT]

/-- **The width comparison.**  For `L ≥ e` and `L ≤ M ≤ 2L`,

`L^{-5/7}/10¹² ≤ M^{-2/3} (log M)^{-5/3}/10⁸`.

The surrogate therefore never exceeds the Vinogradov–Korobov width at a height whose logarithm is
`M`.  Proof: `M^{-2/3} ≥ L^{-2/3}/2`, `(log M)^{-5/3} ≥ (1 + log L)^{-2}`, and
`(1 + log L)² ≤ 4096 L^{1/21}` with `L^{-5/7} = L^{-2/3} L^{-1/21}`. -/
theorem surrogate_le_vinogradovKorobov_width {L M : ℝ} (hL : Real.exp 1 ≤ L) (hLM : L ≤ M)
    (hM : M ≤ 2 * L) :
    L ^ (-(5 : ℝ) / 7) / 10 ^ 12 ≤ M ^ (-(2 : ℝ) / 3) * Real.log M ^ (-(5 : ℝ) / 3) / 10 ^ 8 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hL2 : (2 : ℝ) ≤ L := le_trans he hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogM1 : (1 : ℝ) ≤ Real.log M := by
    rw [Real.le_log_iff_exp_le hM0]
    linarith
  -- `(log M)^{-5/3} ≥ (1 + log L)^{-2} = 1/(1 + log L)²`
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogMup : Real.log M ≤ 1 + Real.log L := by
    have h := Real.log_le_log (by linarith) hM
    rw [Real.log_mul (by norm_num) hL0.ne'] at h
    linarith
  have hb1 : (1 : ℝ) ≤ 1 + Real.log L := by linarith
  have hstep1 : (1 + Real.log L) ^ (-(5 : ℝ) / 3) ≤ Real.log M ^ (-(5 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hlogMup (by norm_num)
  have hstep2 : (1 + Real.log L) ^ (-(2 : ℝ)) ≤ (1 + Real.log L) ^ (-(5 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
  have hsq : (1 + Real.log L) ^ (-(2 : ℝ)) = 1 / (1 + Real.log L) ^ 2 := by
    rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  have hlogMpow : 1 / (1 + Real.log L) ^ 2 ≤ Real.log M ^ (-(5 : ℝ) / 3) := by
    rw [← hsq]; linarith
  -- `M^{-2/3} ≥ L^{-2/3}/2`
  have h2L : (2 * L) ^ (-(2 : ℝ) / 3) ≤ M ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hM0 hM (by norm_num)
  have htwo : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (-(2 : ℝ) / 3) := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num)
      (show (-1 : ℝ) ≤ -(2 : ℝ) / 3 by norm_num)
    rwa [show (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 by
      rw [Real.rpow_neg_one]; norm_num] at h
  have hLpow : (0 : ℝ) < L ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hL0 _
  have hhalf : L ^ (-(2 : ℝ) / 3) / 2 ≤ M ^ (-(2 : ℝ) / 3) := by
    refine le_trans ?_ h2L
    rw [Real.mul_rpow (by norm_num) hL0.le]
    have := mul_le_mul_of_nonneg_right htwo hLpow.le
    linarith
  -- split `L^{-5/7} = L^{-2/3} L^{-1/21}` and compare the logarithmic factor
  have hsplit : L ^ (-(5 : ℝ) / 7) = L ^ (-(2 : ℝ) / 3) * L ^ (-(1 : ℝ) / 21) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hinv : L ^ (-(1 : ℝ) / 21) = 1 / L ^ ((1 : ℝ) / 21) := by
    rw [show -(1 : ℝ) / 21 = -((1 : ℝ) / 21) by ring, Real.rpow_neg hL0.le]
    ring
  have hapow : (0 : ℝ) < L ^ ((1 : ℝ) / 21) := Real.rpow_pos_of_pos hL0 _
  have hlogbd : (1 + Real.log L) ^ 2 ≤ 4096 * L ^ ((1 : ℝ) / 21) := by
    have h := one_add_log_pow_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 21) (by linarith : (1 : ℝ) ≤ L)
    norm_num at h
    linarith
  -- assemble
  have hkey : L ^ (-(1 : ℝ) / 21) / 10 ^ 12 ≤ 1 / (2 * (1 + Real.log L) ^ 2 * 10 ^ 8) := by
    rw [hinv, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq0 : (0 : ℝ) < (1 + Real.log L) ^ 2 := by positivity
    nlinarith [hlogbd, hapow]
  have hpos2 : (0 : ℝ) < 2 * (1 + Real.log L) ^ 2 * 10 ^ 8 := by positivity
  calc L ^ (-(5 : ℝ) / 7) / 10 ^ 12
      = L ^ (-(2 : ℝ) / 3) * (L ^ (-(1 : ℝ) / 21) / 10 ^ 12) := by rw [hsplit]; ring
    _ ≤ L ^ (-(2 : ℝ) / 3) * (1 / (2 * (1 + Real.log L) ^ 2 * 10 ^ 8)) :=
        mul_le_mul_of_nonneg_left hkey hLpow.le
    _ = (L ^ (-(2 : ℝ) / 3) / 2) * (1 / (1 + Real.log L) ^ 2) / 10 ^ 8 := by
        field_simp
    _ ≤ M ^ (-(2 : ℝ) / 3) * Real.log M ^ (-(5 : ℝ) / 3) / 10 ^ 8 := by
        have hMpow : (0 : ℝ) ≤ M ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hM0.le _
        have := mul_le_mul hhalf hlogMpow (by positivity) hMpow
        linarith

/-- **The surrogate zero-free region on height boxes.**  For `T` large, every zero of `ξ` with
ordinate in `[T, 2T]` has real part at most `1 - w(T)`. -/
theorem exists_zeroHeightBox_zeroFree_fiveSevenths :
    ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T → ∀ σ : ℝ, (zeroHeightBox σ T).Nonempty →
      σ ≤ 1 - vinogradovKorobovSurrogateWidth T := by
  obtain ⟨γ₀, hγ₀⟩ := Sieve.riemannZeta_ne_zero_vinogradovKorobov
  refine ⟨max (max γ₀ 1) (Real.exp (Real.exp 1)), le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩
  intro T hT σ ⟨q, hσ, hγ1, hγ2⟩
  have hTγ₀ : γ₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTe : Real.exp (Real.exp 1) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  set β := (q.1 : ℂ).re with hβ
  set γ := (q.1 : ℂ).im with hγ
  have hγ0 : (0 : ℝ) < γ := lt_of_lt_of_le hT0 hγ1
  -- the ordinate sits in `[T, 2T]`, so `log γ ∈ [log T, 2 log T]`
  have hLe : Real.exp 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]; exact hTe
  have hLM : Real.log T ≤ Real.log γ := Real.log_le_log hT0 hγ1
  have hM2 : Real.log γ ≤ 2 * Real.log T := by
    have h := Real.log_le_log hγ0 hγ2
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    rw [Real.log_mul (by norm_num) hT0.ne'] at h
    have : (1 : ℝ) ≤ Real.log T := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    linarith
  -- the Vinogradov–Korobov region at height `γ`
  have hζ : riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 := by
    rw [hβ, hγ, Complex.re_add_im]
    exact riemannZeta_eq_zero_of_xiZeroCopy q
  have hvk : β ≤ 1 - Real.log γ ^ (-(2 : ℝ) / 3) * Real.log (Real.log γ) ^ (-(5 : ℝ) / 3) / 10 ^ 8 := by
    by_contra hcon
    exact hγ₀ β γ (le_trans hTγ₀ hγ1) (by linarith [not_le.mp hcon]) hζ
  have hcmp := surrogate_le_vinogradovKorobov_width hLe hLM hM2
  have hw : vinogradovKorobovSurrogateWidth T = Real.log T ^ (-(5 : ℝ) / 7) / 10 ^ 12 := by
    refine vinogradovKorobovSurrogateWidth_eq ?_
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  rw [hw]
  linarith

end

end RHTower
