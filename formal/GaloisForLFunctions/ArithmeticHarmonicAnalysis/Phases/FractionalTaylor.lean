import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Polynomial replacement of fractional phases

The Taylor step in Fragkos's Lemma 4.1 (arXiv:2611.02465) applies to every
real power. On a block of length `N^θ`, degree `k` gives the explicit loss
`N^(c-(k+1)(1-θ))`. The derivative estimates are proved from the power
function itself, and a sufficiently large degree gives a power saving.
-/

noncomputable section

open Set Finset

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Phases

/-- Taylor polynomial of `x^c` at the left endpoint `N`. -/
def powerTaylor (c N : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1),
    (descPochhammer ℝ j).eval c * N ^ (c - j) * (x - N) ^ j / j.factorial

/-- Uniform coefficient of the Taylor remainder on a dyadic block. -/
def powerTaylorConstant (c : ℝ) (k : ℕ) : ℝ :=
  |(descPochhammer ℝ (k + 1)).eval c| * max 1 ((2 : ℝ) ^ (c - (k + 1))) /
    k.factorial

theorem powerTaylorConstant_nonneg (c : ℝ) (k : ℕ) : 0 ≤ powerTaylorConstant c k := by
  unfold powerTaylorConstant
  positivity

private theorem dyadic_rpow_le (r : ℝ) {N y : ℝ} (hN : 0 < N)
    (hy : y ∈ Icc N (2 * N)) : y ^ r ≤ max 1 ((2 : ℝ) ^ r) * N ^ r := by
  rcases le_total 0 r with hr | hr
  · calc y ^ r ≤ (2 * N) ^ r := Real.rpow_le_rpow (hN.le.trans hy.1) hy.2 hr
      _ = (2 : ℝ) ^ r * N ^ r := Real.mul_rpow (by norm_num) hN.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hN.le _)
  · exact (Real.rpow_le_rpow_of_nonpos hN hy.1 hr).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hN.le _) (le_max_left _ _))

private theorem power_within_deriv (c : ℝ) (j : ℕ) {N y : ℝ}
    (hN : 0 < N) (hy : y ∈ Icc N (2 * N)) :
    iteratedDerivWithin j (fun x : ℝ => x ^ c) (Icc N (2 * N)) y =
      (descPochhammer ℝ j).eval c * y ^ (c - j) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith only [hN]))
    (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (hN.trans_le hy.1))) hy,
    iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

theorem powerTaylor_eq_taylorWithin (c : ℝ) (k : ℕ) {N : ℝ} (hN : 0 < N) (x : ℝ) :
    powerTaylor c N k x = taylorWithinEval (fun y : ℝ => y ^ c) k (Icc N (2 * N)) N x := by
  rw [powerTaylor, taylor_within_apply]
  apply sum_congr rfl
  intro j _
  rw [power_within_deriv c j hN ⟨le_rfl, by linarith only [hN]⟩, smul_eq_mul]
  ring

/-- A dyadic Taylor bound with no assumed derivative estimate. -/
theorem powerTaylor_remainder (c : ℝ) (k : ℕ) {N x : ℝ}
    (hN : 0 < N) (hx : x ∈ Icc N (2 * N)) :
    |x ^ c - powerTaylor c N k x| ≤
      powerTaylorConstant c k * N ^ (c - (k + 1)) * (x - N) ^ (k + 1) := by
  have hf : ContDiffOn ℝ (k + 1) (fun y : ℝ => y ^ c) (Icc N (2 * N)) :=
    fun y hy => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (hN.trans_le hy.1))).contDiffWithinAt
  have hd (y : ℝ) (hy : y ∈ Icc N (2 * N)) :
      ‖iteratedDerivWithin (k + 1) (fun x : ℝ => x ^ c) (Icc N (2 * N)) y‖ ≤
        |(descPochhammer ℝ (k + 1)).eval c| *
          (max 1 ((2 : ℝ) ^ (c - (k + 1))) * N ^ (c - (k + 1))) := by
    rw [power_within_deriv c (k + 1) hN hy, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (hN.le.trans hy.1) _)]
    simpa only [Nat.cast_add_one] using mul_le_mul_of_nonneg_left
      (dyadic_rpow_le (c - ((k + 1 : ℕ) : ℝ)) hN hy)
      (abs_nonneg ((descPochhammer ℝ (k + 1)).eval c))
  have h := taylor_mean_remainder_bound (by linarith only [hN]) hf hx hd
  rw [← powerTaylor_eq_taylorWithin c k hN x, Real.norm_eq_abs] at h
  convert h using 1
  unfold powerTaylorConstant
  ring

/-- A block of length `N^θ` loses exactly the exponent `c-(k+1)(1-θ)`. -/
theorem powerTaylor_short_remainder (c θ : ℝ) (k : ℕ) {N x : ℝ}
    (hN : 1 ≤ N) (hθ : θ ≤ 1) (hx : x ∈ Icc N (N + N ^ θ)) :
    |x ^ c - powerTaylor c N k x| ≤
      powerTaylorConstant c k * N ^ (c - (k + 1) * (1 - θ)) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hlen : N ^ θ ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN hθ
  have hrem := powerTaylor_remainder c k hN0 ⟨hx.1, by linarith only [hx.2, hlen]⟩
  have hpow : (x - N) ^ (k + 1) ≤ (N ^ θ) ^ (k + 1) :=
    pow_le_pow_left₀ (sub_nonneg.mpr hx.1) (by linarith only [hx.2]) _
  calc |x ^ c - powerTaylor c N k x| ≤
      powerTaylorConstant c k * N ^ (c - (k + 1)) * (N ^ θ) ^ (k + 1) :=
      hrem.trans (mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (powerTaylorConstant_nonneg c k) (Real.rpow_nonneg hN0.le _)))
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, mul_assoc, ← Real.rpow_add hN0]
      congr 2
      push_cast
      ring

/-- Every exponent below one admits a degree giving a uniform power saving. -/
theorem exists_powerTaylor_saving (c : ℝ) {θ : ℝ} (hθ : θ < 1) :
    ∃ k : ℕ, ∃ η : ℝ, 0 < η ∧ ∀ N x : ℝ, 1 ≤ N →
      x ∈ Icc N (N + N ^ θ) →
        |x ^ c - powerTaylor c N k x| ≤ powerTaylorConstant c k * N ^ (-η) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (c / (1 - θ))
  have hden : 0 < 1 - θ := sub_pos.mpr hθ
  have hk' : c < (k : ℝ) * (1 - θ) := (div_lt_iff₀ hden).mp hk
  refine ⟨k, ((k : ℝ) + 1) * (1 - θ) - c, by nlinarith only [hk', hden], ?_⟩
  intro N x hN hx
  convert powerTaylor_short_remainder c θ k hN hθ.le hx using 1
  congr 2
  ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Phases
