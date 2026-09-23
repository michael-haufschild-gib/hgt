import GaloisForLFunctions.RHTower.SuzukiWeilLerchBlock

/-!
# The Gauss digamma series off the poles

The corpus (`RHTower.digamma_sub_eq_tsum`) and mathlib only carry Gauss's digamma difference series
on the right half-plane `Re w > 0`.  Suzuki's appendix limit (7.2) evaluates `psi(1/4 - y/2)` with
`y` tending to `+infinity`, i.e. arbitrarily far to the *left*, so the half-plane form is useless.

This file removes the restriction.  The mechanism is that the regularized difference

`S(w) = sum_n (1/(n+w) - 1/(n+1/4))`   (`suzukiLerchDiff 0 w`)

satisfies the *same* one-step shift law as the digamma, with the opposite sign:

`S(w+1) = S(w) - 1/w`,     `psi(w+1) = psi(w) + 1/w`,

so the defect `psi(w) - psi(1/4) + S(w)` is `1`-periodic; it vanishes on `Re w > 0` by the corpus
theorem, hence everywhere off the poles of `Gamma`.

Two by-products of independent use: the series is summable at *every* `w` with no hypothesis at all
(only finitely many indices can be near a pole, and the junk value of `0` inverse is harmless), and
the Lerch kernel obeys a clean uniform bound on `1 <= Re w`.
-/

open Complex Filter Topology
open GaloisForLFunctions.RHTower

open Complex Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-- The factorization of a single Lerch difference term at every point where the shifted
denominator is nonzero (no half-plane hypothesis). -/
theorem suzukiLerchDiffTerm_eq' {t : ℝ} {w : ℂ} {n : ℕ} (h1 : ((n : ℂ) + w) ≠ 0) :
    suzukiLerchDiffTerm t w n = (1 / 4 - w) * suzukiLerchKernelTerm t w n := by
  have h2 : ((n : ℂ) + 1 / 4) ≠ 0 := nat_add_quarter_ne_zero n
  have key : ((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹
      = (1 / 4 - w) / (((n : ℂ) + w) * ((n : ℂ) + 1 / 4)) := by
    rw [inv_sub_inv h1 h2]
    congr 1
    ring
  rw [suzukiLerchDiffTerm, suzukiLerchKernelTerm, key]
  ring

/-- **Unconditional summability of the Lerch difference series.**  Only finitely many indices can
be near the poles, so no half-plane or off-poles hypothesis is needed at all. -/
theorem summable_suzukiLerchDiffTerm_all {t : ℝ} (ht : 0 ≤ t) (w : ℂ) :
    Summable (suzukiLerchDiffTerm t w) := by
  set K : ℕ := ⌈‖w‖⌉₊ + 1 with hK
  rw [← summable_nat_add_iff K]
  refine Summable.of_norm_bounded
    (summable_one_div_nat_add_one_sq.mul_left ‖(1 : ℂ) / 4 - w‖) ?_
  intro n
  have hKw : ‖w‖ + 1 ≤ (K : ℝ) := by
    rw [hK]
    push_cast
    linarith [Nat.le_ceil ‖w‖]
  have hmcast : ((n + K : ℕ) : ℝ) = (n : ℝ) + (K : ℝ) := by push_cast; ring
  have hlow : ((n : ℝ) + 1) ≤ ‖((n + K : ℕ) : ℂ) + w‖ := by
    have h1 : ‖(((n + K : ℕ) : ℂ) + w) - w‖ ≤ ‖((n + K : ℕ) : ℂ) + w‖ + ‖w‖ :=
      norm_sub_le _ _
    have h2 : (((n + K : ℕ) : ℂ) + w) - w = ((n + K : ℕ) : ℂ) := by ring
    rw [h2, Complex.norm_natCast, hmcast] at h1
    linarith
  have hlow2 : ((n : ℝ) + 1) ≤ ‖((n + K : ℕ) : ℂ) + 1 / 4‖ := by
    rw [norm_nat_add_quarter, hmcast]
    have : (1 : ℝ) ≤ (K : ℝ) := by
      rw [hK]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈‖w‖⌉₊]
    linarith
  have hne : ((n + K : ℕ) : ℂ) + w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hApos : (0 : ℝ) < ‖((n + K : ℕ) : ℂ) + w‖ := lt_of_lt_of_le hpos hlow
  have hBpos : (0 : ℝ) < ‖((n + K : ℕ) : ℂ) + 1 / 4‖ := lt_of_lt_of_le hpos hlow2
  rw [suzukiLerchDiffTerm_eq' hne, norm_mul, suzukiLerchKernelTerm, norm_div, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hexp : ‖((Real.exp (-(2 * ((n + K : ℕ) : ℝ) * t)) : ℝ) : ℂ)‖ ≤ 1 := norm_exp_block_le ht _
  calc ‖((Real.exp (-(2 * ((n + K : ℕ) : ℝ) * t)) : ℝ) : ℂ)‖ * ((n : ℝ) + 1) ^ (2 : ℕ)
      ≤ 1 * ((n : ℝ) + 1) ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = ((n : ℝ) + 1) * ((n : ℝ) + 1) := by ring
    _ ≤ ‖((n + K : ℕ) : ℂ) + w‖ * ‖((n + K : ℕ) : ℂ) + 1 / 4‖ :=
        mul_le_mul hlow hlow2 (by positivity) (norm_nonneg _)
    _ = 1 * (‖((n + K : ℕ) : ℂ) + w‖ * ‖((n + K : ℕ) : ℂ) + 1 / 4‖) := by ring

/-- The Lerch difference at the shifted base point `5/4` is `-4`. -/
theorem suzukiLerchDiff_zero_five_quarters : suzukiLerchDiff 0 ((5 : ℂ) / 4) = -4 := by
  have hq : ∀ m : ℕ, ((1 : ℂ) / 4) ≠ -(m : ℂ) := by
    intro m h
    have hre : ((1 : ℂ) / 4).re = (-(m : ℂ)).re := by rw [h]
    simp at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hstep := Complex.digamma_apply_add_one ((1 : ℂ) / 4) hq
  rw [show (1 : ℂ) / 4 + 1 = 5 / 4 by norm_num] at hstep
  have hre : (0 : ℝ) < ((5 : ℂ) / 4).re := by norm_num
  have hbridge := digamma_sub_quarter_eq hre
  rw [hstep] at hbridge
  have hinv : ((1 : ℂ) / 4)⁻¹ = 4 := by norm_num
  rw [hinv] at hbridge
  linear_combination hbridge

/-- **The one-step shift law for the Lerch difference.**  `S(w+1) = S(w) - 1/w`, the exact mirror
of the digamma recurrence `ψ(w+1) = ψ(w) + 1/w`. -/
theorem suzukiLerchDiff_zero_add_one (w : ℂ) :
    suzukiLerchDiff 0 (w + 1) = suzukiLerchDiff 0 w - w⁻¹ := by
  have hs_w : Summable (suzukiLerchDiffTerm 0 w) := summable_suzukiLerchDiffTerm_all le_rfl w
  have hs_q : Summable (suzukiLerchDiffTerm 0 ((5 : ℂ) / 4)) :=
    summable_suzukiLerchDiffTerm_all le_rfl _
  have hs_shift : Summable (fun n : ℕ => suzukiLerchDiffTerm 0 w (n + 1)) :=
    (summable_nat_add_iff 1).mpr hs_w
  have hterm : ∀ n : ℕ, suzukiLerchDiffTerm 0 (w + 1) n
      = suzukiLerchDiffTerm 0 w (n + 1) + suzukiLerchDiffTerm 0 ((5 : ℂ) / 4) n := by
    intro n
    simp only [suzukiLerchDiffTerm, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one,
      one_mul]
    have e1 : ((n : ℂ) + (w + 1)) = (((n + 1 : ℕ) : ℂ) + w) := by push_cast; ring
    have e2 : (((n + 1 : ℕ) : ℂ) + 1 / 4) = ((n : ℂ) + 5 / 4) := by push_cast; ring
    rw [e1, e2]
    ring
  have hsplit : suzukiLerchDiff 0 (w + 1)
      = (∑' n : ℕ, suzukiLerchDiffTerm 0 w (n + 1)) + suzukiLerchDiff 0 ((5 : ℂ) / 4) := by
    rw [suzukiLerchDiff, suzukiLerchDiff, ← hs_shift.tsum_add hs_q]
    exact tsum_congr hterm
  have hzero : suzukiLerchDiff 0 w
      = suzukiLerchDiffTerm 0 w 0 + ∑' n : ℕ, suzukiLerchDiffTerm 0 w (n + 1) :=
    hs_w.tsum_eq_zero_add
  have h0 : suzukiLerchDiffTerm 0 w 0 = w⁻¹ - 4 := by
    simp only [suzukiLerchDiffTerm, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero,
      Complex.ofReal_one, one_mul, zero_add]
    norm_num
  rw [hsplit, suzukiLerchDiff_zero_five_quarters, hzero, h0]
  ring

/-- **The Gauss bridge off the poles.**  `ψ(w) − ψ(1/4) = −∑ₙ (1/(n+w) − 1/(n+1/4))` for every `w`
that is not a pole of `Γ`, with no half-plane restriction.  Mathlib and the corpus only had this on
`Re w > 0`; the extension is by the common shift law `S(w+1) = S(w) − 1/w`, `ψ(w+1) = ψ(w) + 1/w`. -/
theorem digamma_sub_quarter_eq_offPoles {w : ℂ} (hw : ∀ m : ℕ, w ≠ -(m : ℂ)) :
    Complex.digamma w - Complex.digamma (1 / 4) = -suzukiLerchDiff 0 w := by
  have hstep : ∀ v : ℂ, (∀ m : ℕ, v ≠ -(m : ℂ)) →
      Complex.digamma (v + 1) - Complex.digamma (1 / 4) + suzukiLerchDiff 0 (v + 1)
        = Complex.digamma v - Complex.digamma (1 / 4) + suzukiLerchDiff 0 v := by
    intro v hv
    rw [Complex.digamma_apply_add_one v hv, suzukiLerchDiff_zero_add_one v]
    ring
  have hshift : ∀ M : ℕ,
      Complex.digamma (w + (M : ℂ)) - Complex.digamma (1 / 4) + suzukiLerchDiff 0 (w + (M : ℂ))
        = Complex.digamma w - Complex.digamma (1 / 4) + suzukiLerchDiff 0 w := by
    intro M
    induction M with
    | zero => norm_num
    | succ M ih =>
      have hwM : ∀ m : ℕ, w + (M : ℂ) ≠ -(m : ℂ) := by
        intro m hc
        refine hw (m + M) ?_
        push_cast
        linear_combination hc
      have hrw : w + ((M + 1 : ℕ) : ℂ) = (w + (M : ℂ)) + 1 := by push_cast; ring
      rw [hrw, hstep _ hwM, ih]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 0 < (w + (M : ℂ)).re := by
    refine ⟨⌈-w.re⌉₊ + 1, ?_⟩
    have h1 : (w + ((⌈-w.re⌉₊ + 1 : ℕ) : ℂ)).re = w.re + ((⌈-w.re⌉₊ : ℝ) + 1) := by
      push_cast
      simp
    rw [h1]
    linarith [Nat.le_ceil (-w.re)]
  have h0 : Complex.digamma (w + (M : ℂ)) - Complex.digamma (1 / 4)
      + suzukiLerchDiff 0 (w + (M : ℂ)) = 0 := by
    rw [digamma_sub_quarter_eq hM]
    ring
  have hkey := hshift M
  rw [h0] at hkey
  linear_combination -hkey

/-- A crude but uniform bound for the Lerch kernel on `Re w ≥ 1`. -/
theorem norm_suzukiLerchKernel_le_of_one_le_re {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : 1 ≤ w.re) :
    ‖suzukiLerchKernel t w‖ ≤ 4 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 : ℕ) := by
  have hsum : Summable (fun n : ℕ => 4 * (1 / ((n : ℝ) + 1) ^ (2 : ℕ))) :=
    summable_one_div_nat_add_one_sq.mul_left 4
  have hbd : ∀ n : ℕ, ‖suzukiLerchKernelTerm t w n‖ ≤ 4 * (1 / ((n : ℝ) + 1) ^ (2 : ℕ)) := by
    intro n
    have := norm_suzukiLerchKernelTerm_le ht (c := 1) one_pos le_rfl hw n
    simpa using this
  calc ‖suzukiLerchKernel t w‖ ≤ ∑' n : ℕ, 4 * (1 / ((n : ℝ) + 1) ^ (2 : ℕ)) :=
        tsum_of_norm_bounded hsum.hasSum hbd
    _ = 4 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 : ℕ) := tsum_mul_left

end
end RHTower
