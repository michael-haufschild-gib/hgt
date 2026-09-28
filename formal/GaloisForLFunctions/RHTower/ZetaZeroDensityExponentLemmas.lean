import Mathlib

/-!
# Exponent lemmas for the eight-thirds zero-density estimate

Three elementary facts used to turn large-value counts into a zero-density exponent:

* `eventually_const_mul_polylog_le_rpow`: a fixed power of `1 + log T`, times any constant, is
  eventually below `T^c` for every `c > 0`;
* `exists_pow_mem_two_thirds_four_thirds`: if `T^{1/50} ≤ K ≤ T^{4/3}` then some power `K^ℓ` with
  `1 ≤ ℓ ≤ 34` lies in `[T^{2/3}, T^{4/3}]`;
* the linear exponent comparisons behind the mean-value range `σ ≤ 3/4 + ε/32` and the Huxley
  range `σ ≥ 3/4`.
-/

namespace RHTower

noncomputable section

open Filter Real

/-- A fixed power of the logarithm is eventually below every positive power. -/
theorem eventually_const_mul_polylog_le_rpow (B : ℕ) {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, C * (1 + Real.log T) ^ B ≤ T ^ c := by
  set c' : ℝ := c / (2 * (B + 1)) with hc'
  have hc'0 : 0 < c' := by positivity
  have hlog := (isLittleO_log_rpow_atTop hc'0).bound (show (0 : ℝ) < 1 by norm_num)
  have hbig : Tendsto (fun T : ℝ => T ^ (c / 2)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hC := hbig.eventually_ge_atTop (|C| * 2 ^ B + 1)
  filter_upwards [hlog, hC, eventually_ge_atTop (1 : ℝ)] with T hT hTC hT1
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hpow1 : 1 ≤ T ^ c' := Real.one_le_rpow hT1 hc'0.le
  have hlog1 : Real.log T ≤ T ^ c' := by
    rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (Real.rpow_nonneg hT0.le _), one_mul] at hT
    exact hT
  have h1 : 1 + Real.log T ≤ 2 * T ^ c' := by linarith
  have h2 : (1 + Real.log T) ^ B ≤ (2 * T ^ c') ^ B := pow_le_pow_left₀ (by linarith) h1 B
  have h3 : (2 * T ^ c') ^ B = 2 ^ B * T ^ (c' * B) := by
    rw [mul_pow, ← Real.rpow_natCast (T ^ c'), ← Real.rpow_mul hT0.le]
  have h4 : T ^ (c' * B) ≤ T ^ (c / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hT1
    rw [hc']
    have hB : (B : ℝ) ≤ B + 1 := by linarith
    have hden : (0 : ℝ) < 2 * (B + 1) := by positivity
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  have hsplit : T ^ c = T ^ (c / 2) * T ^ (c / 2) := by
    rw [← Real.rpow_add hT0]
    ring_nf
  have hCB : C * (1 + Real.log T) ^ B ≤ |C| * (2 ^ B * T ^ (c / 2)) := by
    have hpos : 0 ≤ (1 + Real.log T) ^ B := by positivity
    calc C * (1 + Real.log T) ^ B ≤ |C| * (1 + Real.log T) ^ B :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hpos
      _ ≤ |C| * (2 ^ B * T ^ (c / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          calc (1 + Real.log T) ^ B ≤ (2 * T ^ c') ^ B := h2
            _ = 2 ^ B * T ^ (c' * B) := h3
            _ ≤ 2 ^ B * T ^ (c / 2) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have hhalf : 0 ≤ T ^ (c / 2) := Real.rpow_nonneg hT0.le _
  calc C * (1 + Real.log T) ^ B ≤ |C| * 2 ^ B * T ^ (c / 2) := by rw [mul_assoc]; exact hCB
    _ ≤ T ^ (c / 2) * T ^ (c / 2) := mul_le_mul_of_nonneg_right (by linarith) hhalf
    _ = T ^ c := hsplit.symm

/-- **A power in the window `[T^{2/3}, T^{4/3}]`.** -/
theorem exists_pow_mem_two_thirds_four_thirds {T : ℝ} (hT : 1 < T) {K : ℕ}
    (hK1 : T ^ (1 / 50 : ℝ) ≤ K) (hK2 : (K : ℝ) ≤ T ^ (4 / 3 : ℝ)) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ 34 ∧ T ^ (2 / 3 : ℝ) ≤ (K : ℝ) ^ ℓ ∧ (K : ℝ) ^ ℓ ≤ T ^ (4 / 3 : ℝ) := by
  classical
  have hT0 : 0 < T := by linarith
  have hK0 : 0 < (K : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hT0 _) hK1
  have h34 : T ^ (2 / 3 : ℝ) ≤ (K : ℝ) ^ (34 : ℕ) := by
    calc T ^ (2 / 3 : ℝ) ≤ T ^ ((1 / 50 : ℝ) * 34) :=
          Real.rpow_le_rpow_of_exponent_le hT.le (by norm_num)
      _ = (T ^ (1 / 50 : ℝ)) ^ (34 : ℕ) := by
          rw [Real.rpow_mul hT0.le]
          norm_cast
      _ ≤ (K : ℝ) ^ (34 : ℕ) := pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hK1 _
  have hex : ∃ ℓ, T ^ (2 / 3 : ℝ) ≤ (K : ℝ) ^ ℓ := ⟨34, h34⟩
  set ℓ := Nat.find hex with hℓ
  have hspec : T ^ (2 / 3 : ℝ) ≤ (K : ℝ) ^ ℓ := Nat.find_spec hex
  have hle34 : ℓ ≤ 34 := Nat.find_min' hex h34
  have hone : 1 < T ^ (2 / 3 : ℝ) := Real.one_lt_rpow hT (by norm_num)
  have hℓ1 : 1 ≤ ℓ := by
    by_contra h
    have h0 : ℓ = 0 := by omega
    rw [h0, pow_zero] at hspec
    linarith
  refine ⟨ℓ, hℓ1, hle34, hspec, ?_⟩
  rcases eq_or_lt_of_le hℓ1 with h | h
  · rw [← h, pow_one]
    exact hK2
  · have hmin1 : ¬ T ^ (2 / 3 : ℝ) ≤ (K : ℝ) ^ (ℓ - 1) := Nat.find_min hex (by omega)
    have hminK : ¬ T ^ (2 / 3 : ℝ) ≤ (K : ℝ) ^ (1 : ℕ) := Nat.find_min hex h
    push Not at hmin1 hminK
    rw [pow_one] at hminK
    have hsplit : (K : ℝ) ^ ℓ = (K : ℝ) ^ (ℓ - 1) * K := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hsplit]
    calc (K : ℝ) ^ (ℓ - 1) * K ≤ T ^ (2 / 3 : ℝ) * T ^ (2 / 3 : ℝ) :=
          mul_le_mul hmin1.le hminK.le hK0.le (Real.rpow_nonneg hT0.le _)
      _ = T ^ (4 / 3 : ℝ) := by rw [← Real.rpow_add hT0]; norm_num

/-- The mean-value exponent `1 + (2/3)(1 - 2σ)` is below `(8/3 + ε)(1 - σ)` for
`σ ≤ 3/4 + ε/32` and `0 < ε ≤ 1`. -/
theorem mvt_exponent_le {σ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ : σ ≤ 3 / 4 + ε / 32) :
    1 + (2 / 3) * (1 - 2 * σ) ≤ (8 / 3 + ε) * (1 - σ) := by
  nlinarith

/-- The Huxley exponent `1 + (2/3)(4 - 6σ)` is below `(8/3)(1 - σ)` for `σ ≥ 3/4`. -/
theorem huxley_exponent_le {σ : ℝ} (hσ : 3 / 4 ≤ σ) :
    1 + (2 / 3) * (4 - 6 * σ) ≤ (8 / 3) * (1 - σ) := by
  linarith

end

end RHTower
