import GaloisForLFunctions.RHTower.PsiWindowUpperBound
import GaloisForLFunctions.RHTower.PsiRemainderWindowSmallValue

/-!
# Existence of pointwise-small gain windows

In every multiplicative window `(Y, QY]` with `log Q > 40/δ + 2` there is a
point `m₀` above which the remainder is **pointwise** small on the whole
relative-`ρ` window:

`∀ t ∈ [m₀, (1+ρ)m₀] : |R(t)| ≤ (δ + ρ(log(1/ρ) + 3))·t
   + (log(QY) + 1) + 2√t·log t`,

combining the small-value supply with the two-sided window slow variation;
the middle term is tamed by the algebraic monotonicity of
`u ↦ u(log t − log u + 2)`.  These are the gain blocks of the
Erdős–Selberg contraction: their ratio is `≈ δ + ρ log(1/ρ)` instead of
the ambient uniform ratio.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- Algebraic monotonicity of `u ↦ u(log t − log u + 2)` on `[1, t]`. -/
theorem mul_log_ratio_mono {u₁ u₂ t : ℝ} (h1 : 1 ≤ u₁) (h12 : u₁ ≤ u₂)
    (h2t : u₂ ≤ t) :
    u₁ * (Real.log t - Real.log u₁ + 2)
      ≤ u₂ * (Real.log t - Real.log u₂ + 2) := by
  have hu₁0 : (0 : ℝ) < u₁ := by linarith
  have hu₂0 : (0 : ℝ) < u₂ := by linarith
  have hlog : Real.log u₂ - Real.log u₁ ≤ (u₂ - u₁) / u₁ := by
    have h := Real.log_le_sub_one_of_pos
      (x := u₂ / u₁) (by positivity)
    rw [Real.log_div hu₂0.ne' hu₁0.ne'] at h
    have heq : u₂ / u₁ - 1 = (u₂ - u₁) / u₁ := by
      field_simp
    linarith
  have hlogt : Real.log u₂ ≤ Real.log t := Real.log_le_log hu₂0 h2t
  have hkey : u₁ * (Real.log u₂ - Real.log u₁) ≤ u₂ - u₁ := by
    have := mul_le_mul_of_nonneg_left hlog hu₁0.le
    rw [mul_div_cancel₀] at this
    · linarith
    · exact hu₁0.ne'
  nlinarith [hkey, hlogt, h12]

/-- **Gain-window existence**: every window `(Y, QY]` with
`log Q > 40/δ + 2` contains `m₀` above which the remainder is pointwise
small on the relative-`ρ` window. -/
theorem exists_pointwise_small_window {δ ρ : ℝ} {Y Q : ℕ}
    (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hY : 1 ≤ Y) (hQ1 : 1 ≤ Q)
    (hQ : 40 / δ + 2 < Real.log Q) :
    ∃ m₀ : ℕ, Y < m₀ ∧ m₀ ≤ Q * Y ∧
      ∀ t : ℕ, m₀ ≤ t → (t : ℝ) ≤ (1 + ρ) * m₀ →
        |psiRemainder t|
          ≤ (δ + ρ * (Real.log (1 / ρ) + 3)) * t
            + (Real.log ((Q * Y : ℕ) : ℝ) + 1)
            + 2 * Real.sqrt t * Real.log t := by
  have hQY : Y ≤ Q * Y := Nat.le_mul_of_pos_left Y (by omega)
  have hbig : 40 / δ + 2 < Real.log ((Q * Y : ℕ) : ℝ) - Real.log Y := by
    have hcast : ((Q * Y : ℕ) : ℝ) = (Q : ℝ) * Y := by push_cast; ring
    rw [hcast, Real.log_mul (Nat.cast_ne_zero.2 (by omega))
      (Nat.cast_ne_zero.2 (by omega))]
    have h0 : (0 : ℝ) ≤ Real.log Y ∧ Real.log Y = Real.log Y := by
      exact ⟨Real.log_nonneg (by exact_mod_cast hY), rfl⟩
    linarith [hQ]
  obtain ⟨m₀, hm₀, hsmall⟩ :=
    exists_small_psiRemainder_in_window hδ hY hQY hbig
  rw [Finset.mem_Ioc] at hm₀
  refine ⟨m₀, hm₀.1, hm₀.2, ?_⟩
  intro t hmt htρ
  have hm₀1 : 1 ≤ m₀ := by omega
  have hm₀R : (1 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm₀1
  have ht2 : t ≤ 2 * m₀ := by
    have h1 : (t : ℝ) ≤ 2 * m₀ := by nlinarith [htρ, hρ1, hm₀R]
    exact_mod_cast h1
  have ht1R : (1 : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ t)
  have hwin := abs_psiRemainder_le_of_window hm₀1 hmt ht2
  -- the small point
  have hsmall' : |psiRemainder m₀|
      ≤ δ * m₀ + Real.log ((Q * Y : ℕ) : ℝ) + 1 := hsmall
  have hδm : δ * m₀ ≤ δ * t := by
    apply mul_le_mul_of_nonneg_left _ hδ.le
    exact_mod_cast hmt
  -- the middle term
  have hmid : ((t - m₀ : ℕ) : ℝ)
      * (Real.log t - Real.log ((t - m₀ : ℕ) : ℝ) + 2)
      ≤ ρ * (Real.log (1 / ρ) + 3) * t := by
    have hρlog0 : 0 ≤ Real.log (1 / ρ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hρ0, one_mul]; exact hρ1)
    rcases Nat.eq_zero_or_pos (t - m₀) with h0 | h0
    · rw [h0]
      simp only [Nat.cast_zero, zero_mul]
      apply mul_nonneg (mul_nonneg hρ0.le (by linarith))
        (Nat.cast_nonneg t)
    · -- `1 ≤ u ≤ ρm₀ ≤ t`
      have hu1 : (1 : ℝ) ≤ ((t - m₀ : ℕ) : ℝ) := by
        exact_mod_cast h0
      have hucast : ((t - m₀ : ℕ) : ℝ) = (t : ℝ) - m₀ := by
        rw [Nat.cast_sub hmt]
      have huρ : ((t - m₀ : ℕ) : ℝ) ≤ ρ * m₀ := by
        rw [hucast]
        nlinarith [htρ]
      have hρm₀t : ρ * m₀ ≤ (t : ℝ) := by
        have h1 : (m₀ : ℝ) ≤ t := by exact_mod_cast hmt
        nlinarith [hρ1, hm₀R]
      have hmono := mul_log_ratio_mono hu1 huρ hρm₀t
      have hval : ρ * m₀ * (Real.log t - Real.log (ρ * m₀) + 2)
          ≤ ρ * (Real.log (1 / ρ) + 3) * t := by
        have hρm₀0 : (0 : ℝ) < ρ * m₀ := by positivity
        have hlow : Real.log t - Real.log (ρ * m₀)
            ≤ Real.log (1 / ρ) + 1 := by
          have h1 : (t : ℝ) ≤ 2 * m₀ := by exact_mod_cast ht2
          have h2 : Real.log t ≤ Real.log (2 * m₀) :=
            Real.log_le_log (by linarith) h1
          rw [Real.log_mul (by norm_num) (by linarith : (m₀:ℝ) ≠ 0)] at h2
          rw [Real.log_mul hρ0.ne' (by linarith : (m₀:ℝ) ≠ 0),
            one_div, Real.log_inv]
          have hlog2 : Real.log 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (x := (2:ℝ)) (by norm_num)
            linarith
          linarith
        have hmul := mul_le_mul_of_nonneg_left hlow hρm₀0.le
        have hm₀le : (m₀ : ℝ) ≤ t := by exact_mod_cast hmt
        calc ρ * m₀ * (Real.log t - Real.log (ρ * m₀) + 2)
            = ρ * m₀ * (Real.log t - Real.log (ρ * m₀))
              + 2 * (ρ * m₀) := by ring
          _ ≤ ρ * m₀ * (Real.log (1 / ρ) + 1) + 2 * (ρ * m₀) := by
              linarith [hmul]
          _ = ρ * m₀ * (Real.log (1 / ρ) + 3) := by ring
          _ ≤ ρ * t * (Real.log (1 / ρ) + 3) := by
              apply mul_le_mul_of_nonneg_right _ (by linarith)
              nlinarith [hm₀le, hρ0.le]
          _ = ρ * (Real.log (1 / ρ) + 3) * t := by ring
      exact le_trans hmono hval
  linarith [hwin, hsmall', hδm, hmid]

end RHTower
