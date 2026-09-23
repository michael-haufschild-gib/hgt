import Mathlib

/-!
# Monotone Möbius positivity

The prime measure `Π` of a generalized number system is recovered from its prime-power measure
`Π_*` by the Möbius inversion `Π = Σ_k μ(k)k^{-2}·Π_*(·/k)` in logarithmic coordinates (the Mellin
multiplier `1/ζ(2-s)`).  Signing that alternating series is normally intractable.

The lemma below replaces it by a single monotonicity requirement: if the prime-power density is
nonnegative and nondecreasing, then the inverted prime density is bounded below by
`(2 - π²/6) ≈ 0.355` times it, hence nonnegative.  Only `Σ_{k≥2}k^{-2} = π²/6 - 1 < 1` is used.
-/

open Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

/-- Logarithmic Möbius inversion of a density: the Mellin multiplier `1/ζ(2-s)`. -/
def mobiusLogInversion (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑' k : ℕ, (moebius k : ℝ) / (k : ℝ) ^ (2 : ℕ) * g (u / k)

private theorem term_abs_le {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hmono : Monotone g)
    {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    |(moebius k : ℝ) / (k : ℝ) ^ (2 : ℕ) * g (u / k)| ≤ g u / (k : ℝ) ^ (2 : ℕ) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hle : u / (k : ℝ) ≤ u := by
    rw [div_le_iff₀ hkpos]
    nlinarith [hu]
  have hgle : g (u / k) ≤ g u := hmono hle
  have hmu : |(moebius k : ℝ)| ≤ 1 := by
    have h := abs_moebius_le_one (n := k)
    calc |(moebius k : ℝ)| = ((|moebius k| : ℤ) : ℝ) := by push_cast; simp
      _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
      _ = 1 := by norm_num
  rw [abs_mul, abs_div, abs_of_nonneg (hg0 (u / k)), abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)^(2 : ℕ))]
  calc |(moebius k : ℝ)| / (k : ℝ) ^ (2 : ℕ) * g (u / k)
      ≤ 1 / (k : ℝ) ^ (2 : ℕ) * g (u / k) := by
        apply mul_le_mul_of_nonneg_right _ (hg0 _)
        exact div_le_div_of_nonneg_right hmu (by positivity)
    _ ≤ 1 / (k : ℝ) ^ (2 : ℕ) * g u := mul_le_mul_of_nonneg_left hgle (by positivity)
    _ = g u / (k : ℝ) ^ (2 : ℕ) := by ring

private theorem summable_scaled (c : ℝ) : Summable (fun k : ℕ => c / (k : ℝ) ^ (2 : ℕ)) := by
  have h : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ (2 : ℕ)) := hasSum_zeta_two.summable
  simpa [div_eq_mul_inv, mul_comm] using h.mul_left c

private theorem tsum_scaled (c : ℝ) :
    (∑' k : ℕ, c / (k : ℝ) ^ (2 : ℕ)) = c * (Real.pi ^ (2 : ℕ) / 6) := by
  have h : HasSum (fun k : ℕ => c * ((1 : ℝ) / (k : ℝ) ^ (2 : ℕ))) (c * (Real.pi ^ (2 : ℕ) / 6)) :=
    hasSum_zeta_two.mul_left c
  have h' : HasSum (fun k : ℕ => c / (k : ℝ) ^ (2 : ℕ)) (c * (Real.pi ^ (2 : ℕ) / 6)) := by
    simpa [div_eq_mul_inv, mul_assoc] using h
  exact h'.tsum_eq

theorem summable_mobiusLogInversion {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hmono : Monotone g)
    {u : ℝ} (hu : 0 ≤ u) :
    Summable (fun k : ℕ => (moebius k : ℝ) / (k : ℝ) ^ (2 : ℕ) * g (u / k)) := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (fun k => abs_nonneg _)
    (fun k => term_abs_le hg0 hmono hu k) (summable_scaled (g u))

/-- **Monotone Möbius positivity.**  If the prime-power density is nonnegative and nondecreasing,
the Möbius-inverted prime density is at least `(2 - π²/6)` times it, hence nonnegative. -/
theorem mobiusLogInversion_ge {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hmono : Monotone g)
    {u : ℝ} (hu : 0 ≤ u) :
    (2 - Real.pi ^ (2 : ℕ) / 6) * g u ≤ mobiusLogInversion g u := by
  classical
  set f : ℕ → ℝ := fun k => (moebius k : ℝ) / (k : ℝ) ^ (2 : ℕ) * g (u / k) with hf
  set T : ℕ → ℝ := fun k => if k = 1 then 0 else f k with hT
  set B : ℕ → ℝ := fun k => if k = 1 then 0 else g u / (k : ℝ) ^ (2 : ℕ) with hB
  have hsum : Summable f := summable_mobiusLogInversion hg0 hmono hu
  have hTle : ∀ k, |T k| ≤ B k := by
    intro k
    by_cases hk : k = 1
    · simp [hT, hB, hk]
    · simp only [hT, hB, if_neg hk]
      exact term_abs_le hg0 hmono hu k
  have hBnonneg : ∀ k, 0 ≤ B k := by
    intro k
    by_cases hk : k = 1
    · simp [hB, hk]
    · simp only [hB, if_neg hk]
      have : 0 ≤ g u := hg0 u
      positivity
  have hBle : ∀ k, B k ≤ g u / (k : ℝ) ^ (2 : ℕ) := by
    intro k
    by_cases hk : k = 1
    · simp only [hB, hk]
      have : 0 ≤ g u := hg0 u
      positivity
    · simp [hB, if_neg hk]
  have hBsummable : Summable B :=
    Summable.of_nonneg_of_le hBnonneg hBle (summable_scaled (g u))
  have hBsummable' : Summable B := hBsummable
  have hTabs : Summable (fun k => |T k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hTle hBsummable'
  have hTsummable : Summable T := Summable.of_abs hTabs
  have hBtsum : (∑' k, B k) = g u * (Real.pi ^ (2 : ℕ) / 6) - g u := by
    have hsplit := (summable_scaled (g u)).tsum_eq_add_tsum_ite 1
    rw [tsum_scaled] at hsplit
    have : (∑' k : ℕ, if k = 1 then 0 else g u / (k : ℝ) ^ (2 : ℕ))
        = g u * (Real.pi ^ (2 : ℕ) / 6) - g u / (1 : ℝ) ^ (2 : ℕ) := by
      linarith [hsplit]
    simpa [hB] using this
  have htail : -(g u * (Real.pi ^ (2 : ℕ) / 6) - g u) ≤ ∑' k, T k := by
    have h1 : |∑' k, T k| ≤ ∑' k, |T k| := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := T) (by simpa using hTabs)
    have h2 : (∑' k, |T k|) ≤ ∑' k, B k :=
      Summable.tsum_le_tsum hTle hTabs hBsummable'
    rw [hBtsum] at h2
    have := abs_le.mp (h1.trans h2)
    linarith [this.1]
  have hsplitf : mobiusLogInversion g u = f 1 + ∑' k, T k := by
    rw [mobiusLogInversion]
    simpa [hT] using hsum.tsum_eq_add_tsum_ite 1
  have hf1 : f 1 = g u := by simp [hf]
  rw [hsplitf, hf1]
  linarith [htail]

end GaloisForLFunctions.HTGeometry
