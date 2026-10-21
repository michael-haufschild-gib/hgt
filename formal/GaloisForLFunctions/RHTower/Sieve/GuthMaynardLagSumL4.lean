import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSumL2

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 8.3 for `R`: the fourth moment is controlled by the additive energy

For every finite set `W ⊂ ℝ` and every window `[A⁻¹, A]` (`A ≥ 1`),

`∫_{A⁻¹}^{A} |R(v)|⁴ dv ≤ (5π/2) · A · max(1, log A) · E(W)`,

with `E(W) = #{(t₁, t₂, t₃, t₄) ∈ W⁴ : |t₁ + t₂ − t₃ − t₄| ≤ 1}`. This is the `R`-half of
Lemma 8.3 of Guth–Maynard (`∫_{v ≍ 1} |R(v)|⁴ dv ⪅ E(W)`), without the `T^{o(1)}` loss and
without any separation hypothesis.

Proof. `R(e^u)² = Σ_{(t₁,t₂) ∈ W²} e^{i(t₁+t₂)u}` is a unit-coefficient exponential sum over pairs,
so the window mean value inequality of `GuthMaynardLagSumL2` bounds `∫|R(e^u)|⁴` by the number of
quadruples with `|t₁ + t₂ − t₃ − t₄| < 1`, which is at most `E(W)`.
-/

open MeasureTheory Set Finset

namespace RHTower.GuthMaynard

noncomputable section

/-- `R(e^u)²` is the unit-coefficient exponential sum over pairs with frequencies
`(t₁ + t₂)/2π`. -/
theorem lagSum_exp_sq_eq_finiteFrequencyPoly (W : Finset ℝ) (u : ℝ) :
    lagSum W (Real.exp u) ^ 2 =
      Sieve.finiteFrequencyPoly (fun _ => 1) (W ×ˢ W)
        (fun p => (p.1 + p.2) / (2 * Real.pi)) u := by
  rw [sq, lagSum_exp, sum_mul_sum, Sieve.finiteFrequencyPoly, sum_product]
  refine sum_congr rfl fun t₁ _ => sum_congr rfl fun t₂ _ => ?_
  have h : 2 * Real.pi * (u * ((t₁ + t₂) / (2 * Real.pi))) = (t₁ + t₂) * u := by
    field_simp
  rw [one_mul, ← Complex.exp_add, h]
  push_cast
  ring_nf

/-- The pair collisions at a scale `δ` with `2πδ ≤ 1` are additive-energy quadruples. -/
theorem pairCollisionWeight_le_additiveEnergy (W : Finset ℝ) {δ : ℝ}
    (hδ1 : 2 * Real.pi * δ ≤ 1) :
    Sieve.finiteFrequencyCollisionWeight (fun _ => (1 : ℂ)) (W ×ˢ W)
        (fun p => (p.1 + p.2) / (2 * Real.pi)) δ
      ≤ additiveEnergy W := by
  have hterm : ∀ t₁ t₂ t₃ t₄ : ℝ,
      (if |(t₁ + t₂) / (2 * Real.pi) - (t₃ + t₄) / (2 * Real.pi)| < δ
        then ‖(1 : ℂ)‖ * ‖(1 : ℂ)‖ else 0)
        ≤ if |t₁ + t₂ - t₃ - t₄| ≤ 1 then (1 : ℝ) else 0 := by
    intro t₁ t₂ t₃ t₄
    split_ifs with h h'
    · simp
    · refine absurd ?_ h'
      rw [← sub_div, abs_div, abs_of_pos Real.two_pi_pos, div_lt_iff₀ Real.two_pi_pos] at h
      have : |t₁ + t₂ - (t₃ + t₄)| ≤ 1 := by
        calc |t₁ + t₂ - (t₃ + t₄)| ≤ δ * (2 * Real.pi) := h.le
          _ = 2 * Real.pi * δ := by ring
          _ ≤ 1 := hδ1
      rwa [show t₁ + t₂ - (t₃ + t₄) = t₁ + t₂ - t₃ - t₄ by ring] at this
    · positivity
    · exact le_rfl
  unfold additiveEnergy
  rw [Sieve.finiteFrequencyCollisionWeight, card_filter]
  push_cast
  simp only [sum_product]
  refine sum_le_sum fun t₁ _ => sum_le_sum fun t₂ _ => sum_le_sum fun t₃ _ =>
    sum_le_sum fun t₄ _ => ?_
  exact hterm t₁ t₂ t₃ t₄

/-- **Guth–Maynard Lemma 8.3 for `R`, explicit form.** For every finite `W ⊂ ℝ` and `A ≥ 1`:
`∫_{A⁻¹}^{A} |R(v)|⁴ dv ≤ (5π/2) · A · max(1, log A) · E(W)`. -/
theorem setIntegral_Icc_inv_lagSum_pow_four_le {A : ℝ} (hA : 1 ≤ A) (W : Finset ℝ) :
    ∫ v in Icc A⁻¹ A, ‖lagSum W v‖ ^ 4
      ≤ 5 * Real.pi / 2 * A * max 1 (Real.log A) * additiveEnergy W := by
  have hcont : Continuous fun u => ‖lagSum W (Real.exp u)‖ ^ 4 :=
    (continuous_lagSum_exp W).norm.pow 4
  have hweight := pairCollisionWeight_le_additiveEnergy W (two_pi_mul_windowScale_le A)
  have hL : (0 : ℝ) ≤ 5 * Real.pi / 2 * max 1 (Real.log A) :=
    mul_nonneg (by positivity) (le_trans zero_le_one (le_max_left _ _))
  have hfour : ∀ u, ‖lagSum W (Real.exp u)‖ ^ 4
      = ‖Sieve.finiteFrequencyPoly (fun _ => 1) (W ×ˢ W)
          (fun p => (p.1 + p.2) / (2 * Real.pi)) u‖ ^ 2 := by
    intro u
    rw [← lagSum_exp_sq_eq_finiteFrequencyPoly, norm_pow]
    ring
  calc ∫ v in Icc A⁻¹ A, ‖lagSum W v‖ ^ 4
      ≤ A * ∫ u in Icc (-Real.log A) (Real.log A), ‖lagSum W (Real.exp u)‖ ^ 4 :=
        setIntegral_Icc_inv_le hA (fun v => by positivity) hcont.integrableOn_Icc
    _ = A * ∫ u in Icc (-Real.log A) (Real.log A),
          ‖Sieve.finiteFrequencyPoly (fun _ => 1) (W ×ˢ W)
            (fun p => (p.1 + p.2) / (2 * Real.pi)) u‖ ^ 2 := by
        simp_rw [hfour]
    _ ≤ A * (5 * Real.pi / 2 * max 1 (Real.log A) * additiveEnergy W) :=
        mul_le_mul_of_nonneg_left ((setIntegral_Icc_normSq_unitPoly_le (W ×ˢ W) _ A).trans
          (mul_le_mul_of_nonneg_left hweight hL)) (by linarith)
    _ = 5 * Real.pi / 2 * A * max 1 (Real.log A) * additiveEnergy W := by ring

/-- **Guth–Maynard Lemma 8.3 for `R`** in the paper's shape: for every window `[A⁻¹, A]` there
is an absolute constant `C` with `∫_{A⁻¹}^{A} |R(v)|⁴ dv ≤ C · E(W)` for every finite `W`. -/
theorem guthMaynard_lemma83_lagSum {A : ℝ} (hA : 1 ≤ A) :
    ∃ C ≥ 0, ∀ W : Finset ℝ, ∫ v in Icc A⁻¹ A, ‖lagSum W v‖ ^ 4 ≤ C * additiveEnergy W := by
  refine ⟨5 * Real.pi / 2 * A * max 1 (Real.log A), ?_, fun W =>
    setIntegral_Icc_inv_lagSum_pow_four_le hA W⟩
  exact mul_nonneg (mul_nonneg (by positivity) (by linarith))
    (le_trans zero_le_one (le_max_left _ _))

end

end RHTower.GuthMaynard
