import GaloisForLFunctions.RHTower.ZetaChiStationaryLeadingTerm

open Complex MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Integer saddles give a common leading direction for every finite
complex-coefficient physical sum. The entire coefficient-weighted remainder
is retained, including when the support grows with the height. -/
theorem exists_zetaChi_coherent_integral_sum :
    ∃ ψ : ℂ, ‖ψ‖ = 1 ∧ ∀ S : Finset ℕ, ∀ c : ℕ → ℂ, ∀ h : ℕ → ℝ, ∀ l u : ℝ,
      (∀ n ∈ S, 0 < n ∧ 8 ≤ 2 * Real.pi * n ∧ 0 < h n ∧
        h n ≤ (2 * Real.pi * n) / 2 ∧ (2 * Real.pi * n) / 2 ≤ l ∧
        l ≤ 2 * Real.pi * n - h n ∧ 2 * Real.pi * n + h n ≤ u ∧ u ≤ 2 * (2 * Real.pi * n)) →
      ‖(∫ t in l..u, ∑ n ∈ S, c n *
          (zetaChi (linePt t) * bourgainOscillation (t * Real.log n))) -
        ψ * ∑ n ∈ S, c n * (Real.sqrt (2 * Real.pi * (2 * Real.pi * n)) : ℂ)‖ ≤
      ∑ n ∈ S, ‖c n‖ * (78 + 4 * (h n) ^ 4 / (2 * Real.pi * n) ^ 2 +
        40 * (2 * Real.pi * n) / h n) := by
  obtain ⟨κ, hκ, hk⟩ := exists_zetaChi_stationary_leading_term
  let ψ : ℂ := κ * bourgainOscillation (-(Real.pi / 4))
  have hψ : ‖ψ‖ = 1 := by rw [norm_mul, hκ, norm_bourgainOscillation, mul_one]
  refine ⟨ψ, hψ, ?_⟩
  intro S c h l u hS
  have hsingle (n : ℕ) (hnS : n ∈ S) :
      ‖(∫ t in l..u, zetaChi (linePt t) * bourgainOscillation (t * Real.log n)) -
        ψ * (Real.sqrt (2 * Real.pi * (2 * Real.pi * n)) : ℂ)‖ ≤
      78 + 4 * (h n) ^ 4 / (2 * Real.pi * n) ^ 2 + 40 * (2 * Real.pi * n) / h n := by
    obtain ⟨_hn, h8, hh, hhalf, hl, hlh, hhu, hu⟩ := hS n hnS
    have hb := hk (2 * Real.pi * n) (h n) l u h8 hh hhalf hl hlh hhu hu
    have hdiv : (2 * Real.pi * (n : ℝ)) / (2 * Real.pi) = n := by field_simp
    have hperiod : bourgainOscillation (2 * Real.pi * n) = 1 := by
      unfold bourgainOscillation
      have he : I * ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) =
          (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by push_cast; ring
      rw [he, Complex.exp_nat_mul_two_pi_mul_I]
    rw [hdiv, hperiod, mul_one] at hb
    have he : κ * ((Real.sqrt (2 * Real.pi * (2 * Real.pi * n)) : ℂ) *
        bourgainOscillation (-(Real.pi / 4))) =
        ψ * (Real.sqrt (2 * Real.pi * (2 * Real.pi * n)) : ℂ) := by
      dsimp only [ψ]
      ring
    rw [he] at hb
    exact hb
  have hcont (n : ℕ) : Continuous (fun t : ℝ =>
      zetaChi (linePt t) * bourgainOscillation (t * Real.log n)) := by
    convert continuous_zetaChiCriticalTwistIntegrand (Real.log n) using 1
    funext t
    unfold bourgainOscillation
    congr 1
    congr 1
    push_cast
    ring
  have hint : (∫ t in l..u, ∑ n ∈ S, c n *
      (zetaChi (linePt t) * bourgainOscillation (t * Real.log n))) =
      ∑ n ∈ S, c n * ∫ t in l..u, zetaChi (linePt t) * bourgainOscillation (t * Real.log n) := by
    rw [intervalIntegral.integral_finsetSum
      (fun n _ => ((hcont n).const_mul (c n)).intervalIntegrable l u)]
    simp_rw [intervalIntegral.integral_const_mul]
  have he : (∫ t in l..u, ∑ n ∈ S, c n *
      (zetaChi (linePt t) * bourgainOscillation (t * Real.log n))) -
      ψ * ∑ n ∈ S, c n * (Real.sqrt (2 * Real.pi * (2 * Real.pi * n)) : ℂ) =
      ∑ n ∈ S, c n * ((∫ t in l..u, zetaChi (linePt t) * bourgainOscillation (t * Real.log n)) -
        ψ * (Real.sqrt (2 * Real.pi * (2 * Real.pi * n)) : ℂ)) := by
    rw [hint, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hsingle n hn) (norm_nonneg _)

end RHTower
