import GaloisForLFunctions.ArithmeticKreinLangerTheory.MultivariateParityAuxiliariesReachTheMainTerm
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheForcedJumpsOfAProducer

/-!
# Quantitative cost of parity-selective factorial producers

The Möbius–Farkas producer has an explicit alphabet radius depending on the slope excess.
Its Stirling error is polynomial in that radius. Clearing denominators introduces no extra
normalized cost: both the slope and the required prime multiplicity scale by that denominator.
-/

open Finset
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section
namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-- Explicit alphabet radius for slope excess `ε` and absolute scale constant `K`. -/
def producerRadius (K ε : ℝ) : ℕ :=
  producerPeriod (ε / 2) (Nat.ceil (K / ε) + 10)

/-- The normalized Stirling cost at the explicit alphabet radius. -/
def producerCost (K ε : ℝ) : ℝ :=
  8 * (producerRadius K ε : ℝ) ^ 3 * (5 + Real.log (producerRadius K ε))

theorem producerPeriod_pos (ε : ℝ) (ℓ : ℕ) : 0 < producerPeriod ε ℓ := by
  unfold producerPeriod
  exact Nat.mul_pos (pow_pos zero_lt_two _) (Nat.factorial_pos _)

theorem producerCost_pos (K ε : ℝ) : 0 < producerCost K ε := by
  have hP : 0 < producerRadius K ε := producerPeriod_pos _ _
  have hPR : (0 : ℝ) < producerRadius K ε := by exact_mod_cast hP
  have hlog : 0 ≤ Real.log (producerRadius K ε) := Real.log_natCast_nonneg _
  unfold producerCost
  positivity

/-- Uniform quantitative dependence on the slope excess for an actual integer producer. -/
theorem exists_producer_with_quantitative_cost :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧
        normSlope c m B < 1 + ε ∧ AlphabetLE c (producerRadius K ε) ∧
        stencilErrorConst c / m ≤ producerCost K ε := by
  obtain ⟨K, hK, hprod⟩ := exists_producer_with_quantitative_support
  refine ⟨K, hK, fun ε hε hε1 => ?_⟩
  obtain ⟨c, m, B, hc0, hbal, hm, hB, hn, hw, hs, _, hdvd⟩ := hprod ε hε hε1
  have hP : IsProducer c m B := ⟨hc0, hbal, hn, hm, hB, hw⟩
  have hA : normSlope c m B < 1 + ε := hs
  have halphabet : AlphabetLE c (producerRadius K ε) := fun k hk =>
    Nat.le_of_dvd (producerPeriod_pos _ _) (hdvd k hk)
  have hS : stencilSlope c ≤ 2 * m := by
    have heq : stencilSlope c = normSlope c m B * ((m : ℝ) * (1 - 1 / (B : ℝ))) := by
      rw [normSlope, div_mul_cancel₀ _ (mul_pos hP.m_pos hP.one_sub_pos).ne']
    have hbound : (m : ℝ) * (1 - 1 / (B : ℝ)) ≤ m := by
      have : 0 ≤ (m : ℝ) / (B : ℝ) := by positivity
      linarith
    rw [heq]
    calc normSlope c m B * ((m : ℝ) * (1 - 1 / (B : ℝ)))
        ≤ 2 * ((m : ℝ) * (1 - 1 / (B : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_pos hP.m_pos hP.one_sub_pos).le
      _ ≤ 2 * m := mul_le_mul_of_nonneg_left hbound (by norm_num)
  refine ⟨c, m, B, hP, hA, halphabet, ?_⟩
  rw [div_le_iff₀ hP.m_pos]
  have hE := hP.stencilErrorConst_le halphabet
  have hlog : 0 ≤ Real.log (producerRadius K ε) := Real.log_natCast_nonneg _
  have hfac : 0 ≤ (producerRadius K ε : ℝ) ^ 3 *
      (5 + Real.log (producerRadius K ε)) := by positivity
  unfold producerCost
  nlinarith [mul_le_mul_of_nonneg_right hS hfac]

/-- The factorial construction yields a prime-count bound with one explicit cost function
for every `ε`; only its absolute scale constant is unspecified. -/
theorem exists_psi_le_quantitative_producer_cost :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : ℝ, 1 ≤ x →
      Chebyshev.psi x ≤ (1 + ε) * x +
        producerCost K ε * (1 + Real.log x) * (1 + Real.log x / Real.log 2) := by
  obtain ⟨K, hK, hprod⟩ := exists_producer_with_quantitative_cost
  refine ⟨K, hK, fun ε hε hε1 x hx => ?_⟩
  obtain ⟨c, m, B, hP, hA, halphabet, _⟩ := hprod ε hε hε1
  have h := hP.psi_le_of_alphabet halphabet (by linarith : normSlope c m B ≤ 2) hx
  have hmain := mul_le_mul_of_nonneg_right hA.le (by linarith : 0 ≤ x)
  exact h.trans (add_le_add_right hmain _)

end GaloisForLFunctions.ArithmeticKreinLangerTheory
