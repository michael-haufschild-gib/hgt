import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A closed one-frequency instance of Matsumoto--Suzuki Proposition 4.1

For the unit positive frequency, the paper's function is
`g(t) = exp (- i t) - 1`.  This file proves the source kernel identity and
its finite Gram nonnegativity directly.  The spectrum, coefficient, and
positivity are all concrete: no analytic or RH premise is used.

Source: Matsumoto--Suzuki, arXiv:2409.00888v2, Proposition 4.1, equation (4.2).
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The paper's one-frequency, unit-coefficient phase increment. -/
def matsumotoSuzukiPhase (t : ℝ) : ℂ :=
  Complex.exp (-((t : ℂ) * Complex.I)) - 1

/-- The one-frequency source function `g(t) = exp(-it) - 1`. -/
def matsumotoSuzukiOneFrequencyScrew (t : ℝ) : ℂ :=
  matsumotoSuzukiPhase t

/-- The source kernel `g(t-u) - g(t) - g(-u) + g(0)`. -/
def matsumotoSuzukiProposition4_1Kernel (t u : ℝ) : ℂ :=
  matsumotoSuzukiOneFrequencyScrew (t - u) - matsumotoSuzukiOneFrequencyScrew t -
    matsumotoSuzukiOneFrequencyScrew (-u) + matsumotoSuzukiOneFrequencyScrew 0

private theorem star_matsumotoSuzukiPhase (u : ℝ) :
    star (matsumotoSuzukiPhase u) = Complex.exp ((u : ℂ) * Complex.I) - 1 := by
  unfold matsumotoSuzukiPhase
  change (starRingEnd ℂ) (Complex.exp (-((u : ℂ) * Complex.I)) - 1) = _
  rw [map_sub, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_one]
  ring_nf

private theorem matsumotoSuzukiPhase_sub (t u : ℝ) :
    matsumotoSuzukiPhase (t - u) =
      Complex.exp (-((t : ℂ) * Complex.I)) * Complex.exp ((u : ℂ) * Complex.I) - 1 := by
  unfold matsumotoSuzukiPhase
  have harg : -(((t - u : ℝ) : ℂ) * Complex.I) =
      -((t : ℂ) * Complex.I) + (u : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

private theorem matsumotoSuzukiPhase_neg (u : ℝ) :
    matsumotoSuzukiPhase (-u) = Complex.exp ((u : ℂ) * Complex.I) - 1 := by
  unfold matsumotoSuzukiPhase
  congr 2
  push_cast
  ring

/-- Source equation (4.2), specialized to the unit positive frequency. -/
theorem matsumotoSuzukiProposition4_1_kernel_factor (t u : ℝ) :
    matsumotoSuzukiProposition4_1Kernel t u =
      matsumotoSuzukiPhase t * star (matsumotoSuzukiPhase u) := by
  unfold matsumotoSuzukiProposition4_1Kernel matsumotoSuzukiOneFrequencyScrew
  rw [matsumotoSuzukiPhase_sub, matsumotoSuzukiPhase_neg,
    show matsumotoSuzukiPhase 0 = 0 by simp [matsumotoSuzukiPhase],
    star_matsumotoSuzukiPhase]
  unfold matsumotoSuzukiPhase
  ring

private theorem oneFrequency_factor_gram
    (n : ℕ) (t : Fin n → ℝ) (ξ : Fin n → ℂ) :
    ∑ i, ∑ j,
        (matsumotoSuzukiPhase (t i) * star (matsumotoSuzukiPhase (t j))) * ξ i * star (ξ j) =
      (∑ i, matsumotoSuzukiPhase (t i) * ξ i) *
        star (∑ i, matsumotoSuzukiPhase (t i) * ξ i) := by
  classical
  calc
    ∑ i, ∑ j,
        (matsumotoSuzukiPhase (t i) * star (matsumotoSuzukiPhase (t j))) * ξ i * star (ξ j) =
        ∑ i, ∑ j,
          (matsumotoSuzukiPhase (t i) * ξ i) *
            star (matsumotoSuzukiPhase (t j) * ξ j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [star_mul]
      ring
    _ = ∑ i, (matsumotoSuzukiPhase (t i) * ξ i) *
        ∑ j, star (matsumotoSuzukiPhase (t j) * ξ j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = (∑ i, matsumotoSuzukiPhase (t i) * ξ i) *
        ∑ j, star (matsumotoSuzukiPhase (t j) * ξ j) := by
      rw [Finset.sum_mul]
    _ = (∑ i, matsumotoSuzukiPhase (t i) * ξ i) *
        star (∑ i, matsumotoSuzukiPhase (t i) * ξ i) := by
      have hstar : star (∑ i, matsumotoSuzukiPhase (t i) * ξ i) =
          ∑ i, star (matsumotoSuzukiPhase (t i) * ξ i) := by
        exact map_sum (starRingEnd ℂ) _ Finset.univ
      rw [hstar]

/-- The concrete source Gram form is exactly a squared complex norm. -/
theorem matsumotoSuzukiProposition4_1_oneFrequency_gram
    (n : ℕ) (t : Fin n → ℝ) (ξ : Fin n → ℂ) :
    (∑ i, ∑ j,
        matsumotoSuzukiProposition4_1Kernel (t i) (t j) * ξ i * star (ξ j)).re =
      ‖∑ i, matsumotoSuzukiPhase (t i) * ξ i‖ ^ (2 : ℕ) := by
  rw [show (∑ i, ∑ j,
      matsumotoSuzukiProposition4_1Kernel (t i) (t j) * ξ i * star (ξ j)) =
      ∑ i, ∑ j,
        (matsumotoSuzukiPhase (t i) * star (matsumotoSuzukiPhase (t j))) * ξ i * star (ξ j) by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [matsumotoSuzukiProposition4_1_kernel_factor], oneFrequency_factor_gram]
  change (((∑ i, matsumotoSuzukiPhase (t i) * ξ i) *
    (starRingEnd ℂ) (∑ i, matsumotoSuzukiPhase (t i) * ξ i)).re) = _
  rw [Complex.mul_conj]
  change Complex.normSq (∑ i, matsumotoSuzukiPhase (t i) * ξ i) = _
  rw [Complex.sq_norm]

/-- Fully discharged one-frequency instance of Matsumoto--Suzuki Proposition 4.1. -/
theorem matsumotoSuzukiProposition4_1_oneFrequency_gram_nonneg
    (n : ℕ) (t : Fin n → ℝ) (ξ : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j,
      matsumotoSuzukiProposition4_1Kernel (t i) (t j) * ξ i * star (ξ j)).re := by
  rw [matsumotoSuzukiProposition4_1_oneFrequency_gram]
  exact sq_nonneg _

end

end GaloisForLFunctions.RHTower
