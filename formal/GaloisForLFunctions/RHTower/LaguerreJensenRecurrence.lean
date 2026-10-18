import GaloisForLFunctions.RHTower.ScaledTerminatingHypergeometricLimit

/-!
# The finite factorial-ratio Jensen recurrence

The exact three-term recurrence is the algebraic part of the Jensen–Hermite
limit. No coefficient asymptotics are assumed.
-/

open Polynomial Finset

noncomputable section

namespace RHTower

def laguerreJensenRatio (b : ℝ) (j : ℕ) : ℝ :=
  b ^ j / ScaledHypergeometric.rising b j

theorem laguerreJensenRatio_zero (b : ℝ) : laguerreJensenRatio b 0 = 1 := by
  simp [laguerreJensenRatio]

theorem laguerreJensenRatio_one {b : ℝ} (hb : 0 < b) : laguerreJensenRatio b 1 = 1 := by
  simp [laguerreJensenRatio, ScaledHypergeometric.rising_succ, hb.ne']

theorem laguerreJensenRatio_succ {b : ℝ} (hb : 0 < b) (j : ℕ) :
    (b + j) * laguerreJensenRatio b (j + 1) = b * laguerreJensenRatio b j := by
  have hr := ScaledHypergeometric.rising_pos hb j
  have hbj : 0 < b + j := by positivity
  rw [laguerreJensenRatio, laguerreJensenRatio, ScaledHypergeometric.rising_succ, pow_succ]
  field_simp

def laguerreJensen (b : ℝ) (d : ℕ) : ℝ[X] :=
  ∑ j ∈ range (d + 1), monomial j ((d.choose j : ℝ) * laguerreJensenRatio b j)

theorem coeff_laguerreJensen (b : ℝ) (d j : ℕ) :
    (laguerreJensen b d).coeff j = (d.choose j : ℝ) * laguerreJensenRatio b j := by
  unfold laguerreJensen
  simp only [finsetSum_coeff, coeff_monomial]
  by_cases hj : j < d + 1
  · simp [hj]
  · have hdj : d < j := by omega
    simp [hj, Nat.choose_eq_zero_of_lt hdj]

theorem laguerreJensen_zero (b : ℝ) : laguerreJensen b 0 = 1 := by
  ext j
  cases j <;> simp [coeff_laguerreJensen, laguerreJensenRatio_zero, coeff_one]

theorem laguerreJensen_one {b : ℝ} (hb : 0 < b) : laguerreJensen b 1 = 1 + X := by
  ext j
  rcases j with _ | (_ | j)
  · simp [coeff_laguerreJensen, laguerreJensenRatio_zero]
  · simp [coeff_laguerreJensen, laguerreJensenRatio_one hb, coeff_one]
  · simp [coeff_laguerreJensen, coeff_one, coeff_X,
      Nat.choose_eq_zero_of_lt (show 1 < j + 1 + 1 by omega)]

private theorem real_choose_mul_succ (d k : ℕ) :
    ((d : ℝ) + 1) * (d.choose k : ℝ) =
      ((d : ℝ) + 1 - k) * ((d + 1).choose k : ℝ) := by
  by_cases hk : k ≤ d + 1
  · have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_mul_succ_eq d k)
    push_cast [Nat.cast_sub hk] at h
    nlinarith
  · have hd : d < k := by omega
    have hd1 : d + 1 < k := by omega
    simp [Nat.choose_eq_zero_of_lt hd, Nat.choose_eq_zero_of_lt hd1]

/-- The terminating Laguerre recurrence, including every coefficient. -/
theorem laguerreJensen_add_two {b : ℝ} (hb : 0 < b) (d : ℕ) :
    C (b + (d : ℝ) + 1) * laguerreJensen b (d + 2) =
      (C (b + 2 * (d : ℝ) + 2) + C b * X) * laguerreJensen b (d + 1) -
        C ((d : ℝ) + 1) * laguerreJensen b d := by
  ext j
  rw [add_mul, mul_assoc]
  cases j with
  | zero =>
    simp only [coeff_C_mul, coeff_sub, coeff_add, coeff_X_mul_zero,
      coeff_laguerreJensen, Nat.choose_zero_right, Nat.cast_one,
      laguerreJensenRatio_zero, mul_one, mul_zero, add_zero]
    ring
  | succ k =>
    simp only [coeff_C_mul, coeff_sub, coeff_add, coeff_X_mul, coeff_laguerreJensen]
    have hpascal₁ : ((d + 2).choose (k + 1) : ℝ) =
        ((d + 1).choose k : ℝ) + ((d + 1).choose (k + 1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ (d + 1) k
    have hpascal₂ : ((d + 1).choose (k + 1) : ℝ) =
        (d.choose k : ℝ) + (d.choose (k + 1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ d k
    have hc := congrArg (fun a : ℝ => a * laguerreJensenRatio b (k + 1))
      (real_choose_mul_succ d k)
    have hr := congrArg (fun a : ℝ => ((d + 1).choose k : ℝ) * a)
      (laguerreJensenRatio_succ hb k)
    rw [hpascal₁, hpascal₂]
    nlinarith

end RHTower
