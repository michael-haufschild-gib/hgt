import GaloisForLFunctions.RHTower.RouteJResidualFirstDifferenceForm

/-!
# The diagonal boost moments are Legendre polynomials

With the explicit Legendre polynomial
`P_N(x) = Σ_{k ≤ N/2} (−1)^k (2N−2k)! / (2^N k! (N−k)! (N−2k)!) x^{N−2k}`,
the Pfaff `σ`-form of the diagonal cosine moments reads

`∫ p_n² cos(δ s) dμ = (cosh δ)^{-1/2} P_{2n}(sech δ)`.

Consequently the first-order response of the Route J residual to the mode `cos(δ s)` is an exact
combination of `P_{4k}, …, P_{4k+8}` at `sech δ`, which is the object of the beat-mode profile
(MUST-150).
-/

open Finset
open scoped BigOperators

namespace RHTower

namespace LegendreBoost

open ScaledHypergeometric RouteJProfile CosineModeResponse

/-- The coefficient of `x^{N−2k}` in the Legendre polynomial `P_N` (zero for `2k > N`). -/
noncomputable def legendreCoeff (N k : ℕ) : ℝ :=
  if 2 * k ≤ N then
    (-1) ^ k * ((2 * N - 2 * k).factorial : ℝ) /
      (2 ^ N * (k.factorial : ℝ) * ((N - k).factorial : ℝ) * ((N - 2 * k).factorial : ℝ))
  else 0

/-- The Legendre polynomial `P_N(x)` (explicit formula). -/
noncomputable def legendre (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), legendreCoeff N k * x ^ (N - 2 * k)

theorem legendreCoeff_eq_zero_of_lt {N k : ℕ} (h : N < 2 * k) : legendreCoeff N k = 0 := by
  unfold legendreCoeff
  rw [if_neg (by omega)]

theorem legendreCoeff_two_mul (n j : ℕ) (hj : j ≤ n) :
    legendreCoeff (2 * n) (n - j) =
      (-1) ^ n * cb n * ((-1) ^ j * fallingNat n j * rising ((n : ℝ) + 1 / 2) j /
        (rising (1 / 2) j * j.factorial)) := by
  unfold legendreCoeff cb
  rw [if_pos (by omega), normalizedCentralBinom_eq_rising_half_div, fallingNat_eq_factorial_mul_choose]
  have hA : rising (1 / 2) (n + j) = rising (1 / 2) n * rising ((n : ℝ) + 1 / 2) j := by
    rw [rising_add, show (1 / 2 : ℝ) + n = (n : ℝ) + 1 / 2 by ring]
  have h1 := rising_half_mul_factorial n
  have h2 := rising_half_mul_factorial j
  have h3 := rising_half_mul_factorial (n + j)
  have hch := Nat.choose_mul_factorial_mul_factorial hj
  have hchR : (n.choose j : ℝ) * j.factorial * (n - j).factorial = n.factorial := by exact_mod_cast hch
  rw [show 2 * (2 * n) - 2 * (n - j) = 2 * (n + j) by omega, show 2 * n - (n - j) = n + j by omega,
    show 2 * n - 2 * (n - j) = 2 * j by omega]
  have hsign : ((-1 : ℝ)) ^ (n - j) = (-1) ^ n * (-1) ^ j := by
    have : (-1 : ℝ) ^ n = (-1) ^ (n - j) * (-1) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    have hj2 : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    calc (-1 : ℝ) ^ (n - j) = (-1) ^ (n - j) * ((-1) ^ j * (-1) ^ j) := by rw [hj2, mul_one]
      _ = (-1) ^ n * (-1) ^ j := by rw [← mul_assoc, ← this]
  rw [hsign]
  have hr1 : rising (1 / 2) n ≠ 0 := (rising_pos (by norm_num) n).ne'
  have hr2 : rising (1 / 2) j ≠ 0 := (rising_pos (by norm_num) j).ne'
  have hf1 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hf2 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hf3 : ((n - j).factorial : ℝ) ≠ 0 := by exact_mod_cast (n - j).factorial_ne_zero
  have hf4 : ((n + j).factorial : ℝ) ≠ 0 := by exact_mod_cast (n + j).factorial_ne_zero
  have hf5 : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast (2 * j).factorial_ne_zero
  have h4 : (2 : ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  have hc : (n.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  -- express the factorial of 2(n+j), 2n, 2j through the rising factorials
  have e3 : ((2 * (n + j)).factorial : ℝ) = 4 ^ (n + j) * (rising (1 / 2) (n + j) * (n + j).factorial) := by
    rw [h3]; field_simp
  have e2 : ((2 * j).factorial : ℝ) = 4 ^ j * (rising (1 / 2) j * j.factorial) := by
    rw [h2]; field_simp
  rw [e3, e2, hA, ← hchR, h4]
  field_simp
  ring

/-- **`P_{2n}(σ) = (−1)^n C_n ₂F₁(−n, n+½; ½; σ²)`.** -/
theorem legendre_two_mul_eq (n : ℕ) (σ : ℝ) :
    legendre (2 * n) σ = (-1) ^ n * cb n * hypSumSq n (1 / 2) (1 / 2) (σ ^ 2) := by
  unfold legendre hypSumSq
  rw [← sum_range_add_sum_Ico _ (by omega : n + 1 ≤ 2 * n + 1)]
  rw [sum_eq_zero (s := Ico (n + 1) (2 * n + 1)) (fun k hk => by
    rw [mem_Ico] at hk
    rw [legendreCoeff_eq_zero_of_lt (by omega)]
    ring), add_zero, ← sum_range_reflect, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [show n + 1 - 1 - j = n - j by omega, legendreCoeff_two_mul n j (by omega),
    show 2 * n - 2 * (n - j) = 2 * j by omega, pow_mul]
  ring

/-- **The diagonal boost moments are Legendre polynomials:**
`∫ p_n² cos(δ s) dμ = (cosh δ)^{-1/2} P_{2n}(sech δ)`. -/
theorem cosineDiagonalMoment_eq_legendre (δ : ℝ) (n : ℕ) :
    cosineDiagonalMoment δ n = Real.cosh δ ^ (-(1 / 2 : ℝ)) * legendre (2 * n) (1 / Real.cosh δ) := by
  rw [cosineDiagonalMoment_eq_cb, legendre_two_mul_eq]
  unfold Fh RouteJProfile.sq
  ring

/-- **The Route J residual response as a Legendre combination.** -/
theorem residualJetOf_cosineMode_eq_legendre (δ : ℝ) (k : ℕ) :
    residualJetOf (cosineModeDeterminantJet δ) k =
      Real.cosh δ ^ (-(1 / 2 : ℝ)) *
        (semilocalArchimedeanJacobiCoefficient (2 * k) * semilocalArchimedeanJacobiCoefficient (2 * k + 1) *
            (legendre (4 * k + 4) (1 / Real.cosh δ) - legendre (4 * k) (1 / Real.cosh δ)) -
          2 * semilocalArchimedeanJacobiCoefficient (2 * k + 1) ^ 2 *
            (legendre (4 * k + 4) (1 / Real.cosh δ) - legendre (4 * k + 2) (1 / Real.cosh δ)) -
          2 * semilocalArchimedeanJacobiCoefficient (2 * k + 2) ^ 2 *
            (legendre (4 * k + 6) (1 / Real.cosh δ) - legendre (4 * k + 4) (1 / Real.cosh δ)) +
          semilocalArchimedeanJacobiCoefficient (2 * k + 2) * semilocalArchimedeanJacobiCoefficient (2 * k + 3) *
            (legendre (4 * k + 8) (1 / Real.cosh δ) - legendre (4 * k + 4) (1 / Real.cosh δ))) := by
  unfold residualJetOf
  simp only [radiusJetOf_cosineMode, cosineDiagonalMoment_eq_legendre]
  simp only [show 2 * (2 * k) = 4 * k by ring, show 2 * (2 * k + 1) = 4 * k + 2 by ring,
    show 2 * (2 * k + 1 + 1) = 4 * k + 4 by ring,
    show 2 * (2 * k + 2 + 1) = 4 * k + 6 by ring,
    show 2 * (2 * k + 3 + 1) = 4 * k + 8 by ring]
  ring

end LegendreBoost

end RHTower
