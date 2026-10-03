import GaloisForLFunctions.HTGeometry.BBPProductOpenCore

/-!
# The four BBP series and the sharpness of the joint reduction

With `S_j = Σ_k 16^{−k}/(8k+j)`, the BBP formula reads `π = 4 S₁ − 2 S₄ − S₅ − S₆`
(`pi_eq_four_series`), so `e(h 16ⁿ π)` is the joint phase of `(16ⁿS₁, 16ⁿS₄, 16ⁿS₅, 16ⁿS₆)` at
the integer vector `h (4, −2, −1, −1)` (`exp_sixteen_pow_pi_eq_prod`).  The Weyl sums of `π` are
therefore exactly the joint Weyl sums along the multiples of `(4, −2, −1, −1)`.

* `not_parityDriftHypothesis_pi_of_jointWeylSums`: if these joint sums vanish on average for every
  `h ≠ 0`, the Parity-Drift Hypothesis fails for `π`.

Since the joint sums along `h(4, −2, −1, −1)` *are* the Weyl sums of `π`, no weaker joint statement
about the four series implies the conclusion: the reduction to the four series is sharp, and
separate normality of each `S_j` is not sufficient.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.BBPPi

open BinaryParityDrift

/-- `S_j = Σ_k 16^{−k}/(8k+j)`. -/
noncomputable def bbpS (j : ℕ) : ℝ := ∑' k : ℕ, (1 / 16 : ℝ) ^ k / (8 * k + j)

theorem summable_bbpS {j : ℕ} (hj : 1 ≤ j) :
    Summable fun k : ℕ => (1 / 16 : ℝ) ^ k / (8 * k + j) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_geometric_of_lt_one (r := (1 / 16 : ℝ)) (by norm_num) (by norm_num))
  have : (1 : ℝ) ≤ 8 * k + j := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact div_le_self (by positivity) this

/-- **The BBP formula as four series.**  `π = 4 S₁ − 2 S₄ − S₅ − S₆`. -/
theorem pi_eq_four_series : Real.pi = 4 * bbpS 1 - 2 * bbpS 4 - bbpS 5 - bbpS 6 := by
  have h1 := (summable_bbpS (j := 1) le_rfl).hasSum
  have h4 := (summable_bbpS (j := 4) (by norm_num)).hasSum
  have h5 := (summable_bbpS (j := 5) (by norm_num)).hasSum
  have h6 := (summable_bbpS (j := 6) (by norm_num)).hasSum
  have hcomb := (((h1.mul_left 4).sub (h4.mul_left 2)).sub h5).sub h6
  refine hasSum_bbp.unique (hcomb.congr_fun fun k => ?_)
  simp only [bbpTerm]
  push_cast
  ring

/-- **Phase factorisation.**  `e(h 16ⁿ π)` is the product of the phases of the four series at
`h (4, −2, −1, −1)`. -/
theorem exp_sixteen_pow_pi_eq_prod (h : ℤ) (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * h * (((16 : ℝ) ^ n * Real.pi : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (4 * h : ℤ) * (((16 : ℝ) ^ n * bbpS 1 : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (-2 * h : ℤ) * (((16 : ℝ) ^ n * bbpS 4 : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (-h : ℤ) * (((16 : ℝ) ^ n * bbpS 5 : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (-h : ℤ) * (((16 : ℝ) ^ n * bbpS 6 : ℝ) : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    show (16 : ℝ) ^ n * Real.pi = (16 : ℝ) ^ n * (4 * bbpS 1 - 2 * bbpS 4 - bbpS 5 - bbpS 6) by
      rw [← pi_eq_four_series]]
  congr 1
  push_cast
  ring

/-- **The joint reduction.**  If the joint Weyl sums of `(16ⁿS₁, 16ⁿS₄, 16ⁿS₅, 16ⁿS₆)` along
`h (4, −2, −1, −1)` vanish on average for every `h ≠ 0`, then the Parity-Drift Hypothesis fails for
`π`.  The joint sums are exactly the Weyl sums of `π`, so the reduction is sharp. -/
theorem not_parityDriftHypothesis_pi_of_jointWeylSums
    (hJ : ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      Complex.exp (2 * Real.pi * Complex.I * (4 * h : ℤ) * (((16 : ℝ) ^ n * bbpS 1 : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (-2 * h : ℤ) * (((16 : ℝ) ^ n * bbpS 4 : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (-h : ℤ) * (((16 : ℝ) ^ n * bbpS 5 : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (-h : ℤ) * (((16 : ℝ) ^ n * bbpS 6 : ℝ) : ℂ)))
      atTop (𝓝 0)) :
    ¬ ParityDriftHypothesis Real.pi := by
  have hW : ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      Complex.exp (2 * Real.pi * Complex.I * h * (((16 : ℝ) ^ n * Real.pi : ℝ) : ℂ))) atTop
      (𝓝 0) := fun h hh =>
    (hJ h hh).congr fun N => by simp_rw [exp_sixteen_pow_pi_eq_prod]
  refine not_parityDriftHypothesis_of_weylSums fun k hk => ?_
  exact tendsto_weylSum_four_of_sixteen (hW k hk) (hW (4 * k) (by omega))

end GaloisForLFunctions.HTGeometry.BBPPi
