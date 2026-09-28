import GaloisForLFunctions.RHTower.ZetaZeroDensitySeparatedSelection
import GaloisForLFunctions.RHTower.DirichletPowerDivisorMass
import GaloisForLFunctions.RHTower.DirichletPolynomialLargeValueCounts

/-!
# Powers of a detection class polynomial and their large-value counts

A class of `exists_separated_class_of_zeroHeightBox` is the Dirichlet polynomial

`P(t) = Σ_{k ∈ B_j} e_k (log k/Λ)^i k^{-σ'} k^{-it}`

on the `j`-th dyadic block `B_j ⊆ [2^j, 2^{j+1})` of the detection support.  Its coefficients are real
and bounded by `k^{-σ} d(k)` for every `σ ≤ σ'`, because `|e_k| ≤ d(k)` and the weight
`(log k/Λ)^i ∈ [0, 1]`.  Hence its `ℓ`-th power is a real Dirichlet polynomial supported in
`[2^{jℓ}, (2^{j+1}-1)^ℓ]` with mass at most `(2^{jℓ})^{-2σ} 2^{(j+1)ℓ}(1 + log 2^{(j+1)ℓ})^{2^{4ℓ}-1}`
(`sum_sq_powConv_le`).  This file applies the two large-value counts to that power.
-/

namespace RHTower

noncomputable section

open Complex Finset RHTower.Sieve

/-- The real coefficients of a class polynomial. -/
def classCoeff (N y : ℕ) (Λ : ℝ) (i : ℕ) (σ' : ℝ) : ℕ → ℝ :=
  fun k => detCoeff N y k * (Real.log k / Λ) ^ i * (k : ℝ) ^ (-σ')

theorem abscissaTaylorPoly_eq_dpoly (N y j : ℕ) (Λ : ℝ) (i : ℕ) (σ' t : ℝ) :
    abscissaTaylorPoly (detDyadicBlock N y j) (detCoeffC N y) Λ i σ' t
      = dpoly (classCoeff N y Λ i σ') (detDyadicBlock N y j) t := by
  unfold abscissaTaylorPoly dpoly
  refine sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (mem_detSupport_le (Finset.mem_filter.mp hk).1).1
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hcpow : (k : ℂ) ^ (-((σ' : ℂ) + (t : ℂ) * I))
      = (((k : ℝ) ^ (-σ') : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log k : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hk0,
      show Complex.log (k : ℂ) = (Real.log k : ℂ) by
        rw [← Complex.ofReal_natCast, Complex.ofReal_log hkR.le],
      Real.rpow_def_of_pos hkR, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [cterm, classCoeff, detCoeffC, hcpow]
  push_cast
  ring

theorem detCoeffW_zero_eq (N y : ℕ) : detCoeffW N y 0 = detCoeff N y := by
  funext k
  simp only [detCoeffW, detCoeff, neg_zero, Real.rpow_zero, mul_one]
  rfl

/-- `|e_k| ≤ d(k)` for every `k ≥ 1`. -/
theorem abs_detCoeff_le_divisors {N y k : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) (hk : 1 ≤ k) :
    |detCoeff N y k| ≤ (k.divisors.card : ℝ) := by
  by_cases hk1 : k = 1
  · subst hk1
    rw [detCoeff_eq_zero_of_le le_rfl hN hy]
    simp
  · have h := abs_detCoeffW_le (N := N) (y := y) 0 hk hk1
    rw [detCoeffW_zero_eq] at h
    simpa using h

/-- The class coefficients are bounded by `k^{-σ} d(k)` for `σ ≤ σ'`. -/
theorem abs_classCoeff_le {N y j i : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) {σ σ' : ℝ} (hσσ' : σ ≤ σ')
    {k : ℕ} (hk : k ∈ detDyadicBlock N y j) :
    |classCoeff N y (Real.log (N * y : ℕ)) i σ' k| ≤ (k : ℝ) ^ (-σ) * k.divisors.card := by
  have hks := mem_detSupport_le (Finset.mem_filter.mp hk).1
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hks.1
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hkR
  have hlogle : Real.log k ≤ Real.log (N * y : ℕ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hks.2)
  have hw : |(Real.log k / Real.log (N * y : ℕ)) ^ i| ≤ 1 := by
    rw [abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    rcases eq_or_lt_of_le (le_trans hlog0 hlogle) with h | h
    · rw [← h, div_zero, abs_zero]
      norm_num
    · rw [abs_div, abs_of_nonneg hlog0, abs_of_pos h, div_le_one h]
      exact hlogle
  have hpow : (k : ℝ) ^ (-σ') ≤ (k : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hkR (by linarith)
  unfold classCoeff
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hd := abs_detCoeff_le_divisors hN hy hks.1
  calc |detCoeff N y k| * |(Real.log k / Real.log (N * y : ℕ)) ^ i| * (k : ℝ) ^ (-σ')
      ≤ (k.divisors.card : ℝ) * 1 * (k : ℝ) ^ (-σ) := by
        gcongr
    _ = (k : ℝ) ^ (-σ) * k.divisors.card := by ring

theorem detDyadicBlock_bounds' {N y j k : ℕ} (hk : k ∈ detDyadicBlock N y j) :
    2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1 := by
  obtain ⟨h1, h2⟩ := mem_detDyadicBlock_bounds hk
  rw [pow_succ] at h2
  omega

/-- The norm of the `ℓ`-th power of a class polynomial is the norm of a real Dirichlet polynomial
with the convolution-power coefficients. -/
theorem norm_pow_class_eq {N y j i ℓ : ℕ} {Λ σ' t : ℝ} :
    ‖dpoly (classCoeff N y Λ i σ') (detDyadicBlock N y j) t‖ ^ ℓ
      = ‖dpoly (powConv (classCoeff N y Λ i σ') (detDyadicBlock N y j) ℓ)
          (powSupport (detDyadicBlock N y j) ℓ) t‖ := by
  rw [← norm_pow, dpoly_pow (classCoeff N y Λ i σ') (detDyadicBlock N y j)
    (fun k hk => (mem_detSupport_le (Finset.mem_filter.mp hk).1).1) t ℓ]

/-- The support of the `ℓ`-th power lies in `[2^{jℓ}, 2^{jℓ}·2^ℓ)`. -/
theorem powSupport_class_bounds {N y j ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∀ n ∈ powSupport (detDyadicBlock N y j) ℓ, (2 ^ j) ^ ℓ ≤ n ∧ n < (2 ^ j) ^ ℓ * 2 ^ ℓ := by
  intro n hn
  obtain ⟨h1, h2⟩ := mem_powSupport_bounds (fun _ hk => detDyadicBlock_bounds' hk) ℓ n hn
  refine ⟨h1, lt_of_le_of_lt h2 ?_⟩
  calc (2 * 2 ^ j - 1) ^ ℓ < (2 * 2 ^ j) ^ ℓ :=
        Nat.pow_lt_pow_left (by have := Nat.one_le_two_pow (n := j); omega) (by omega)
    _ = (2 ^ j) ^ ℓ * 2 ^ ℓ := by rw [mul_pow, mul_comm]

/-- **The mass of the `ℓ`-th power of a class polynomial.** -/
theorem sum_sq_powConv_class_le {N y j i ℓ : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) {σ σ' : ℝ}
    (hσ : 0 ≤ σ) (hσσ' : σ ≤ σ') :
    ∑ n ∈ powSupport (detDyadicBlock N y j) ℓ,
        (powConv (classCoeff N y (Real.log (N * y : ℕ)) i σ') (detDyadicBlock N y j) ℓ n) ^ 2
      ≤ (((2 ^ j : ℕ) : ℝ) ^ ℓ) ^ (-2 * σ) * (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)
          * (1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)) ^ (2 ^ (4 * ℓ) - 1) :=
  sum_sq_powConv_le hσ (Nat.one_le_two_pow) (fun _ hk => detDyadicBlock_bounds' hk)
    (fun _ hk => abs_classCoeff_le hN hy hσσ' hk)

end

end RHTower
