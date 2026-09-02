import GaloisForLFunctions.HTGeometry.PoincareSeriesFourierExpansion

/-!
# The Fourier coefficients of the Poincaré series in Bessel form

With `J_ν(x) = Σ_j (-1)^j (x/2)^{2j+ν}/(j!(j+ν)!)`, the inner series of the coefficient identity
sums to a Bessel function:

  `Σ_j B(c, j) n^{k'+j} = 2π (-i)^{k'+1} (n/m)^{k'/2} c^{-1} J_{k'}(4π√(mn)/c)`,

so that, for weight `k = k' + 1 ≥ 3` and `m, n ≥ 1`,

  `a_{P_m}(n) = (1 + (-1)^k) [δ_{nm} + 2π (-i)^k (n/m)^{(k-1)/2} Σ_{c ≥ 1} S(m,n;c)/c · J_{k-1}(4π√(mn)/c)]`.
-/

open Complex RHTower.Sieve
open scoped Real MatrixGroups ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The Bessel function of integer order -/

/-- The Bessel function of the first kind of integer order `ν`, by its power series. -/
def besselJ (ν : ℕ) (x : ℝ) : ℝ :=
  ∑' j : ℕ, (-1) ^ j * (x / 2) ^ (2 * j + ν) / ((j.factorial : ℝ) * ((j + ν).factorial : ℝ))

theorem summable_besselJ_term (ν : ℕ) (x : ℝ) :
    Summable fun j : ℕ =>
      (-1 : ℝ) ^ j * (x / 2) ^ (2 * j + ν) / ((j.factorial : ℝ) * ((j + ν).factorial : ℝ)) := by
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial ((x / 2) ^ 2)).mul_left (|x / 2| ^ ν)) fun j => ?_
  have hf : (1 : ℝ) ≤ ((j + ν).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hj : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have hnum : |x / 2| ^ (2 * j + ν) = |x / 2| ^ ν * ((x / 2) ^ 2) ^ j := by
    rw [pow_add, pow_mul, sq_abs, mul_comm]
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < (j.factorial : ℝ) * ((j + ν).factorial : ℝ)), hnum,
    mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (by positivity) hj (le_mul_of_one_le_right hj.le hf))
    (by positivity)

/-- `J_ν(x) = (x/2)^ν Σ_j (-1)^j (x/2)^{2j}/(j!(j+ν)!)`. -/
theorem besselJ_eq_mul_tsum (ν : ℕ) (x : ℝ) :
    besselJ ν x = (x / 2) ^ ν *
      ∑' j : ℕ, (-1) ^ j * (x / 2) ^ (2 * j) / ((j.factorial : ℝ) * ((j + ν).factorial : ℝ)) := by
  rw [besselJ, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [pow_add]
  ring

/-! ## The inner series is a Bessel function -/

theorem neg_two_pi_I_sq : ((-2 * π * I) ^ 2 : ℂ) = -((2 * π) ^ 2) := by
  linear_combination (4 * (π : ℂ) ^ 2) * I_sq

/-- The termwise identity behind the Bessel form. -/
theorem expansionCoeff_mul_pow_eq (k' m : ℕ) (c : ℕ+) (n j : ℕ) :
    expansionCoeff k' m c j * (n : ℂ) ^ (k' + j)
      = (-2 * π * I) ^ (k' + 1) * ((c : ℂ) ^ (k' + 1))⁻¹ * (n : ℂ) ^ k' *
          (((-1 : ℝ) ^ j * ((2 * π / (c : ℝ)) ^ 2 * (m * n)) ^ j /
            ((j.factorial : ℝ) * ((j + k').factorial : ℝ)) : ℝ) : ℂ) := by
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast c.ne_zero
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hjk : ((j + k').factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hsq : ((-2 * π * I) ^ j : ℂ) * (-2 * π * I) ^ j = (-1) ^ j * ((2 * π) ^ 2) ^ j := by
    rw [← pow_add, ← two_mul, pow_mul, neg_two_pi_I_sq, neg_pow]
  unfold expansionCoeff
  rw [Nat.add_comm k' j]
  push_cast
  linear_combination ((m : ℂ) / c) ^ j / (j.factorial : ℂ) * ((c : ℂ) ^ (k' + 1 + j))⁻¹ *
    ((-2 * π * I) ^ (k' + 1) / ((j + k').factorial : ℂ)) * (n : ℂ) ^ (j + k') * hsq

theorem tsum_expansionCoeff_mul_pow (k' m : ℕ) (c : ℕ+) (n : ℕ) :
    ∑' j : ℕ, expansionCoeff k' m c j * (n : ℂ) ^ (k' + j)
      = (-2 * π * I) ^ (k' + 1) * ((c : ℂ) ^ (k' + 1))⁻¹ * (n : ℂ) ^ k' *
          ((∑' j : ℕ, (-1 : ℝ) ^ j * (2 * π * Real.sqrt (m * n) / c) ^ (2 * j) /
            ((j.factorial : ℝ) * ((j + k').factorial : ℝ)) : ℝ) : ℂ) := by
  simp_rw [expansionCoeff_mul_pow_eq]
  rw [tsum_mul_left, Complex.ofReal_tsum]
  congr 1
  refine tsum_congr fun j => ?_
  congr 3
  rw [pow_mul]
  simp only [mul_pow, div_pow]
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- **The Bessel form of the inner series**, `m, n ≥ 1`:
`Σ_j B(c,j) n^{k'+j} = 2π (-i)^{k'+1} √(n/m)^{k'} c^{-1} J_{k'}(4π√(mn)/c)`. -/
theorem tsum_expansionCoeff_mul_pow_eq_besselJ {k' m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (c : ℕ+) :
    ∑' j : ℕ, expansionCoeff k' m c j * (n : ℂ) ^ (k' + j)
      = 2 * π * (-I) ^ (k' + 1) * ((Real.sqrt (n / m)) ^ k' : ℝ) * ((c : ℂ))⁻¹ *
          (besselJ k' (4 * π * Real.sqrt (m * n) / c) : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (0 : ℝ) < c := by exact_mod_cast c.pos
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast c.ne_zero
  have hx : 4 * π * Real.sqrt (m * n) / (c : ℝ) / 2 = 2 * π * Real.sqrt (m * n) / c := by ring
  rw [tsum_expansionCoeff_mul_pow, besselJ_eq_mul_tsum, hx]
  set T : ℝ := ∑' j : ℕ, (-1 : ℝ) ^ j * (2 * π * Real.sqrt (m * n) / c) ^ (2 * j) /
    ((j.factorial : ℝ) * ((j + k').factorial : ℝ)) with hT
  have hts : Real.sqrt (n / m) * Real.sqrt (m * n) = n := by
    rw [← Real.sqrt_mul (by positivity), show (n : ℝ) / m * (m * n) = (n : ℝ) ^ 2 by
      field_simp, Real.sqrt_sq hn'.le]
  have hI : (-2 * π * I : ℂ) ^ (k' + 1) = (2 * π) ^ (k' + 1) * (-I) ^ (k' + 1) := by
    rw [← mul_pow]
    congr 1
    ring
  have hnk : (n : ℂ) ^ k' = ((Real.sqrt (n / m) : ℝ) : ℂ) ^ k' * ((Real.sqrt (m * n) : ℝ) : ℂ) ^ k' := by
    rw [← mul_pow, ← Complex.ofReal_mul, hts, Complex.ofReal_natCast]
  rw [hI, hnk]
  push_cast
  ring

/-! ## The coefficients in Bessel form -/

/-- **The Fourier coefficients of `P_m` in Bessel form**, weight `k' + 1 ≥ 3`, `m, n ≥ 1`. -/
theorem poincareCoeff_eq_bessel {k' m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    poincareCoeff k' m n
      = (1 + (-1 : ℂ) ^ (k' + 1)) * ((if n = m then 1 else 0) +
          2 * π * (-I) ^ (k' + 1) * ((Real.sqrt (n / m)) ^ k' : ℝ) *
            ∑' c : ℕ+, kloostermanSum c (m : ZMod c) (n : ZMod c) / (c : ℂ) *
              (besselJ k' (4 * π * Real.sqrt (m * n) / c) : ℝ)) := by
  unfold poincareCoeff
  congr 2
  rw [← tsum_mul_left]
  refine tsum_congr fun c => ?_
  rw [tsum_mul_right, tsum_expansionCoeff_mul_pow_eq_besselJ hm hn c]
  ring

/-- **The Fourier coefficients of the Poincaré cusp form in Bessel form.** -/
theorem cuspCoeff_poincareSeriesCF_eq_bessel {k' : ℕ} (hk' : 2 ≤ k') {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) :
    cuspCoeff n (poincareSeriesCF (k := ((k' + 1 : ℕ) : ℤ)) (by omega) hm)
      = (1 + (-1 : ℂ) ^ (k' + 1)) * ((if n = m then 1 else 0) +
          2 * π * (-I) ^ (k' + 1) * ((Real.sqrt (n / m)) ^ k' : ℝ) *
            ∑' c : ℕ+, kloostermanSum c (m : ZMod c) (n : ZMod c) / (c : ℂ) *
              (besselJ k' (4 * π * Real.sqrt (m * n) / c) : ℝ)) := by
  rw [cuspCoeff_poincareSeriesCF_eq_poincareCoeff hk' hm n, poincareCoeff_eq_bessel hm hn]

/-! ## The Petersson formula for level one -/

/-- **The Petersson formula for `SL(2,ℤ)`**: for an orthonormal basis `b` of the cusp forms of
weight `k = k' + 1 ≥ 3` and `m, n ≥ 1`,
`2 (4πm)^{1-k} Γ(k-1) Σ_i conj(a_{b_i}(m)) a_{b_i}(n)
   = (1 + (-1)^k)[δ_{nm} + 2π(-i)^k (n/m)^{(k-1)/2} Σ_c S(m,n;c)/c · J_{k-1}(4π√(mn)/c)]`. -/
theorem petersson_formula_levelOne {k' : ℕ} (hk' : 2 ≤ k') {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (PeterssonSpace ((k' + 1 : ℕ) : ℤ))) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) :
    peterssonConstant ((k' + 1 : ℕ) : ℤ) m *
        ∑ i, conj (cuspCoeff m (b i).toCuspForm) * cuspCoeff n (b i).toCuspForm
      = (1 + (-1 : ℂ) ^ (k' + 1)) * ((if n = m then 1 else 0) +
          2 * π * (-I) ^ (k' + 1) * ((Real.sqrt (n / m)) ^ k' : ℝ) *
            ∑' c : ℕ+, kloostermanSum c (m : ZMod c) (n : ZMod c) / (c : ℂ) *
              (besselJ k' (4 * π * Real.sqrt (m * n) / c) : ℝ)) := by
  rw [← cuspCoeff_poincareSeriesCF_eq_sum b (by omega) hm n,
    cuspCoeff_poincareSeriesCF_eq_bessel hk' hm hn]

end

end GaloisForLFunctions.HTGeometry
