import GaloisForLFunctions.HTGeometry.ShellCarrierSeries

/-!
# The Poincaré coefficient polynomials of the mass carrier

Each factor of the carrier series is graded by the shell variable: the shell powers and the Poincaré
factor lose one unit of shell degree per unit of inverse order, so they contribute only at order
zero, while the exponential of the root defect keeps pace exactly.  Consequently the coefficient of
each inverse order is a polynomial in the squared shell variable of degree exactly that order, whose
extremal coefficient comes from the exponential alone.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section ShellGrading

theorem coeff_coeff_shellBinomSeries (α : ℝ) (m j d : ℕ) :
    ((shellBinomSeries α m).coeff j).coeff d
      = if j = 2 * d ∧ d < m then ((cbinomCoeff α d : ℝ) : ℂ) else 0 := by
  classical
  rw [shellBinomSeries, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  by_cases h : j = 2 * d ∧ d < m
  · obtain ⟨hj, hdm⟩ := h
    rw [if_pos ⟨hj, hdm⟩,
      Finset.sum_eq_single_of_mem d (Finset.mem_range.mpr hdm)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos hj, mul_one,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro k _ hkd
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero,
        Polynomial.coeff_zero]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hjk : j = 2 * k
    · rw [if_pos hjk, mul_one, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hdk : ¬ (d = k) := by
        rintro rfl
        exact h ⟨hjk, Finset.mem_range.mp hk⟩
      rw [if_neg hdk, mul_zero]
    · rw [if_neg hjk, mul_zero, Polynomial.coeff_zero]

theorem subDiag_two_shellBinomSeries (α : ℝ) (m : ℕ) : SubDiag 2 (shellBinomSeries α m) := by
  intro j d hjd
  rw [coeff_coeff_shellBinomSeries, if_neg]
  rintro ⟨hj, -⟩
  omega

theorem diagSym_shellBinomSeries (α : ℝ) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    diagSym (shellBinomSeries α m) j = if j = 0 then 1 else 0 := by
  rw [diagSym, coeff_coeff_shellBinomSeries]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [if_pos ⟨by omega, hm⟩, if_pos rfl, cbinomCoeff_zero]
    norm_num
  · rw [if_neg (by rintro ⟨h, -⟩; omega), if_neg (by omega)]

theorem subDiag_one_shellDefectSeries (m : ℕ) : SubDiag 1 (shellDefectSeries m) := by
  intro j d hjd
  rw [shellDefectSeries, Polynomial.coeff_divX, Polynomial.coeff_sub, Polynomial.coeff_one,
    if_neg (by omega), sub_zero]
  exact subDiag_two_shellBinomSeries _ _ (j + 1) d (by omega)

theorem cbinomCoeff_one (α : ℝ) : cbinomCoeff α 1 = α := by
  rw [cbinomCoeff, Finset.prod_range_one]
  norm_num

theorem diagSym_shellDefectSeries {m : ℕ} (hm : 0 < m) (j : ℕ) :
    diagSym (shellDefectSeries m) j = if j = 1 then (1 / 2 : ℂ) else 0 := by
  rw [diagSym, shellDefectSeries, Polynomial.coeff_divX, Polynomial.coeff_sub,
    Polynomial.coeff_one, if_neg (by omega), sub_zero, coeff_coeff_shellBinomSeries]
  rcases eq_or_ne j 1 with rfl | hj
  · rw [if_pos ⟨by omega, by omega⟩, if_pos rfl, cbinomCoeff_one]
    norm_num
  · rw [if_neg (by rintro ⟨h, -⟩; omega), if_neg hj]

end ShellGrading

section ExponentialFactor

/-- The scaled root-defect series. -/
theorem subDiag_one_scaledDefect (a : ℝ) (m : ℕ) :
    SubDiag 1 (Polynomial.C (Polynomial.C (-(a : ℂ))) * shellDefectSeries m) :=
  (subDiag_CC 1 _).mul (subDiag_one_shellDefectSeries m)

theorem diagSym_scaledDefect (a : ℝ) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    diagSym (Polynomial.C (Polynomial.C (-(a : ℂ))) * shellDefectSeries m) j
      = if j = 1 then -(a : ℂ) / 2 else 0 := by
  rw [diagSym_CC_mul (subDiag_one_shellDefectSeries m), diagSym_shellDefectSeries hm]
  split_ifs with h
  · ring
  · ring

theorem subDiag_one_defectExpSeries (a : ℝ) (m : ℕ) : SubDiag 1 (defectExpSeries a m) := by
  rw [defectExpSeries]
  exact SubDiag.sum _ fun j _ => (subDiag_CC 1 _).mul ((subDiag_one_scaledDefect a m).pow j)

/-- **The exponential factor carries the extremal shell degree at every order.** -/
theorem diagSym_defectExpSeries (a : ℝ) {m j : ℕ} (hm : 0 < m) (hj : j < m) :
    diagSym (defectExpSeries a m) j
      = ((Nat.factorial j : ℕ) : ℂ)⁻¹ * (-(a : ℂ) / 2) ^ j := by
  rw [defectExpSeries, diagSym_sum,
    Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)]
  · rw [diagSym_CC_mul ((subDiag_one_scaledDefect a m).pow j),
      diagSym_pow_of_linear (subDiag_one_scaledDefect a m) (diagSym_scaledDefect a hm) j j,
      if_pos rfl]
  · intro r _ hrj
    rw [diagSym_CC_mul ((subDiag_one_scaledDefect a m).pow r),
      diagSym_pow_of_linear (subDiag_one_scaledDefect a m) (diagSym_scaledDefect a hm) r j,
      if_neg (Ne.symm hrj), mul_zero]

end ExponentialFactor

section PoincareFactor

theorem subDiag_two_shellPoincareSeries (a : ℝ) (n m : ℕ) :
    SubDiag 2 (shellPoincareSeries a n m) := by
  rw [shellPoincareSeries]
  exact SubDiag.sum _ fun k _ =>
    ((subDiag_CC 2 _).mul (subDiag_X_pow 2 k)).mul (subDiag_two_shellBinomSeries _ m)

theorem diagSym_shellPoincareSeries_zero (a : ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    diagSym (shellPoincareSeries a n m) 0 = ((besselK1Coeff 0 : ℝ) : ℂ) := by
  rw [shellPoincareSeries, diagSym_sum,
    Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hn)]
  · rw [diagSym_mul_zero ((subDiag_CC 1 _).mul (subDiag_X_pow 1 0))
      ((subDiag_two_shellBinomSeries _ m).mono (by omega)),
      diagSym_CC_mul (subDiag_X_pow 1 0), diagSym_X_pow_zero, if_pos rfl,
      diagSym_shellBinomSeries _ hm, if_pos rfl]
    norm_num
  · intro k _ hk0
    rw [diagSym_mul_zero ((subDiag_CC 1 _).mul (subDiag_X_pow 1 k))
      ((subDiag_two_shellBinomSeries _ m).mono (by omega)),
      diagSym_CC_mul (subDiag_X_pow 1 k), diagSym_X_pow_zero, if_neg hk0, mul_zero, zero_mul]

end PoincareFactor

section Coefficients

theorem besselK1Coeff_zero : besselK1Coeff 0 = (Real.sqrt 2)⁻¹ := by
  rw [besselK1Coeff, schlafliCoeff, gaussianMomentFactor, binomCoeff]
  norm_num

theorem subDiag_one_carrierProductSeries (a : ℝ) (n m : ℕ) :
    SubDiag 1 (carrierProductSeries a n m) := by
  rw [carrierProductSeries]
  exact ((((subDiag_CC 1 _).mul ((subDiag_two_shellBinomSeries _ m).mono (by omega))).mul
      ((subDiag_two_shellBinomSeries _ m).mono (by omega))).mul
      (subDiag_one_defectExpSeries a m)).mul
      ((subDiag_two_shellPoincareSeries a n m).mono (by omega))

/-- **The extremal shell coefficient of the carrier series at every order.** -/
theorem diagSym_carrierProductSeries (a : ℝ) {n m j : ℕ} (hn : 0 < n) (hm : 0 < m) (hj : j < m) :
    diagSym (carrierProductSeries a n m) j
      = ((Nat.factorial j : ℕ) : ℂ)⁻¹ * (-(a : ℂ) / 2) ^ j := by
  have hA := (subDiag_two_shellBinomSeries (-1 / 2 : ℝ) m).mono (show 1 ≤ 2 by omega)
  have hG1 : SubDiag 1 (Polynomial.C (Polynomial.C ((Real.sqrt 2 : ℝ) : ℂ))
      * shellBinomSeries (-1 / 2) m) := (subDiag_CC 1 _).mul hA
  have hG2 : SubDiag 1 (Polynomial.C (Polynomial.C ((Real.sqrt 2 : ℝ) : ℂ))
      * shellBinomSeries (-1 / 2) m * shellBinomSeries (-1 / 4) m) :=
    hG1.mul ((subDiag_two_shellBinomSeries _ m).mono (by omega))
  have hG3 : SubDiag 1 (Polynomial.C (Polynomial.C ((Real.sqrt 2 : ℝ) : ℂ))
      * shellBinomSeries (-1 / 2) m * shellBinomSeries (-1 / 4) m * defectExpSeries a m) :=
    hG2.mul (subDiag_one_defectExpSeries a m)
  have hG1d : ∀ i, diagSym (Polynomial.C (Polynomial.C ((Real.sqrt 2 : ℝ) : ℂ))
      * shellBinomSeries (-1 / 2) m) i
      = if i = 0 then ((Real.sqrt 2 : ℝ) : ℂ) else 0 := by
    intro i
    rw [diagSym_CC_mul hA, diagSym_shellBinomSeries _ hm]
    split_ifs with h
    · ring
    · ring
  have hG2d : ∀ i, diagSym (Polynomial.C (Polynomial.C ((Real.sqrt 2 : ℝ) : ℂ))
      * shellBinomSeries (-1 / 2) m * shellBinomSeries (-1 / 4) m) i
      = if i = 0 then ((Real.sqrt 2 : ℝ) : ℂ) else 0 := by
    intro i
    rw [diagSym_mul_subDiag_two hG1 (subDiag_two_shellBinomSeries _ m),
      diagSym_shellBinomSeries _ hm, if_pos rfl, hG1d i]
    split_ifs with h
    · ring
    · ring
  have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) * ((besselK1Coeff 0 : ℝ) : ℂ) = 1 := by
    rw [besselK1Coeff_zero, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))), Complex.ofReal_one]
  rw [carrierProductSeries,
    diagSym_mul_subDiag_two hG3 (subDiag_two_shellPoincareSeries a n m),
    diagSym_shellPoincareSeries_zero a hn hm,
    diagSym_mul_of_left_delta hG2 (subDiag_one_defectExpSeries a m) hG2d,
    diagSym_defectExpSeries a hm hj]
  rw [mul_comm (((Real.sqrt 2 : ℝ) : ℂ)) _, mul_assoc, mul_assoc, hsqrt, mul_one]

/-- The Poincaré coefficient polynomial at inverse order `j`, in the squared shell variable. -/
def poincareCoeffPoly (a : ℝ) (n m j : ℕ) : Polynomial ℂ := (carrierProductSeries a n m).coeff j

/-- **Item 2, the degree bound.** -/
theorem natDegree_poincareCoeffPoly_le (a : ℝ) (n m j : ℕ) :
    (poincareCoeffPoly a n m j).natDegree ≤ j :=
  natDegree_coeff_le_of_subDiag (subDiag_one_carrierProductSeries a n m) j

/-- **Item 2, the extremal coefficient.** -/
theorem coeff_poincareCoeffPoly_self (a : ℝ) {n m j : ℕ} (hn : 0 < n) (hm : 0 < m) (hj : j < m) :
    (poincareCoeffPoly a n m j).coeff j
      = ((Nat.factorial j : ℕ) : ℂ)⁻¹ * (-(a : ℂ) / 2) ^ j :=
  diagSym_carrierProductSeries a hn hm hj

/-- **Item 2, the exact degree.** -/
theorem natDegree_poincareCoeffPoly (a : ℝ) {n m j : ℕ} (ha : a ≠ 0) (hn : 0 < n) (hm : 0 < m)
    (hj : j < m) : (poincareCoeffPoly a n m j).natDegree = j := by
  refine le_antisymm (natDegree_poincareCoeffPoly_le a n m j) ?_
  refine Polynomial.le_natDegree_of_ne_zero ?_
  rw [coeff_poincareCoeffPoly_self a hn hm hj]
  have hfac : ((Nat.factorial j : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hane : (-(a : ℂ) / 2) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, neg_eq_zero, Complex.ofReal_eq_zero]
    push Not
    exact ⟨ha, by norm_num⟩
  exact mul_ne_zero (inv_ne_zero hfac) (pow_ne_zero j hane)

/-- The assembled approximant realizes those coefficient polynomials at the squared shell
variable. -/
theorem coeff_carrierProductPoly (a x : ℝ) (n m j : ℕ) :
    (carrierProductPoly a x n m).coeff j
      = (poincareCoeffPoly a n m j).eval (((x : ℝ) : ℂ) ^ 2) := by
  rw [← shellEval_carrierProductSeries a n m x, coeff_shellEval, poincareCoeffPoly]

/-- **The mass carrier's deep-time expansion at every finite order, with classified
coefficients.**

The distortion of the carrier against its deep-time profile agrees, to order `m` in the reciprocal
spectral parameter, with a polynomial whose coefficient at inverse order `j` is a polynomial of
degree exactly `j` in the squared shell variable, with extremal coefficient `(-a/2)^j / j!`. -/
theorem carrier_poincare_expansion {a x : ℝ} (ha : 0 ≤ a) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2)
    (hdef : a * shellDefectRate x * r ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ j, (poincareCoeffPoly a n m j).natDegree ≤ j) ∧
      (∀ j < m, (poincareCoeffPoly a n m j).coeff j
        = ((Nat.factorial j : ℕ) : ℂ)⁻¹ * (-(a : ℂ) / 2) ^ j) ∧
      ∀ t : ℂ, 0 < t.re → 0 < t.im → Real.sqrt 2 * x ^ 2 < t.re * ‖t‖ → ‖t⁻¹‖ ≤ r →
        ‖carrierDistortion a t (_root_.HTGeometry.massBesselRoot t x) n
            - ∑ j ∈ Finset.range m, (poincareCoeffPoly a n m j).eval (((x : ℝ) : ℂ) ^ 2)
                * (t⁻¹) ^ j‖
          ≤ C * ‖t⁻¹‖ ^ m := by
  obtain ⟨C, hC, hbound⟩ := exists_poly_approx_carrierDistortion ha n m hr0 hr1 hxr hdef
  refine ⟨C, hC, natDegree_poincareCoeffPoly_le a n m,
    fun j hj => coeff_poincareCoeffPoly_self a hn hm hj, fun t htre htim hsm hw => ?_⟩
  have heval : (truncBelow m (carrierProductPoly a x n m)).eval t⁻¹
      = ∑ j ∈ Finset.range m, (poincareCoeffPoly a n m j).eval (((x : ℝ) : ℂ) ^ 2) * (t⁻¹) ^ j := by
    rw [eval_truncBelow]
    exact Finset.sum_congr rfl fun j _ => by rw [coeff_carrierProductPoly]
  rw [← heval]
  exact hbound t htre htim hsm hw

end Coefficients

end

end GaloisForLFunctions.HTGeometry
