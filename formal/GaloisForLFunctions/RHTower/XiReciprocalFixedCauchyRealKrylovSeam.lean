import GaloisForLFunctions.RHTower.XiReciprocalFixedCauchyRealKrylovRecovery

/-!
# Real reciprocal-Krylov seam law

Real reciprocal polynomials impose an exact two-point conjugation law across critical-line
reflection. The law survives Hilbert-norm limits. On fixed adjoint response its residual is exactly
`4 * Im(a) * Im(z)` times nonzero reciprocal factors. Therefore saturation at one nonreal regular
pole forces every centered Xi spectral coordinate to be real and is equivalent to RH.

This localizes real-response recovery obstruction without a quadratic-form estimate or a global
positivity assumption.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Two-point conjugation seam forced by real reciprocal-polynomial coefficients. -/
def xiReciprocalCauchyRealKrylovSeam
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy)
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) : ℂ :=
  ((starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ)) *
      v (xiZeroCopyLineConjEquiv q) -
    ((starRingEnd ℂ) (xiSpectralPoint q) -
        (starRingEnd ℂ) (z : ℂ)) * (starRingEnd ℂ) (v q)

/-- Every finite real reciprocal-Krylov vector satisfies the seam exactly. -/
theorem xiReciprocalCauchyRealKrylovSeam_polynomial_eq_zero
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) (p : Polynomial ℝ) :
    xiReciprocalCauchyRealKrylovSeam z q
        (xiReciprocalCauchyKrylovPolynomialVector z
          (xiRealPolynomialToComplex p)) = 0 := by
  have haz : xiSpectralPoint q ≠ (z : ℂ) := by
    intro h
    apply z.1.property
    rw [← h]
    exact XiC_xiSpectralPoint_eq_zero q
  have hconjz : (starRingEnd ℂ) (xiSpectralPoint q) ≠ (z : ℂ) := by
    intro h
    apply z.1.property
    rw [← h, ← xiSpectralPoint_lineConj]
    exact XiC_xiSpectralPoint_eq_zero (xiZeroCopyLineConjEquiv q)
  have hconjconjz :
      (starRingEnd ℂ) (xiSpectralPoint q) ≠
        (starRingEnd ℂ) (z : ℂ) := by
    intro h
    apply haz
    have hc := congrArg (starRingEnd ℂ) h
    simpa using hc
  rw [xiReciprocalCauchyRealKrylovSeam,
    xiReciprocalCauchyKrylovPolynomialVector_apply,
    xiReciprocalCauchyKrylovPolynomialVector_apply,
    xiSpectralPoint_lineConj]
  simp only [xiWeilContinuedCauchyLp, xiWeilCauchyLp_apply,
    xiWeilCauchyTest, xiRealPolynomialToComplex]
  rw [← evalRealPolynomial, ← evalRealPolynomial]
  simp only [xiSpectralPoint_lineConj, map_mul, map_inv₀, map_sub]
  rw [← evalRealPolynomial_conj]
  simp only [map_inv₀]
  have hleft := mul_inv_cancel₀ (sub_ne_zero.mpr hconjz)
  have hright := mul_inv_cancel₀ (sub_ne_zero.mpr hconjconjz)
  calc
    _ = evalRealPolynomial p ((starRingEnd ℂ) (xiSpectralPoint q))⁻¹ *
          (((starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ)) *
            ((starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ))⁻¹) -
        evalRealPolynomial p ((starRingEnd ℂ) (xiSpectralPoint q))⁻¹ *
          (((starRingEnd ℂ) (xiSpectralPoint q) -
              (starRingEnd ℂ) (z : ℂ)) *
            ((starRingEnd ℂ) (xiSpectralPoint q) -
              (starRingEnd ℂ) (z : ℂ))⁻¹) := by ring
    _ = 0 := by rw [hleft, hright]; ring

private theorem tendsto_lp_apply
    {V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2}
    {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hV : Tendsto V atTop (nhds v)) (q : XiZeroCopy) :
    Tendsto (fun n => V n q) atTop (nhds (v q)) := by
  have hinner : Tendsto
      (fun n => inner ℂ (HilbertSchmidt.lpBasis XiZeroCopy q) (V n))
      atTop
      (nhds (inner ℂ (HilbertSchmidt.lpBasis XiZeroCopy q) v)) :=
    tendsto_const_nhds.inner hV
  simpa only [HilbertSchmidt.lpBasis_apply, lp.inner_single_left,
    RCLike.inner_apply, map_one, one_mul, mul_one] using hinner

/-- Hilbert-norm limits of real reciprocal-Krylov vectors retain every local seam equation. -/
theorem xiReciprocalCauchyRealKrylovSeam_eq_zero_of_tendsto
    (z : XiContinuedCauchyPoint) (p : ℕ → Polynomial ℝ)
    (v : lp (fun _ : XiZeroCopy => ℂ) 2)
    (hp : Tendsto (fun n => xiReciprocalCauchyKrylovPolynomialVector z
        (xiRealPolynomialToComplex (p n))) atTop (nhds v))
    (q : XiZeroCopy) :
    xiReciprocalCauchyRealKrylovSeam z q v = 0 := by
  let V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2 := fun n =>
    xiReciprocalCauchyKrylovPolynomialVector z
      (xiRealPolynomialToComplex (p n))
  have hV : Tendsto V atTop (nhds v) := hp
  have hq := tendsto_lp_apply hV q
  have hqJ := tendsto_lp_apply hV (xiZeroCopyLineConjEquiv q)
  have hseam : Tendsto (fun n => xiReciprocalCauchyRealKrylovSeam z q (V n))
      atTop (nhds (xiReciprocalCauchyRealKrylovSeam z q v)) := by
    unfold xiReciprocalCauchyRealKrylovSeam
    exact (tendsto_const_nhds.mul hqJ).sub
      (tendsto_const_nhds.mul
        (RCLike.continuous_conj.continuousAt.tendsto.comp hq))
  have hzero : Tendsto
      (fun n => xiReciprocalCauchyRealKrylovSeam z q (V n))
      atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun n =>
      (xiReciprocalCauchyRealKrylovSeam_polynomial_eq_zero z q (p n)).symm
  exact tendsto_nhds_unique hseam hzero

/-! ## Constructive seam-fixed closure -/

/-- Conjugate every coefficient of a complex polynomial. -/
def xiPolynomialConjugateCoefficients (p : Polynomial ℂ) : Polynomial ℂ :=
  p.map (starRingEnd ℂ)

/-- Real polynomial obtained by taking the real part of every complex coefficient. -/
def xiPolynomialCoefficientRealPart (p : Polynomial ℂ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (p.natDegree + 1), Polynomial.monomial j (p.coeff j).re

@[simp] theorem xiPolynomialCoefficientRealPart_coeff (p : Polynomial ℂ) (k : ℕ) :
    (xiPolynomialCoefficientRealPart p).coeff k = (p.coeff k).re := by
  rw [xiPolynomialCoefficientRealPart, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (p.natDegree + 1)) k
    fun j => (p.coeff j).re]
  by_cases hk : k ∈ Finset.range (p.natDegree + 1)
  · rw [if_pos hk]
  · rw [if_neg hk]
    rw [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k),
      Complex.zero_re]

/-- Complexification of coefficientwise real part is the average with coefficient conjugation. -/
theorem xiRealPolynomialToComplex_coefficientRealPart (p : Polynomial ℂ) :
    xiRealPolynomialToComplex (xiPolynomialCoefficientRealPart p) =
      Polynomial.C (1 / 2 : ℂ) * (p + xiPolynomialConjugateCoefficients p) := by
  ext k
  rw [xiRealPolynomialToComplex, Polynomial.coeff_map,
    xiPolynomialCoefficientRealPart_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_add, xiPolynomialConjugateCoefficients,
    Polynomial.coeff_map]
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp [Complex.mul_im]

/-- Coefficientwise real-part symmetrization averages the two complex Krylov vectors. -/
theorem xiReciprocalCauchyKrylovPolynomialVector_coefficientRealPart
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) :
    xiReciprocalCauchyKrylovPolynomialVector z
        (xiRealPolynomialToComplex (xiPolynomialCoefficientRealPart p)) =
      (1 / 2 : ℂ) •
        (xiReciprocalCauchyKrylovPolynomialVector z p +
          xiReciprocalCauchyKrylovPolynomialVector z
            (xiPolynomialConjugateCoefficients p)) := by
  rw [xiRealPolynomialToComplex_coefficientRealPart,
    xiReciprocalCauchyKrylovPolynomialVector_C_mul,
    xiReciprocalCauchyKrylovPolynomialVector_add]

/-- Ratio transporting coefficient conjugation across the critical-line reflection seam. -/
def xiReciprocalCauchyRealKrylovMultiplier
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) : ℂ :=
  ((starRingEnd ℂ) (xiSpectralPoint q) - (starRingEnd ℂ) (z : ℂ)) *
    ((starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ))⁻¹

/-- Coefficient conjugation becomes conjugation of the vector, twisted by the seam multiplier. -/
theorem xiReciprocalCauchyKrylovPolynomialVector_conjugateCoefficients_lineConj
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ) (q : XiZeroCopy) :
    xiReciprocalCauchyKrylovPolynomialVector z
        (xiPolynomialConjugateCoefficients p) (xiZeroCopyLineConjEquiv q) =
      xiReciprocalCauchyRealKrylovMultiplier z q *
        (starRingEnd ℂ) (xiReciprocalCauchyKrylovPolynomialVector z p q) := by
  have hden : (starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ) ≠ 0 := by
    simpa only [xiSpectralPoint_lineConj] using
      xiSpectralPoint_sub_continuedCauchyPoint_ne z
        (xiZeroCopyLineConjEquiv q)
  have hconjDen :
      (starRingEnd ℂ) (xiSpectralPoint q) - (starRingEnd ℂ) (z : ℂ) ≠ 0 := by
    rw [← map_sub]
    exact (map_ne_zero (starRingEnd ℂ)).2
      (xiSpectralPoint_sub_continuedCauchyPoint_ne z q)
  rw [xiReciprocalCauchyKrylovPolynomialVector_apply,
    xiReciprocalCauchyKrylovPolynomialVector_apply,
    xiSpectralPoint_lineConj]
  simp only [xiPolynomialConjugateCoefficients,
    xiWeilContinuedCauchyLp, xiWeilCauchyLp_apply, xiWeilCauchyTest,
    xiReciprocalCauchyRealKrylovMultiplier, xiSpectralPoint_lineConj,
    map_mul, map_inv₀, map_sub]
  rw [show ((starRingEnd ℂ) (xiSpectralPoint q))⁻¹ =
      (starRingEnd ℂ) ((xiSpectralPoint q)⁻¹) by rw [map_inv₀],
    Polynomial.eval_map_apply]
  field_simp [hden, hconjDen]

/-- Seam multiplier is identity plus a fixed Cauchy-kernel multiple. -/
theorem xiReciprocalCauchyRealKrylovMultiplier_eq_one_add
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    xiReciprocalCauchyRealKrylovMultiplier z q =
      1 + ((z : ℂ) - (starRingEnd ℂ) (z : ℂ)) *
        ((starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ))⁻¹ := by
  have hden : (starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ) ≠ 0 := by
    simpa only [xiSpectralPoint_lineConj] using
      xiSpectralPoint_sub_continuedCauchyPoint_ne z
        (xiZeroCopyLineConjEquiv q)
  rw [xiReciprocalCauchyRealKrylovMultiplier]
  field_simp [hden]
  ring

/-- Seam multiplier has a uniform bound supplied by the fixed Cauchy vector. -/
theorem norm_xiReciprocalCauchyRealKrylovMultiplier_le
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    ‖xiReciprocalCauchyRealKrylovMultiplier z q‖ ≤
      1 + ‖(z : ℂ) - (starRingEnd ℂ) (z : ℂ)‖ *
        ‖xiWeilContinuedCauchyLp z‖ := by
  rw [xiReciprocalCauchyRealKrylovMultiplier_eq_one_add]
  calc
    _ ≤ ‖(1 : ℂ)‖ +
        ‖((z : ℂ) - (starRingEnd ℂ) (z : ℂ)) *
          ((starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ))⁻¹‖ :=
      norm_add_le _ _
    _ = 1 + ‖(z : ℂ) - (starRingEnd ℂ) (z : ℂ)‖ *
        ‖((starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ))⁻¹‖ := by
      rw [norm_one, norm_mul]
    _ ≤ _ := by
      gcongr
      simpa only [xiWeilContinuedCauchyLp, xiWeilCauchyLp_apply,
        xiWeilCauchyTest, xiSpectralPoint_lineConj] using
          (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
            (xiWeilContinuedCauchyLp z) (xiZeroCopyLineConjEquiv q))

/-- A seam-fixed vector transforms by the same multiplier as coefficient-conjugated Krylov
vectors. -/
theorem lp_lineConj_eq_realKrylovMultiplier_conj_of_seam
    (z : XiContinuedCauchyPoint)
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) (q : XiZeroCopy)
    (hseam : xiReciprocalCauchyRealKrylovSeam z q v = 0) :
    v (xiZeroCopyLineConjEquiv q) =
      xiReciprocalCauchyRealKrylovMultiplier z q * (starRingEnd ℂ) (v q) := by
  have hden : (starRingEnd ℂ) (xiSpectralPoint q) - (z : ℂ) ≠ 0 := by
    simpa only [xiSpectralPoint_lineConj] using
      xiSpectralPoint_sub_continuedCauchyPoint_ne z
        (xiZeroCopyLineConjEquiv q)
  apply mul_left_cancel₀ hden
  calc
    _ = ((starRingEnd ℂ) (xiSpectralPoint q) -
          (starRingEnd ℂ) (z : ℂ)) * (starRingEnd ℂ) (v q) :=
      sub_eq_zero.mp (by
        simpa only [xiReciprocalCauchyRealKrylovSeam] using hseam)
    _ = _ := by
      rw [xiReciprocalCauchyRealKrylovMultiplier]
      field_simp [hden]

/-- Coefficient conjugation is bounded on approximation errors about any seam-fixed vector. -/
theorem norm_conjugateCoefficientKrylov_sub_le_of_seam
    (z : XiContinuedCauchyPoint) (p : Polynomial ℂ)
    (v : lp (fun _ : XiZeroCopy => ℂ) 2)
    (hseam : ∀ q, xiReciprocalCauchyRealKrylovSeam z q v = 0) :
    ‖xiReciprocalCauchyKrylovPolynomialVector z
        (xiPolynomialConjugateCoefficients p) - v‖ ≤
      (1 + ‖(z : ℂ) - (starRingEnd ℂ) (z : ℂ)‖ *
          ‖xiWeilContinuedCauchyLp z‖) *
        ‖xiReciprocalCauchyKrylovPolynomialVector z p - v‖ := by
  let Vsharp := xiReciprocalCauchyKrylovPolynomialVector z
    (xiPolynomialConjugateCoefficients p) - v
  let V := xiReciprocalCauchyKrylovPolynomialVector z p - v
  let M := 1 + ‖(z : ℂ) - (starRingEnd ℂ) (z : ℂ)‖ *
    ‖xiWeilContinuedCauchyLp z‖
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hcoord (q : XiZeroCopy) :
      Vsharp (xiZeroCopyLineConjEquiv q) =
        xiReciprocalCauchyRealKrylovMultiplier z q *
          (starRingEnd ℂ) (V q) := by
    dsimp only [Vsharp, V]
    change xiReciprocalCauchyKrylovPolynomialVector z
          (xiPolynomialConjugateCoefficients p) (xiZeroCopyLineConjEquiv q) -
        v (xiZeroCopyLineConjEquiv q) =
      xiReciprocalCauchyRealKrylovMultiplier z q *
        (starRingEnd ℂ)
          (xiReciprocalCauchyKrylovPolynomialVector z p q - v q)
    rw [xiReciprocalCauchyKrylovPolynomialVector_conjugateCoefficients_lineConj,
      lp_lineConj_eq_realKrylovMultiplier_conj_of_seam z v q (hseam q),
      map_sub]
    ring
  have hpoint (q : XiZeroCopy) :
      ‖Vsharp (xiZeroCopyLineConjEquiv q)‖ ^ 2 ≤
        M ^ 2 * ‖V q‖ ^ 2 := by
    rw [hcoord, norm_mul, Complex.norm_conj]
    have hmult := norm_xiReciprocalCauchyRealKrylovMultiplier_le z q
    change ‖xiReciprocalCauchyRealKrylovMultiplier z q‖ ≤ M at hmult
    have hprod := mul_le_mul_of_nonneg_right hmult (norm_nonneg (V q))
    have hleft : 0 ≤
        ‖xiReciprocalCauchyRealKrylovMultiplier z q‖ * ‖V q‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hright : 0 ≤ M * ‖V q‖ := mul_nonneg hM (norm_nonneg _)
    nlinarith
  have hsumRight : Summable (fun q : XiZeroCopy => M ^ 2 * ‖V q‖ ^ 2) :=
    (HilbertSchmidt.summable_coe_sq V).mul_left (M ^ 2)
  have hsumLeft : Summable (fun q : XiZeroCopy =>
      ‖Vsharp (xiZeroCopyLineConjEquiv q)‖ ^ 2) :=
    xiZeroCopyLineConjEquiv.summable_iff.mpr
      (HilbertSchmidt.summable_coe_sq Vsharp)
  have hsq : ‖Vsharp‖ ^ 2 ≤ (M * ‖V‖) ^ 2 := by
    calc
      ‖Vsharp‖ ^ 2 = ∑' q, ‖Vsharp (xiZeroCopyLineConjEquiv q)‖ ^ 2 := by
        rw [HilbertSchmidt.lp_norm_sq_eq]
        exact (xiZeroCopyLineConjEquiv.tsum_eq
          (fun q => ‖Vsharp q‖ ^ 2)).symm
      _ ≤ ∑' q, M ^ 2 * ‖V q‖ ^ 2 :=
        hsumLeft.tsum_le_tsum hpoint hsumRight
      _ = M ^ 2 * ∑' q, ‖V q‖ ^ 2 := by
        rw [tsum_mul_left]
      _ = (M * ‖V‖) ^ 2 := by
        rw [← HilbertSchmidt.lp_norm_sq_eq]
        ring
  change ‖Vsharp‖ ≤ M * ‖V‖
  nlinarith [norm_nonneg Vsharp, norm_nonneg V, mul_nonneg hM (norm_nonneg V)]

/-- Any complex reciprocal-Krylov approximation of a seam-fixed vector can be symmetrized,
coefficient by coefficient, into a real reciprocal-Krylov approximation of the same vector. -/
theorem exists_real_reciprocalCauchyKrylovPolynomials_tendsto_of_complex_tendsto_of_seam
    (z : XiContinuedCauchyPoint)
    (v : lp (fun _ : XiZeroCopy => ℂ) 2)
    (p : ℕ → Polynomial ℂ)
    (hp : Tendsto (fun n => xiReciprocalCauchyKrylovPolynomialVector z (p n))
      atTop (nhds v))
    (hseam : ∀ q, xiReciprocalCauchyRealKrylovSeam z q v = 0) :
    ∃ r : ℕ → Polynomial ℝ,
      Tendsto (fun n => xiReciprocalCauchyKrylovPolynomialVector z
        (xiRealPolynomialToComplex (r n))) atTop (nhds v) := by
  let P : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2 := fun n =>
    xiReciprocalCauchyKrylovPolynomialVector z (p n)
  let Psharp : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2 := fun n =>
    xiReciprocalCauchyKrylovPolynomialVector z
      (xiPolynomialConjugateCoefficients (p n))
  let M := 1 + ‖(z : ℂ) - (starRingEnd ℂ) (z : ℂ)‖ *
    ‖xiWeilContinuedCauchyLp z‖
  have hP : Tendsto P atTop (nhds v) := hp
  have hPnorm : Tendsto (fun n => ‖P n - v‖) atTop (nhds 0) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mp hP
  have hsharpNorm : Tendsto (fun n => ‖Psharp n - v‖) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n => norm_nonneg _
    · exact Eventually.of_forall fun n => by
        exact norm_conjugateCoefficientKrylov_sub_le_of_seam
          z (p n) v hseam
    · simpa only [mul_zero] using hPnorm.const_mul M
  have hPsharp : Tendsto Psharp atTop (nhds v) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hsharpNorm
  have havg : Tendsto (fun n => (1 / 2 : ℂ) • (P n + Psharp n))
      atTop (nhds v) := by
    have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℂ)) atTop (nhds (1 / 2 : ℂ)) :=
      tendsto_const_nhds
    have h := hc.smul (hP.add hPsharp)
    have hvavg : (1 / 2 : ℂ) • (v + v) = v := by
      rw [smul_add, ← add_smul]
      norm_num
    simpa only [hvavg] using h
  refine ⟨fun n => xiPolynomialCoefficientRealPart (p n), ?_⟩
  simpa only [P, Psharp,
    xiReciprocalCauchyKrylovPolynomialVector_coefficientRealPart] using havg

private theorem reciprocalCauchyRealKrylovSeam_algebra
    (a z : ℂ) (haz : a ≠ z)
    (haconjz : a ≠ (starRingEnd ℂ) z) :
    ((starRingEnd ℂ) a - z) * (a⁻¹ ^ 2 * (a - z)⁻¹) -
        ((starRingEnd ℂ) a - (starRingEnd ℂ) z) *
          (a⁻¹ ^ 2 * (a - (starRingEnd ℂ) z)⁻¹) =
      4 * a.im * z.im * a⁻¹ ^ 2 * (a - z)⁻¹ *
        (a - (starRingEnd ℂ) z)⁻¹ := by
  have hnum :
      ((starRingEnd ℂ) a - z) * (a - (starRingEnd ℂ) z) -
          ((starRingEnd ℂ) a - (starRingEnd ℂ) z) * (a - z) =
        4 * a.im * z.im := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring
  calc
    _ = a⁻¹ ^ 2 *
        ((((starRingEnd ℂ) a - z) * (a - (starRingEnd ℂ) z) -
            ((starRingEnd ℂ) a - (starRingEnd ℂ) z) * (a - z)) *
          ((a - z) * (a - (starRingEnd ℂ) z))⁻¹) := by
      rw [mul_inv_rev]
      have hd : (a - z) * (a - z)⁻¹ = 1 :=
        mul_inv_cancel₀ (sub_ne_zero.mpr haz)
      have he : (a - (starRingEnd ℂ) z) *
          (a - (starRingEnd ℂ) z)⁻¹ = 1 :=
        mul_inv_cancel₀ (sub_ne_zero.mpr haconjz)
      calc
        _ = a⁻¹ ^ 2 *
            (((starRingEnd ℂ) a - z) * (a - z)⁻¹ -
              ((starRingEnd ℂ) a - (starRingEnd ℂ) z) *
                (a - (starRingEnd ℂ) z)⁻¹) := by ring
        _ = a⁻¹ ^ 2 *
            (((starRingEnd ℂ) a - z) *
                ((a - (starRingEnd ℂ) z) *
                  (a - (starRingEnd ℂ) z)⁻¹) * (a - z)⁻¹ -
              ((starRingEnd ℂ) a - (starRingEnd ℂ) z) *
                ((a - z) * (a - z)⁻¹) *
                  (a - (starRingEnd ℂ) z)⁻¹) := by rw [hd, he]; ring
        _ = _ := by ring
    _ = _ := by
      rw [hnum]
      rw [mul_inv_rev]
      ring

/-- Exact residual of fixed adjoint response against real reciprocal-Krylov seam. -/
theorem xiReciprocalCauchyRealKrylovSeam_adjointResponse_eq
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    xiReciprocalCauchyRealKrylovSeam z q
        (xiWeilEvaluationLp
          (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
          (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)) =
      4 * (xiSpectralPoint q).im * (z : ℂ).im *
        (xiSpectralPoint q)⁻¹ ^ 2 *
        (xiSpectralPoint q - (z : ℂ))⁻¹ *
        (xiSpectralPoint q - (starRingEnd ℂ) (z : ℂ))⁻¹ := by
  let a := xiSpectralPoint q
  have haz : a ≠ (z : ℂ) := by
    intro h
    apply z.1.property
    rw [← h]
    exact XiC_xiSpectralPoint_eq_zero q
  have hzconj : XiC ((starRingEnd ℂ) (z : ℂ)) ≠ 0 := by
    intro h
    rw [XiC_conj] at h
    have hc := congrArg (starRingEnd ℂ) h
    apply z.1.property
    simpa using hc
  have haconjz : a ≠ (starRingEnd ℂ) (z : ℂ) := by
    intro h
    apply hzconj
    rw [← h]
    exact XiC_xiSpectralPoint_eq_zero q
  rw [xiReciprocalCauchyRealKrylovSeam,
    xiWeilEvaluationLp_apply, xiWeilEvaluationLp_apply,
    xiReciprocalSquareCauchyAdjointResponseTest,
    xiSpectralPoint_lineConj]
  simp only [xiReciprocalSquareCauchyAdjointResponseTest,
    map_mul, map_inv₀, map_pow, map_sub, Complex.conj_conj]
  dsimp only [a] at haz haconjz ⊢
  exact reciprocalCauchyRealKrylovSeam_algebra
    (xiSpectralPoint q) (z : ℂ) haz haconjz

/-- At any nonreal regular pole, zero adjoint-response seam forces one spectral point real. -/
theorem xiSpectralPoint_im_eq_zero_of_adjointResponse_realKrylovSeam_eq_zero
    (z : XiContinuedCauchyPoint) (hzim : (z : ℂ).im ≠ 0)
    (q : XiZeroCopy)
    (hseam : xiReciprocalCauchyRealKrylovSeam z q
        (xiWeilEvaluationLp
          (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
          (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)) = 0) :
    (xiSpectralPoint q).im = 0 := by
  let a := xiSpectralPoint q
  have haz : a ≠ (z : ℂ) := by
    intro h
    apply z.1.property
    rw [← h]
    exact XiC_xiSpectralPoint_eq_zero q
  have hzconj : XiC ((starRingEnd ℂ) (z : ℂ)) ≠ 0 := by
    intro h
    rw [XiC_conj] at h
    have hc := congrArg (starRingEnd ℂ) h
    apply z.1.property
    simpa using hc
  have haconjz : a ≠ (starRingEnd ℂ) (z : ℂ) := by
    intro h
    apply hzconj
    rw [← h]
    exact XiC_xiSpectralPoint_eq_zero q
  have hres := xiReciprocalCauchyRealKrylovSeam_adjointResponse_eq z q
  rw [hseam] at hres
  have hzero :
      4 * (xiSpectralPoint q).im * (z : ℂ).im *
          (xiSpectralPoint q)⁻¹ ^ 2 *
          (xiSpectralPoint q - (z : ℂ))⁻¹ *
          (xiSpectralPoint q - (starRingEnd ℂ) (z : ℂ))⁻¹ = 0 :=
    hres.symm
  have hrest :
      (4 : ℂ) * (z : ℂ).im * (xiSpectralPoint q)⁻¹ ^ 2 *
          (xiSpectralPoint q - (z : ℂ))⁻¹ *
          (xiSpectralPoint q - (starRingEnd ℂ) (z : ℂ))⁻¹ ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · norm_num
          · exact_mod_cast hzim
        · exact pow_ne_zero 2 (inv_ne_zero (xiSpectralPoint_ne_zero q))
      · exact inv_ne_zero (sub_ne_zero.mpr (by simpa only [a] using haz))
    · exact inv_ne_zero (sub_ne_zero.mpr (by simpa only [a] using haconjz))
  have himul : ((xiSpectralPoint q).im : ℂ) *
      ((4 : ℂ) * (z : ℂ).im * (xiSpectralPoint q)⁻¹ ^ 2 *
        (xiSpectralPoint q - (z : ℂ))⁻¹ *
        (xiSpectralPoint q - (starRingEnd ℂ) (z : ℂ))⁻¹) = 0 := by
    calc
      _ = 4 * (xiSpectralPoint q).im * (z : ℂ).im *
          (xiSpectralPoint q)⁻¹ ^ 2 *
          (xiSpectralPoint q - (z : ℂ))⁻¹ *
          (xiSpectralPoint q - (starRingEnd ℂ) (z : ℂ))⁻¹ := by ring
      _ = 0 := hzero
  have himComplex : ((xiSpectralPoint q).im : ℂ) = 0 :=
    (mul_eq_zero.mp himul).resolve_right hrest
  exact_mod_cast himComplex

/-- Exact local seam condition on fixed adjoint response. -/
def XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation : Prop :=
  ∀ q : XiZeroCopy,
    xiReciprocalCauchyRealKrylovSeam xiReciprocalSquareFixedCauchyPole q
      (xiWeilEvaluationLp
        (xiReciprocalSquareCauchyAdjointResponseTest
          (xiReciprocalSquareFixedCauchyPole : ℂ))
        (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
          xiReciprocalSquareFixedCauchyPole)) = 0

/-- Fixed adjoint-response seam saturation is equivalent to RH. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_riemannHypothesis :
    XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation ↔ RiemannHypothesis := by
  constructor
  · intro hseam
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have him :=
      xiSpectralPoint_im_eq_zero_of_adjointResponse_realKrylovSeam_eq_zero
        xiReciprocalSquareFixedCauchyPole
        (by rw [xiReciprocalSquareFixedCauchyPole_im]; norm_num)
        q (hseam q)
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simpa using him
  · intro hRH q
    rw [← xiReciprocalSquareFixedCauchyRealKrylov_X_sq_eq_adjointResponse_of_riemannHypothesis
      hRH]
    exact xiReciprocalCauchyRealKrylovSeam_polynomial_eq_zero
      xiReciprocalSquareFixedCauchyPole q (Polynomial.X ^ 2)

/-- Real response recovery automatically supplies all local seam equations. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovResponseRecovery_implies_seamSaturation
    (hrecovery : XiReciprocalSquareFixedCauchyRealKrylovResponseRecovery) :
    XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation := by
  rcases hrecovery with ⟨p, hp⟩
  intro q
  exact xiReciprocalCauchyRealKrylovSeam_eq_zero_of_tendsto
    xiReciprocalSquareFixedCauchyPole p
    (xiWeilEvaluationLp
      (xiReciprocalSquareCauchyAdjointResponseTest
        (xiReciprocalSquareFixedCauchyPole : ℂ))
      (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
        xiReciprocalSquareFixedCauchyPole)) hp q

/-- Local seam saturation constructively yields global real response recovery: unconditional complex
cyclicity supplies complex approximants, then coefficient symmetrization makes them real. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovResponseRecovery_of_seamSaturation
    (hseam : XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation) :
    XiReciprocalSquareFixedCauchyRealKrylovResponseRecovery := by
  obtain ⟨p, hp⟩ := exists_reciprocalCauchyKrylovPolynomials_tendsto_evaluation
    xiReciprocalSquareFixedCauchyPole
    (xiReciprocalSquareCauchyAdjointResponseTest
      (xiReciprocalSquareFixedCauchyPole : ℂ))
    (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
      xiReciprocalSquareFixedCauchyPole)
  exact exists_real_reciprocalCauchyKrylovPolynomials_tendsto_of_complex_tendsto_of_seam
    xiReciprocalSquareFixedCauchyPole
    (xiWeilEvaluationLp
      (xiReciprocalSquareCauchyAdjointResponseTest
        (xiReciprocalSquareFixedCauchyPole : ℂ))
      (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
        xiReciprocalSquareFixedCauchyPole)) p hp hseam

/-- Global real recovery and local adjoint-response seam saturation coincide constructively. -/
theorem xiReciprocalSquareFixedCauchyRealKrylovResponseRecovery_iff_seamSaturation :
    XiReciprocalSquareFixedCauchyRealKrylovResponseRecovery ↔
      XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation := by
  exact ⟨xiReciprocalSquareFixedCauchyRealKrylovResponseRecovery_implies_seamSaturation,
    xiReciprocalSquareFixedCauchyRealKrylovResponseRecovery_of_seamSaturation⟩

end

end RHTower
