import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationRadialEdge

/-!
# Radial orientation of the product-fibre translation edge

Divisor reflection removes the sine channel before the finite translation edges are summed.
The remaining fixed-product edge still vanishes through degree `2*d+1`, so it has the same
forced radial factor as every individual edge.  Above the cutoff its coefficients are exactly
those of the product of the two reflected finite cosine packets.
-/

open Complex Polynomial Finset

namespace RHTower

noncomputable section

private lemma polynomial_coeff_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → Polynomial ℂ) (m : ℕ) :
    (∑ i ∈ s, F i).coeff m = ∑ i ∈ s, (F i).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, Polynomial.coeff_add]

/-- The complete finite translation edge on one positive product fibre. -/
def thetaProductFiberFiniteTranslationTopEdge
    (k d : ℕ) (x : ℝ) : Polynomial ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    finiteCosineTranslationTopEdge d x (thetaFactorPairLogDisplacement q)

/-- Product-fibre summation preserves the full forced zero at the spectral origin. -/
theorem thetaProductFiberFiniteTranslationTopEdge_X_pow_dvd
    (k d : ℕ) (x : ℝ) :
    (X : Polynomial ℂ) ^ (2 * d + 2) ∣
      thetaProductFiberFiniteTranslationTopEdge k d x := by
  rw [Polynomial.X_pow_dvd_iff]
  intro m hm
  unfold thetaProductFiberFiniteTranslationTopEdge
  rw [polynomial_coeff_finset_sum]
  apply Finset.sum_eq_zero
  intro q _hq
  exact finiteCosineTranslationTopEdge_coeff_eq_zero_of_le d x
    (thetaFactorPairLogDisplacement q) (by omega)

theorem exists_thetaProductFiberFiniteTranslationTopEdge_radialFactor
    (k d : ℕ) (x : ℝ) :
    ∃ R : Polynomial ℂ,
      thetaProductFiberFiniteTranslationTopEdge k d x =
        X ^ (2 * d + 2) * R := by
  obtain ⟨R, hR⟩ := thetaProductFiberFiniteTranslationTopEdge_X_pow_dvd k d x
  exact ⟨R, hR⟩

/-- Exact orientation split after divisor reflection.  In the upper half-plane the second term
is nonpositive and grows linearly with the finite-section degree. -/
theorem thetaProductFiberFiniteTranslationTopEdge_radial_current
    (k d : ℕ) (x : ℝ) (R : Polynomial ℂ)
    (hR : thetaProductFiberFiniteTranslationTopEdge k d x =
      X ^ (2 * d + 2) * R) (z : ℂ) :
    orientedPolynomialCurrent (thetaProductFiberFiniteTranslationTopEdge k d x) z =
      Complex.normSq z ^ (2 * d + 2) * orientedPolynomialCurrent R z -
        ((2 * d + 2 : ℕ) : ℝ) * z.im * Complex.normSq z ^ (2 * d + 1) *
          Complex.normSq (R.eval z) := by
  rw [hR, orientedPolynomialCurrent_X_pow_mul,
    show 2 * d + 2 - 1 = 2 * d + 1 by omega]

/-- A finite cosine section has no coefficient above its defining even degree. -/
theorem finiteCosinePolynomial_coeff_eq_zero_of_gt
    (d : ℕ) (x : ℝ) {m : ℕ} (hm : 2 * d < m) :
    (finiteCosinePolynomial d x).coeff m = 0 := by
  unfold finiteCosinePolynomial
  rw [polynomial_coeff_finset_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with heq
  · have hjd : j ≤ d := by simpa using hj
    omega
  · simp

/-- Above the cutoff, the translated finite sections themselves have disappeared.  The complete
product-fibre edge is therefore exactly the high-degree part of the reflected cosine product. -/
theorem thetaProductFiberFiniteTranslationTopEdge_coeff_eq_product_of_gt
    (k d : ℕ) (x : ℝ) {m : ℕ} (hm : 2 * d < m) :
    (thetaProductFiberFiniteTranslationTopEdge k d x).coeff m =
      (finiteCosinePolynomial d x *
        ∑ q ∈ thetaPositiveFactorPairs k,
          finiteCosinePolynomial d (thetaFactorPairLogDisplacement q)).coeff m := by
  have hsum := sum_finiteCosinePolynomial_add_factorPairs k d x
  unfold thetaProductFiberFiniteTranslationTopEdge
  rw [show (∑ q ∈ thetaPositiveFactorPairs k,
      finiteCosineTranslationTopEdge d x (thetaFactorPairLogDisplacement q)) =
      finiteCosinePolynomial d x *
        ∑ q ∈ thetaPositiveFactorPairs k,
          finiteCosinePolynomial d (thetaFactorPairLogDisplacement q) -
        ∑ q ∈ thetaPositiveFactorPairs k,
          finiteCosinePolynomial d
            (x + thetaFactorPairLogDisplacement q) by
      linear_combination hsum]
  rw [coeff_sub]
  have hz : (∑ q ∈ thetaPositiveFactorPairs k,
      finiteCosinePolynomial d (x + thetaFactorPairLogDisplacement q)).coeff m = 0 := by
    rw [polynomial_coeff_finset_sum]
    apply Finset.sum_eq_zero
    intro q _hq
    exact finiteCosinePolynomial_coeff_eq_zero_of_gt d _ hm
  rw [hz, sub_zero]

/-- Exact even coefficient of a finite cosine section. -/
theorem finiteCosinePolynomial_coeff_two_mul
    (d : ℕ) (x : ℝ) (j : ℕ) :
    (finiteCosinePolynomial d x).coeff (2 * j) =
      if j ≤ d then
        ((-1 : ℂ) ^ j * (x : ℂ) ^ (2 * j)) / (2 * j).factorial
      else 0 := by
  classical
  unfold finiteCosinePolynomial
  rw [polynomial_coeff_finset_sum]
  by_cases hj : j ≤ d
  · rw [if_pos hj]
    have hjmem : j ∈ Finset.range (d + 1) := by simpa using hj
    rw [Finset.sum_eq_single j]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl]
      simp
    · intro b _hb hbj
      rw [coeff_C_mul, coeff_X_pow, if_neg]
      · simp
      · intro h
        apply hbj
        omega
    · exact fun h => (h hjmem).elim
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hbj : b = j
    · subst b
      exact (hj (by simpa using hb)).elim
    · rw [coeff_C_mul, coeff_X_pow, if_neg]
      · simp
      · intro h
        apply hbj
        omega

/-- Finite cosine sections have no odd coefficient. -/
theorem finiteCosinePolynomial_coeff_two_mul_add_one
    (d : ℕ) (x : ℝ) (j : ℕ) :
    (finiteCosinePolynomial d x).coeff (2 * j + 1) = 0 := by
  unfold finiteCosinePolynomial
  rw [polynomial_coeff_finset_sum]
  apply Finset.sum_eq_zero
  intro b _hb
  rw [coeff_C_mul, coeff_X_pow, if_neg]
  · simp
  · omega

end

end RHTower

namespace RHTower

noncomputable section

/-- The even moment of the reflected logarithmic divisor packet. -/
def thetaProductFiberEvenMoment (k r : ℕ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    thetaFactorPairLogDisplacement q ^ (2 * r)

/-- Every reflected divisor-packet even moment is nonnegative. -/
theorem thetaProductFiberEvenMoment_nonneg (k r : ℕ) :
    0 ≤ thetaProductFiberEvenMoment k r := by
  unfold thetaProductFiberEvenMoment
  apply Finset.sum_nonneg
  intro q _hq
  exact (even_two_mul r).pow_nonneg _

/-- Exact coefficient of the reflected cosine packet.  Divisor reflection has converted every
surviving coefficient into one nonnegative arithmetic even moment with the universal alternating
cosine sign. -/
theorem coeff_sum_finiteCosinePolynomial_thetaFactorPairLogDisplacement_two_mul
    (k d l : ℕ) :
    (∑ q ∈ thetaPositiveFactorPairs k,
      finiteCosinePolynomial d (thetaFactorPairLogDisplacement q)).coeff (2 * l) =
      if l ≤ d then
        ((-1 : ℂ) ^ l * (thetaProductFiberEvenMoment k l : ℂ)) /
          (2 * l).factorial
      else 0 := by
  rw [Polynomial.finsetSum_coeff]
  by_cases hl : l ≤ d
  · rw [if_pos hl]
    simp_rw [finiteCosinePolynomial_coeff_two_mul, if_pos hl]
    unfold thetaProductFiberEvenMoment
    rw [Complex.ofReal_sum]
    rw [← Finset.sum_div, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro q _hq
    rw [Complex.ofReal_pow]
  · rw [if_neg hl]
    simp_rw [finiteCosinePolynomial_coeff_two_mul, if_neg hl]
    simp

end

end RHTower
