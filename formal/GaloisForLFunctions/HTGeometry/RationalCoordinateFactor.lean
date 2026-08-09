import GaloisForLFunctions.HTGeometry.PairTopDegree

/-!
# Rational factors at one coordinate

A first-order linear equation with **rational** coefficients places a ratio of two univariate
factors at a coordinate.  Everything the peel reads off such a ratio is the difference of what it
reads off the two polynomials: the logarithmic derivative, its degree, and its residue at infinity
are all additive in the numerator and denominator.

That is what makes the rational case a corollary of the polynomial one rather than a second theory.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## The polynomial logarithmic factor, without a degree hypothesis -/

/-- **A logarithmic factor always has degree `−1`.**  A constant contributes zero. -/
theorem topDegLE_logFactor_all (m : ℕ) (q : Polynomial ℂ) :
    TopDegLE m (-1) (logFactor q m) := by
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | h0
  · rw [logFactor_eq_zero_of_natDegree_zero h0]
    exact topDegLE_zero _ _
  · exact topDegLE_logFactor m h0

/-- **The residue at infinity of a logarithmic factor is its degree**, with no hypothesis. -/
theorem topLim_fx_mul_logFactor_all (m : ℕ) (q : Polynomial ℂ) :
    TopLim m (fx m * logFactor q m) (algebraMap ℂ CascadeField (q.natDegree : ℂ)) := by
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | h0
  · rw [logFactor_eq_zero_of_natDegree_zero h0, mul_zero, h0]
    simp only [Nat.cast_zero, map_zero]
    exact topLim_const
  · exact topLim_fx_mul_logFactor m h0

/-! ## The rational factor -/

/-- A rational function of one coordinate: a ratio of two univariate factors. -/
noncomputable def ratFact (n d : Polynomial ℂ) (j : ℕ) : CascadeField :=
  fact n j / fact d j

/-- Its logarithmic derivative: the difference of the two logarithmic factors. -/
noncomputable def logRatFactor (n d : Polynomial ℂ) (j : ℕ) : CascadeField :=
  logFactor n j - logFactor d j

theorem ratFact_ne_zero {n d : Polynomial ℂ} (hn : n ≠ 0) (hd : d ≠ 0) (j : ℕ) :
    ratFact n d j ≠ 0 :=
  div_ne_zero (fact_ne_zero hn j) (fact_ne_zero hd j)

theorem inv_ratFact (n d : Polynomial ℂ) (j : ℕ) : (ratFact n d j)⁻¹ = ratFact d n j := by
  rw [ratFact, ratFact, inv_div]

theorem ratFact_mem_coordField {j m : ℕ} (h : j ≤ m) (n d : Polynomial ℂ) :
    ratFact n d j ∈ coordField m :=
  div_mem (fact_mem_coordField h n) (fact_mem_coordField h d)

theorem logFactor_mem_coordField {j m : ℕ} (h : j ≤ m) (q : Polynomial ℂ) :
    logFactor q j ∈ coordField m := by
  rw [logFactor]
  exact div_mem (fact_mem_coordField h _) (fact_mem_coordField h q)

theorem logRatFactor_mem_coordField {j m : ℕ} (h : j ≤ m) (n d : Polynomial ℂ) :
    logRatFactor n d j ∈ coordField m :=
  sub_mem (logFactor_mem_coordField h n) (logFactor_mem_coordField h d)

/-! ## The coordinate derivations -/

theorem fpderiv_ratFact_of_ne {n d : Polynomial ℂ} {j k : ℕ} (h : j ≠ k) :
    fpderiv k (ratFact n d j) = 0 := by
  rw [ratFact, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
    fpderiv_fact_of_ne h, fpderiv_fact_of_ne h]
  simp

/-- **A derivation differentiates a rational factor logarithmically.** -/
theorem derivation_ratFact (D : Derivation ℂ CascadeField CascadeField) {n d : Polynomial ℂ}
    (hn : n ≠ 0) (hd : d ≠ 0) (j : ℕ) :
    D (ratFact n d j) = ratFact n d j * logRatFactor n d j * D (fx j) := by
  have hN : fact n j ≠ 0 := fact_ne_zero hn j
  have hD : fact d j ≠ 0 := fact_ne_zero hd j
  rw [ratFact, logRatFactor, logFactor, logFactor, div_eq_mul_inv, Derivation.leibniz,
    Derivation.leibniz_inv, derivation_fact, derivation_fact]
  simp only [smul_eq_mul]
  field_simp
  ring

/-! ## Freedom, degree, and residue -/

theorem topFree_ratFact {m j : ℕ} (h : m ≠ j) (n d : Polynomial ℂ) :
    TopFree m (ratFact n d j) := by
  rw [ratFact, div_eq_mul_inv]
  exact TopFree.mul (topFree_fact h n) (topFree_inv_fact h d)

theorem topFree_logRatFactor {m j : ℕ} (h : m ≠ j) (n d : Polynomial ℂ) :
    TopFree m (logRatFactor n d j) :=
  TopFree.sub (topFree_logFactor h n) (topFree_logFactor h d)

theorem topDegLE_ratFact (j : ℕ) {n d : Polynomial ℂ} (hd : d ≠ 0) :
    TopDegLE j ((n.natDegree : ℤ) - (d.natDegree : ℤ)) (ratFact n d j) := by
  rw [ratFact, div_eq_mul_inv]
  have h := TopDegLE.mul (topDegLE_fact j n) (topDegLE_inv_fact j hd)
  refine TopDegLE.mono ?_ h
  omega

theorem topDegLE_inv_ratFact (j : ℕ) {n d : Polynomial ℂ} (hn : n ≠ 0) :
    TopDegLE j ((d.natDegree : ℤ) - (n.natDegree : ℤ)) ((ratFact n d j)⁻¹) := by
  rw [inv_ratFact]
  exact topDegLE_ratFact j hn

/-- **A rational logarithmic derivative has degree `−1`.** -/
theorem topDegLE_logRatFactor (m : ℕ) (n d : Polynomial ℂ) :
    TopDegLE m (-1) (logRatFactor n d m) := by
  rw [logRatFactor]
  exact TopDegLE.sub (topDegLE_logFactor_all m n) (topDegLE_logFactor_all m d)

/-- **The residue at infinity of a rational logarithmic derivative is the degree difference.** -/
theorem topLim_fx_mul_logRatFactor (m : ℕ) (n d : Polynomial ℂ) :
    TopLim m (fx m * logRatFactor n d m)
      (algebraMap ℂ CascadeField ((n.natDegree : ℂ) - (d.natDegree : ℂ))) := by
  rw [logRatFactor, mul_sub, map_sub, sub_eq_add_neg, sub_eq_add_neg]
  exact TopLim.add (topLim_fx_mul_logFactor_all m n)
    (TopLim.neg (topLim_fx_mul_logFactor_all m d))

end GaloisForLFunctions.HTGeometry
