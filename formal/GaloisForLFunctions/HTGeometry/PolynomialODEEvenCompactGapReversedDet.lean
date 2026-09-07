import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflection

/-! # The literal determinant reflected from its degree-twenty boundary -/
namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- The complete fixed correction in polynomial gap coordinates. -/
def evenCompactGapCorrectionPolynomial (u : ℝ) : Polynomial ℝ :=
  Polynomial.C (1000000000000 : ℝ)*evenCompactGapSourceZeroPolynomial u*
    (Polynomial.C (3 : ℝ)*evenCompactGapSourceZeroPolynomial u-Polynomial.C (6/19 : ℝ))

theorem evenCompactGapCorrectionPolynomial_degree (u : ℝ) :
    (evenCompactGapCorrectionPolynomial u).natDegree ≤ 2 := by
  have hQ := evenCompactGapSourceZeroPolynomial_degree u
  have hlarge : (Polynomial.C (1000000000000 : ℝ)*evenCompactGapSourceZeroPolynomial u).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans hQ
  have hthree : (Polynomial.C (3 : ℝ)*evenCompactGapSourceZeroPolynomial u).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans hQ
  have hconstant : (Polynomial.C (6/19 : ℝ)).natDegree ≤ 1 := by simp
  exact Polynomial.natDegree_mul_le_of_le hlarge
    (Polynomial.natDegree_sub_le_of_le hthree hconstant)

/-- The correction vanishes in the first six reversed coefficients. -/
theorem evenCompactGapCorrectionPolynomial_reflect_coeff (u : ℝ) (n : ℕ) (hn : n < 6) :
    (Polynomial.reflect 8 (evenCompactGapCorrectionPolynomial u)).coeff n = 0 := by
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by omega : n ≤ 8)]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact (evenCompactGapCorrectionPolynomial_degree u).trans_lt (by omega)

/-- Reversal retains every source polynomial and the full correction. -/
def evenCompactGapReversedDetPolynomial (u w : ℝ) : Polynomial ℝ :=
  hankelFourDet ((Polynomial.reflect 1 (evenCompactGapSourceZeroPolynomial u))^2)
    (-Polynomial.reflect 3 (evenCompactGapReflectedTwoPolynomial u w))
    (Polynomial.reflect 4 (evenCompactGapReflectedFourPolynomial u w))
    (-Polynomial.reflect 5 (evenCompactGapReflectedSixPolynomial u w))
    (Polynomial.reflect 6 (evenCompactGapReflectedEightPolynomial u w))
    (-Polynomial.reflect 7 (evenCompactGapReflectedTenPolynomial u w))
    (Polynomial.reflect 8 (evenCompactGapReflectedTwelvePolynomial u w)+
      Polynomial.reflect 8 (evenCompactGapCorrectionPolynomial u)) *
      Polynomial.C (((100 : ℝ)^12)⁻¹)

/-- Degree bounds justify weighted entrywise reflection of the entire determinant. -/
theorem evenCompactGapDetPolynomial_reflect (u w : ℝ) :
    Polynomial.reflect 20 (evenCompactGapDetPolynomial u w) =
      evenCompactGapReversedDetPolynomial u w := by
  have hQ : evenCompactGapReflection (evenCompactGapSourceZeroPolynomial u) 1
      (Polynomial.reflect 1 (evenCompactGapSourceZeroPolynomial u)) :=
    ⟨evenCompactGapSourceZeroPolynomial_degree u, rfl⟩
  have htwo : evenCompactGapReflection (evenCompactGapReflectedTwoPolynomial u w) 3
      (Polynomial.reflect 3 (evenCompactGapReflectedTwoPolynomial u w)) :=
    ⟨evenCompactGapReflectedTwoPolynomial_degree u w, rfl⟩
  have hfour : evenCompactGapReflection (evenCompactGapReflectedFourPolynomial u w) 4
      (Polynomial.reflect 4 (evenCompactGapReflectedFourPolynomial u w)) :=
    ⟨evenCompactGapReflectedFourPolynomial_degree u w, rfl⟩
  have hsix : evenCompactGapReflection (evenCompactGapReflectedSixPolynomial u w) 5
      (Polynomial.reflect 5 (evenCompactGapReflectedSixPolynomial u w)) :=
    ⟨evenCompactGapReflectedSixPolynomial_degree u w, rfl⟩
  have height : evenCompactGapReflection (evenCompactGapReflectedEightPolynomial u w) 6
      (Polynomial.reflect 6 (evenCompactGapReflectedEightPolynomial u w)) :=
    ⟨evenCompactGapReflectedEightPolynomial_degree u w, rfl⟩
  have hten : evenCompactGapReflection (evenCompactGapReflectedTenPolynomial u w) 7
      (Polynomial.reflect 7 (evenCompactGapReflectedTenPolynomial u w)) :=
    ⟨evenCompactGapReflectedTenPolynomial_degree u w, rfl⟩
  have htwelve : evenCompactGapReflection (evenCompactGapReflectedTwelvePolynomial u w) 8
      (Polynomial.reflect 8 (evenCompactGapReflectedTwelvePolynomial u w)) :=
    ⟨evenCompactGapReflectedTwelvePolynomial_degree u w, rfl⟩
  have hcorr : evenCompactGapReflection (evenCompactGapCorrectionPolynomial u) 8
      (Polynomial.reflect 8 (evenCompactGapCorrectionPolynomial u)) :=
    ⟨(evenCompactGapCorrectionPolynomial_degree u).trans (by omega), rfl⟩
  have hdet := evenCompactGapReflection.hankel _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hQ.pow 2) htwo.neg hfour hsix.neg height hten.neg (htwelve.add hcorr)
  have hfinal := hdet.mul (evenCompactGapReflection.constant (((100 : ℝ)^12)⁻¹))
  exact hfinal.2

/-- A coefficient near the top becomes a low coefficient in the reversed determinant. -/
theorem evenCompactGapDetPolynomial_coeff_from_reverse (u w : ℝ) (n : ℕ) (hn : n ≤ 20) :
    (evenCompactGapDetPolynomial u w).coeff (20-n) =
      (evenCompactGapReversedDetPolynomial u w).coeff n := by
  rw [← evenCompactGapDetPolynomial_reflect, Polynomial.coeff_reflect,
    Polynomial.revAt_le hn]

end
end HTGeometry
