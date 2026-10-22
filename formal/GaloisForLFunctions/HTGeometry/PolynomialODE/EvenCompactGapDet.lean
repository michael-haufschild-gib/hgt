import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapLift

/-! # The raw determinant as a bounded-degree polynomial in the gap -/
namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxRecDepth 10000

local notation "dm" => Polynomial.natDegree_mul_le_of_le
local notation "da" => Polynomial.natDegree_add_le_of_degree_le
local notation "ds" => Polynomial.natDegree_sub_le_of_le
local notation "dp" => Polynomial.natDegree_pow_le_of_le

private theorem evenCompactHankelGapDegree (a b c d e f g : Polynomial ℝ)
    (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 3) (hc : c.natDegree ≤ 4)
    (hd : d.natDegree ≤ 5) (he : e.natDegree ≤ 6) (hf : f.natDegree ≤ 7)
    (hg : g.natDegree ≤ 8) :
    (hankelFourDet a b c d e f g).natDegree ≤ 20 := by
  have htwo : (2 : Polynomial ℝ).natDegree ≤ 0 := by simp
  have hhead : (a*c*e-a*d^(2 : ℕ)-b^(2 : ℕ)*e+2*b*c*d-c^(3 : ℕ)).natDegree ≤ 12 :=
    ds (da (ds (ds (dm (dm ha hc) he) (dm ha (dp 2 hd)))
      (dm (dp 2 hb) he)) (Polynomial.natDegree_mul_le_of_le (m := 7) (n := 5) (Polynomial.natDegree_mul_le_of_le (m := 3) (n := 4) (Polynomial.natDegree_mul_le_of_le (m := 0) (n := 3) htwo hb) hc) hd)) (dp 3 hc)
  have h1 : ((c*e-d^(2 : ℕ))*d^(2 : ℕ)).natDegree ≤ 20 :=
    dm (ds (dm hc he) (dp 2 hd)) (dp 2 hd)
  have h2 : (2*(c*d-b*e)*d*e).natDegree ≤ 20 :=
    dm (dm (dm htwo (ds (dm hc hd) (dm hb he))) hd) he
  have h3 : (2*(b*d-c^(2 : ℕ))*d*f).natDegree ≤ 20 :=
    dm (dm (dm htwo (ds (dm hb hd) (dp 2 hc))) hd) hf
  have h4 : ((a*e-c^(2 : ℕ))*e^(2 : ℕ)).natDegree ≤ 20 :=
    dm (ds (dm ha he) (dp 2 hc)) (dp 2 he)
  have h5 : (2*(b*c-a*d)*e*f).natDegree ≤ 20 :=
    dm (dm (dm htwo (ds (dm hb hc) (dm ha hd))) he) hf
  have h6 : ((a*c-b^(2 : ℕ))*f^(2 : ℕ)).natDegree ≤ 20 :=
    dm (ds (dm ha hc) (dp 2 hb)) (dp 2 hf)
  exact ds (dm hhead hg) (da (da (da (da (da h1 h2) h3) h4) h5) h6)

/-- Polynomial determinant formed from the exact lifted source entries. -/
def evenCompactGapDetPolynomial (u w : ℝ) : Polynomial ℝ :=
  hankelFourDet ((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ))
    (-evenCompactGapReflectedTwoPolynomial u w)
    (evenCompactGapReflectedFourPolynomial u w)
    (-evenCompactGapReflectedSixPolynomial u w)
    (evenCompactGapReflectedEightPolynomial u w)
    (-evenCompactGapReflectedTenPolynomial u w)
    (evenCompactGapReflectedTwelvePolynomial u w+
      Polynomial.C (1000000000000 : ℝ)*evenCompactGapSourceZeroPolynomial u*
        (Polynomial.C (3 : ℝ)*evenCompactGapSourceZeroPolynomial u-Polynomial.C (6/19 : ℝ))) *
      Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- Polynomial evaluation is exactly the complete corrected raw determinant. -/
theorem evenCompactGapDetPolynomial_eval (u a w : ℝ) :
    (evenCompactGapDetPolynomial u w).eval a = evenCompactRawDet u a w := by
  dsimp only [evenCompactGapDetPolynomial, evenCompactRawDet, hankelFourDet]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_ofNat,
    evenCompactGapSourceZeroPolynomial_eval, evenCompactGapReflectedTwoPolynomial_eval,
    evenCompactGapReflectedFourPolynomial_eval, evenCompactGapReflectedSixPolynomial_eval,
    evenCompactGapReflectedEightPolynomial_eval, evenCompactGapReflectedTenPolynomial_eval,
    evenCompactGapReflectedTwelvePolynomial_eval, div_eq_mul_inv]

/-- Every determinant monomial has gap degree at most twenty. -/
theorem evenCompactGapDetPolynomial_degree (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).natDegree ≤ 20 := by
  have hQ := evenCompactGapSourceZeroPolynomial_degree u
  have hlarge : (Polynomial.C (1000000000000 : ℝ)*evenCompactGapSourceZeroPolynomial u).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans hQ
  have hthree : (Polynomial.C (3 : ℝ)*evenCompactGapSourceZeroPolynomial u).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans hQ
  have hconstant : (Polynomial.C (6/19 : ℝ)).natDegree ≤ 1 := by simp
  have hcorrection : (Polynomial.C (1000000000000 : ℝ)*evenCompactGapSourceZeroPolynomial u*
      (Polynomial.C (3 : ℝ)*evenCompactGapSourceZeroPolynomial u-Polynomial.C (6/19 : ℝ))).natDegree ≤ 2 :=
    dm hlarge (ds hthree hconstant)
  have hlast := da (evenCompactGapReflectedTwelvePolynomial_degree u w)
    (hcorrection.trans (by omega : 2 ≤ 8))
  unfold evenCompactGapDetPolynomial
  apply (Polynomial.natDegree_mul_C_le _ _).trans
  exact evenCompactHankelGapDegree _ _ _ _ _ _ _ (dp 2 hQ)
    (Polynomial.natDegree_neg_le_of_le (evenCompactGapReflectedTwoPolynomial_degree u w))
    (evenCompactGapReflectedFourPolynomial_degree u w)
    (Polynomial.natDegree_neg_le_of_le (evenCompactGapReflectedSixPolynomial_degree u w))
    (evenCompactGapReflectedEightPolynomial_degree u w)
    (Polynomial.natDegree_neg_le_of_le (evenCompactGapReflectedTenPolynomial_degree u w)) hlast


/-- The already checked raw coefficient table, without expanding any coefficient. -/
def evenCompactGapTablePolynomial (u w : ℝ) : Polynomial ℝ :=
  compactGapPolynomial% (fun a : ℝ => evenCompactRawPolynomial u a w)

/-- Evaluation gives the exact existing gap-graded raw polynomial. -/
theorem evenCompactGapTablePolynomial_eval (u a w : ℝ) :
    (evenCompactGapTablePolynomial u w).eval a = evenCompactRawPolynomial u a w := by
  dsimp only [evenCompactGapTablePolynomial, evenCompactRawPolynomial]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

/-- No coefficient above degree twenty occurs in the existing raw table. -/
theorem evenCompactGapTablePolynomial_degree (u w : ℝ) :
    (evenCompactGapTablePolynomial u w).natDegree ≤ 20 := by
  unfold evenCompactGapTablePolynomial
  compute_degree

end
end HTGeometry
