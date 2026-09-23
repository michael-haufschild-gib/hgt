import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSourceZeroSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTwoSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedFourSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedSixSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedEightSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTenSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTwelveSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapTop

/-! # The top gap coefficient of the literal corrected determinant -/
namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- The degree-twenty coefficient follows from the seven source leading coefficients. -/
theorem evenCompactGapDetPolynomial_coeff_twenty (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 20 = evenCompactRawGapGrade20 u w := by
  have hQ : evenCompactGapTop (evenCompactGapSourceZeroPolynomial u) 1
      (evenCompactGapSourceZeroCoeff 1 u) :=
    ⟨evenCompactGapSourceZeroPolynomial_degree u,
      evenCompactGapSourceZeroPolynomial_coeff 1 u⟩
  have htwo : evenCompactGapTop (evenCompactGapReflectedTwoPolynomial u w) 3
      (evenCompactGapReflectedTwoCoeff 3 u w) :=
    ⟨evenCompactGapReflectedTwoPolynomial_degree u w,
      evenCompactGapReflectedTwoPolynomial_coeff 3 u w⟩
  have hfour : evenCompactGapTop (evenCompactGapReflectedFourPolynomial u w) 4
      (evenCompactGapReflectedFourCoeff 4 u w) :=
    ⟨evenCompactGapReflectedFourPolynomial_degree u w,
      evenCompactGapReflectedFourPolynomial_coeff 4 u w⟩
  have hsix : evenCompactGapTop (evenCompactGapReflectedSixPolynomial u w) 5
      (evenCompactGapReflectedSixCoeff 5 u w) :=
    ⟨evenCompactGapReflectedSixPolynomial_degree u w,
      evenCompactGapReflectedSixPolynomial_coeff 5 u w⟩
  have height : evenCompactGapTop (evenCompactGapReflectedEightPolynomial u w) 6
      (evenCompactGapReflectedEightCoeff 6 u w) :=
    ⟨evenCompactGapReflectedEightPolynomial_degree u w,
      evenCompactGapReflectedEightPolynomial_coeff 6 u w⟩
  have hten : evenCompactGapTop (evenCompactGapReflectedTenPolynomial u w) 7
      (evenCompactGapReflectedTenCoeff 7 u w) :=
    ⟨evenCompactGapReflectedTenPolynomial_degree u w,
      evenCompactGapReflectedTenPolynomial_coeff 7 u w⟩
  have htwelve : evenCompactGapTop (evenCompactGapReflectedTwelvePolynomial u w) 8
      (evenCompactGapReflectedTwelveCoeff 8 u w) :=
    ⟨evenCompactGapReflectedTwelvePolynomial_degree u w,
      evenCompactGapReflectedTwelvePolynomial_coeff 8 u w⟩
  let correction := Polynomial.C (1000000000000 : ℝ)*evenCompactGapSourceZeroPolynomial u*
    (Polynomial.C (3 : ℝ)*evenCompactGapSourceZeroPolynomial u-Polynomial.C (6/19 : ℝ))
  have hlarge : (Polynomial.C (1000000000000 : ℝ)*evenCompactGapSourceZeroPolynomial u).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans hQ.1
  have hthree : (Polynomial.C (3 : ℝ)*evenCompactGapSourceZeroPolynomial u).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans hQ.1
  have hconstant : (Polynomial.C (6/19 : ℝ)).natDegree ≤ 1 := by simp
  have hcorrection : correction.natDegree ≤ 2 :=
    Polynomial.natDegree_mul_le_of_le hlarge
      (Polynomial.natDegree_sub_le_of_le hthree hconstant)
  have hcorr : evenCompactGapTop correction 8 0 :=
    ⟨hcorrection.trans (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt
      (hcorrection.trans_lt (by omega))⟩
  have hdet := evenCompactGapTop.hankel _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hQ.pow 2) htwo.neg hfour hsix.neg height hten.neg (htwelve.add hcorr)
  have hfinal := hdet.mul (evenCompactGapTop.constant (((100 : ℝ)^(12 : ℕ))⁻¹))
  have hcoeff := hfinal.2
  change (evenCompactGapDetPolynomial u w).coeff 20 = _ at hcoeff
  rw [hcoeff]
  simp only [← evenCompactGapSourceZeroPolynomial_coeff,
    ← evenCompactGapReflectedTwoPolynomial_coeff,
    ← evenCompactGapReflectedFourPolynomial_coeff,
    ← evenCompactGapReflectedSixPolynomial_coeff,
    ← evenCompactGapReflectedEightPolynomial_coeff,
    ← evenCompactGapReflectedTenPolynomial_coeff,
    ← evenCompactGapReflectedTwelvePolynomial_coeff]
  norm_num [hankelFourDet, evenCompactRawGapGrade20,
    evenCompactGapSourceZeroPolynomial_coeff_slice0,
    evenCompactGapSourceZeroPolynomial_coeff_slice1,
    evenCompactGapSourceZeroPolynomial_coeff_above,
    evenCompactGapReflectedTwoPolynomial_coeff_slice0,
    evenCompactGapReflectedTwoPolynomial_coeff_slice1,
    evenCompactGapReflectedTwoPolynomial_coeff_slice2,
    evenCompactGapReflectedTwoPolynomial_coeff_slice3,
    evenCompactGapReflectedTwoPolynomial_coeff_above,
    evenCompactGapReflectedFourPolynomial_coeff_slice0,
    evenCompactGapReflectedFourPolynomial_coeff_slice1,
    evenCompactGapReflectedFourPolynomial_coeff_slice2,
    evenCompactGapReflectedFourPolynomial_coeff_slice3,
    evenCompactGapReflectedFourPolynomial_coeff_slice4,
    evenCompactGapReflectedFourPolynomial_coeff_above,
    evenCompactGapReflectedSixPolynomial_coeff_slice0,
    evenCompactGapReflectedSixPolynomial_coeff_slice1,
    evenCompactGapReflectedSixPolynomial_coeff_slice2,
    evenCompactGapReflectedSixPolynomial_coeff_slice3,
    evenCompactGapReflectedSixPolynomial_coeff_slice4,
    evenCompactGapReflectedSixPolynomial_coeff_slice5,
    evenCompactGapReflectedSixPolynomial_coeff_above,
    evenCompactGapReflectedEightPolynomial_coeff_slice0,
    evenCompactGapReflectedEightPolynomial_coeff_slice1,
    evenCompactGapReflectedEightPolynomial_coeff_slice2,
    evenCompactGapReflectedEightPolynomial_coeff_slice3,
    evenCompactGapReflectedEightPolynomial_coeff_slice4,
    evenCompactGapReflectedEightPolynomial_coeff_slice5,
    evenCompactGapReflectedEightPolynomial_coeff_slice6,
    evenCompactGapReflectedEightPolynomial_coeff_above,
    evenCompactGapReflectedTenPolynomial_coeff_slice0,
    evenCompactGapReflectedTenPolynomial_coeff_slice1,
    evenCompactGapReflectedTenPolynomial_coeff_slice2,
    evenCompactGapReflectedTenPolynomial_coeff_slice3,
    evenCompactGapReflectedTenPolynomial_coeff_slice4,
    evenCompactGapReflectedTenPolynomial_coeff_slice5,
    evenCompactGapReflectedTenPolynomial_coeff_slice6,
    evenCompactGapReflectedTenPolynomial_coeff_slice7,
    evenCompactGapReflectedTenPolynomial_coeff_above,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice0,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice1,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice2,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice3,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice4,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice5,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice6,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice7,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice8,
    evenCompactGapReflectedTwelvePolynomial_coeff_above]
  try dsimp only [evenCompactGapSourceZeroSlice0,
    evenCompactGapSourceZeroSlice1,
    evenCompactGapReflectedTwoSlice0,
    evenCompactGapReflectedTwoSlice1,
    evenCompactGapReflectedTwoSlice2,
    evenCompactGapReflectedTwoSlice3,
    evenCompactGapReflectedFourSlice0,
    evenCompactGapReflectedFourSlice1,
    evenCompactGapReflectedFourSlice2,
    evenCompactGapReflectedFourSlice3,
    evenCompactGapReflectedFourSlice4,
    evenCompactGapReflectedSixSlice0,
    evenCompactGapReflectedSixSlice1,
    evenCompactGapReflectedSixSlice2,
    evenCompactGapReflectedSixSlice3,
    evenCompactGapReflectedSixSlice4,
    evenCompactGapReflectedSixSlice5,
    evenCompactGapReflectedEightSlice0,
    evenCompactGapReflectedEightSlice1,
    evenCompactGapReflectedEightSlice2,
    evenCompactGapReflectedEightSlice3,
    evenCompactGapReflectedEightSlice4,
    evenCompactGapReflectedEightSlice5,
    evenCompactGapReflectedEightSlice6,
    evenCompactGapReflectedTenSlice0,
    evenCompactGapReflectedTenSlice1,
    evenCompactGapReflectedTenSlice2,
    evenCompactGapReflectedTenSlice3,
    evenCompactGapReflectedTenSlice4,
    evenCompactGapReflectedTenSlice5,
    evenCompactGapReflectedTenSlice6,
    evenCompactGapReflectedTenSlice7,
    evenCompactGapReflectedTwelveSlice0,
    evenCompactGapReflectedTwelveSlice1,
    evenCompactGapReflectedTwelveSlice2,
    evenCompactGapReflectedTwelveSlice3,
    evenCompactGapReflectedTwelveSlice4,
    evenCompactGapReflectedTwelveSlice5,
    evenCompactGapReflectedTwelveSlice6,
    evenCompactGapReflectedTwelveSlice7,
    evenCompactGapReflectedTwelveSlice8]

  ring1

end
end HTGeometry
