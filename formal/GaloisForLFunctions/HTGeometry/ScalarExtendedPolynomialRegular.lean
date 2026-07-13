import GaloisForLFunctions.HTGeometry.DisjointBlockPolynomialIndependence
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

namespace GaloisForLFunctions.HTGeometry

open scoped nonZeroDivisors

noncomputable section

/-- Scalar extension of a nonzero polynomial over a field is a non-zero-divisor over every
nontrivial algebra, even when the coefficient algebra itself has zero divisors. -/
theorem mvPolynomial_map_algebraMap_isRegular
    {k A σ : Type*} [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    [LinearOrder σ] [WellFoundedGT σ]
    (P : MvPolynomial σ k) (hP : P ≠ 0) :
    IsRegular (MvPolynomial.map (algebraMap k A) P) := by
  let m : MonomialOrder σ := MonomialOrder.lex
  have hinj : Function.Injective (algebraMap k A) :=
    FaithfulSMul.algebraMap_injective k A
  have hsupport : (MvPolynomial.map (algebraMap k A) P).support = P.support :=
    MvPolynomial.support_map_of_injective P hinj
  have hdegree : m.degree (MvPolynomial.map (algebraMap k A) P) = m.degree P := by
    simp only [MonomialOrder.degree, hsupport]
  have hleading :
      m.leadingCoeff (MvPolynomial.map (algebraMap k A) P) =
        algebraMap k A (m.leadingCoeff P) := by
    rw [MonomialOrder.leadingCoeff, hdegree, MvPolynomial.coeff_map]
    rfl
  rw [isRegular_iff_mem_nonZeroDivisors]
  apply m.mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors
  rw [hleading, ← isRegular_iff_mem_nonZeroDivisors]
  exact IsUnit.isRegular (isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr hP) |>.map _)

end
end GaloisForLFunctions.HTGeometry
