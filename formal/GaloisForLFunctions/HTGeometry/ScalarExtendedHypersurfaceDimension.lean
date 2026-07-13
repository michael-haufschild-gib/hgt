import GaloisForLFunctions.HTGeometry.ScalarExtendedPolynomialRegular
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

namespace GaloisForLFunctions.HTGeometry

open scoped nonZeroDivisors

noncomputable section

/-- A nonzero scalar polynomial cuts Krull dimension by at least one after extension to an
arbitrary nontrivial Noetherian coefficient algebra. -/
theorem scalarExtendedHypersurface_krullDim_add_one_le
    {k A σ : Type*} [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    [IsNoetherianRing A] [Finite σ] [LinearOrder σ] [WellFoundedGT σ]
    (P : MvPolynomial σ k) (hP : P ≠ 0) :
    ringKrullDim
          ((MvPolynomial σ A) ⧸
            Ideal.span {MvPolynomial.map (algebraMap k A) P}) + 1 ≤
      ringKrullDim A + Nat.card σ := by
  rw [← MvPolynomial.ringKrullDim_of_isNoetherianRing]
  exact ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mvPolynomial_map_algebraMap_isRegular P hP).mem_nonZeroDivisors

end
end GaloisForLFunctions.HTGeometry
