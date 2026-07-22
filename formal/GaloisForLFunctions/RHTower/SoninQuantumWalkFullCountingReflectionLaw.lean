import GaloisForLFunctions.RHTower.SoninFullCountingReflection
import GaloisForLFunctions.RHTower.SoninProjectionQuantumWalk

/-!
# Sonin quantum-walk full-counting reflection

The Fourier-forbidden compression of the shifted two-projection quantum walk is twice the
interior Sonin alternating block.  Dividing by two therefore identifies a concrete compressed
unitary-walk coordinate with the full-counting interior operator.  Existing determinant reflection
then transports both degree-one and Hilbert--Carleman Fredholm germs to the exterior compression.
-/

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- The interior full-counting operator written directly as a compressed shifted unitary walk. -/
def centralSoninQuantumWalkInterior (a : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  (2 : ℂ)⁻¹ •
    ((centralFourierForbidden a).starProjection *
      (centralSoninProjectionQuantumWalk a + 1) *
        (centralFourierForbidden a).starProjection)

/-- The compressed shifted walk is exactly the central Sonin alternating block after the factor
two is removed. -/
theorem centralSoninQuantumWalkInterior_eq_alternatingBlock (a : ℝ) :
    centralSoninQuantumWalkInterior a =
      soninAlternatingBlock
        (centralPhysicalForbidden a) (centralFourierForbidden a) := by
  rw [centralSoninQuantumWalkInterior,
    centralFourier_compress_centralSoninProjectionQuantumWalk_add_one_eq_two_mul_prolateBlock]
  rw [two_mul, smul_add, ← add_smul]
  norm_num

/-- **Sonin unitary-walk full-counting reflection law.**  For every positive aperture, both
regularized determinant germs of the compressed shifted unitary walk agree with the corresponding
exterior Sonin determinant germs for every complex parameter. -/
theorem centralSoninQuantumWalk_fullCountingDeterminantReflection
    (a : ℝ) (ha : 0 < a) (z : ℂ) :
    HTGeometry.operatorFredholmDet1Germ (centralSoninQuantumWalkInterior a) z =
        HTGeometry.operatorFredholmDet1Germ
          (centralSoninExteriorCompression a) z ∧
      HTGeometry.operatorFredholmDet2Germ (centralSoninQuantumWalkInterior a) z =
        HTGeometry.operatorFredholmDet2Germ
          (centralSoninExteriorCompression a) z := by
  rw [centralSoninQuantumWalkInterior_eq_alternatingBlock]
  exact ⟨centralSoninFullCountingDet1Germ_eq a ha z,
    centralSoninFullCountingDet2Germ_eq a ha z⟩

end

end RHTower
