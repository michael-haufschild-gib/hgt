import GaloisForLFunctions.HTGeometry.Octonion.Basic

open scoped Quaternion

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- The standard real basis `1,i,j,k` of the quaternion component. -/
def quaternionStandardBasis : Module.Basis (Fin 4) ℝ ℍ[ℝ] :=
  QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1 : ℝ)

/-- The eight-coordinate real basis induced from the two quaternion components of an octonion. -/
def standardBasis : Module.Basis (Fin 8) ℝ RealOctonion :=
  (quaternionStandardBasis.prod quaternionStandardBasis).reindex finSumFinEquiv

/-- Coordinate form of a real octonion endomorphism's determinant. -/
theorem det_eq_standardBasis_toMatrix_det (f : RealOctonion →ₗ[ℝ] RealOctonion) :
    LinearMap.det f = (LinearMap.toMatrix standardBasis standardBasis f).det := by
  exact (LinearMap.det_toMatrix standardBasis f).symm

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
