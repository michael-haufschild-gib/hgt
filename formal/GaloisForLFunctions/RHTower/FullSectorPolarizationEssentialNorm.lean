import GaloisForLFunctions.HTGeometry.FullSectorPolarizationLaw
import GaloisForLFunctions.RHTower.SchattenApproximation

/-!
# Essential-norm and Schatten consequences of full-sector polarization

The compact-perturbation floor from `FullSectorPolarizationLaw` is exactly a lower bound for the
project's essential norm.  Noncompactness also excludes every positive Schatten class.
-/

open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A positive correction coercive on a full infinite sign sector has essential norm at least
one. -/
theorem fullSector_one_le_essentialNorm
    (J G : E →L[ℂ] E) (S : Submodule ℂ E)
    (hS : IsClosed (S : Set E)) (hSinfinite : ¬ FiniteDimensional ℂ S)
    (hnegative : ∀ x ∈ S, J x = -x)
    (hpositive : ∀ x : E, 0 ≤ Complex.re ⟪(J + G) x, x⟫_ℂ) :
    1 ≤ essentialNorm G := by
  exact le_essentialNorm G 1 fun K hK =>
    fullSector_one_le_norm_sub_compact J G S hS hSinfinite hnegative hpositive K hK

/-- A positive correction coercive on a full infinite sign sector lies outside every Schatten
class of positive exponent. -/
theorem fullSector_not_memSchattenClass
    (J G : E →L[ℂ] E) (S : Submodule ℂ E)
    (hS : IsClosed (S : Set E)) (hSinfinite : ¬ FiniteDimensional ℂ S)
    (hnegative : ∀ x ∈ S, J x = -x)
    (hpositive : ∀ x : E, 0 ≤ Complex.re ⟪(J + G) x, x⟫_ℂ)
    {p : ℝ} (hp : 0 < p) :
    ¬ MemSchattenClass p G := by
  exact not_memSchattenClass_of_not_isCompactOperator hp
    (fullSector_not_isCompactOperator J G S hS hSinfinite hnegative hpositive)

end RHTower
