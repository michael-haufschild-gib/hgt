import GaloisForLFunctions.HTGeometry.PaperPolynomialPointEquiv
import GaloisForLFunctions.HTGeometry.PaperFourVariableClockObstruction
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.ZeroLocusInterface

/-!
# Every complex point fibre resists polynomial ambient straightening

The paper's radical zero-locus theorem promotes a setwise equality of complex
points to equality of the actual defining ideals. The already proved native
coordinate obstruction therefore applies even when rectification is requested
only as an equality of point sets.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate MvPolynomial

noncomputable section

/-- Ordinary complex points of an exact source fibre. -/
def paperPointFiber (t : ℂ) : Set (Fin 4 → ℂ) := {x | aeval x f = t}

/-- The standard coordinate hyperplane as an ordinary complex point set. -/
def paperPointHyperplane : Set (Fin 4 → ℂ) := {x | x 0 = 0}

/-- The fibre's actual prime ideal cuts out precisely its ordinary point set. -/
theorem paperPointFiber_zeroLocus (t : ℂ) :
    zeroLocus ℂ (fiberIdeal t) = paperPointFiber t :=
  ZeroLocusInterface.zeroLocus_fiber_ideal f t

/-- The standard prime hyperplane ideal has the expected complex points. -/
theorem paperPointHyperplane_zeroLocus :
    zeroLocus ℂ GeometricInterpretation.hyperplaneIdeal = paperPointHyperplane := by
  change zeroLocus ℂ (Ideal.span {(X (0 : Fin 4) : R 4)}) = {x : Fin 4 → ℂ | x 0 = 0}
  simpa only [map_zero, sub_zero, aeval_X] using
    ZeroLocusInterface.zeroLocus_fiber_ideal (X (0 : Fin 4) : R 4) 0

/-- No polynomial algebra automorphism straightens even the set of complex fibre points. -/
theorem paperPointFiber_no_ambient_automorphism (t : ℂ) :
    ¬ ∃ e : R 4 ≃ₐ[ℂ] R 4,
      ZeroLocusInterface.pointEquiv e '' paperPointFiber t = paperPointHyperplane := by
  rintro ⟨e, he⟩
  have hm := ZeroLocusInterface.map_ideal_eq_of_image_zeroLocus_eq e.symm
    (paperFiberIdeal_isPrime t).isRadical GeometricInterpretation.hyperplaneIdeal_isPrime.isRadical
  have hi : (fiberIdeal t).map e.symm.toRingHom = GeometricInterpretation.hyperplaneIdeal := by
    apply hm
    rw [paperPointFiber_zeroLocus, paperPointHyperplane_zeroLocus]
    exact he
  exact f_not_coordinate ((rectifiableFiber_iff_coordinate t).mp ⟨e.symm, hi⟩)

/-- The obstruction applies to every pair of polynomial inverse coordinate witnesses. -/
theorem paperPointFiber_no_polynomial_coordinates (t : ℂ) :
    ¬ ∃ e : AmbientMaps.PolynomialEquiv ℂ (Fin 4) (Fin 4),
      e.toPointMap '' paperPointFiber t = paperPointHyperplane := by
  rintro ⟨e, he⟩
  apply paperPointFiber_no_ambient_automorphism t
  refine ⟨paperPolynomialEquivAlgEquiv e, ?_⟩
  change AmbientMaps.pointMap (paperPolynomialEquivAlgEquiv e).toAlgHom ''
    paperPointFiber t = paperPointHyperplane
  rw [paperPolynomialEquivAlgEquiv_pointMap]
  exact he

end

end GaloisForLFunctions.HTGeometry
