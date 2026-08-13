import GaloisForLFunctions.HTGeometry.NevanlinnaNormalizationTwist
import GaloisForLFunctions.HTGeometry.NevBauerMarkovFacesUnconditional

/-!
# Normalization independence of the constructed Nevanlinna retraction

The constructed boundary family of an indeterminate normalised moment sequence carries a canonical
constraint projector.  Changing the real determinant-one Nevanlinna matrix by an element of
`SL(2,ℝ)` produces the twisted family of the same moment sequence, and the projector, its range,
and the boundary simplex are unchanged.  The canonical retraction is therefore an invariant of the
moment sequence and not of the chosen matrix coordinate.
-/

open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

noncomputable section

variable {s : ℕ → ℝ}

/-- The constructed boundary family in a changed determinant-one normalization. -/
noncomputable def nevBoundaryFamilyTwist (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryFamily s :=
  (nevBoundaryFamily h h0b h0).twist g

/-- **The canonical constraint projector is independent of the Nevanlinna normalization.** -/
theorem nevCarrierProjector_twist (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (nevBoundaryFamilyTwist h h0b h0 g).carrierProjector =
      (nevBoundaryFamily h h0b h0).carrierProjector :=
  (nevBoundaryFamily h h0b h0).twist_carrierProjector g

/-- **The boundary carrier simplex is independent of the Nevanlinna normalization.** -/
theorem nevBarycenter_range_twist (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Set.range (nevBoundaryFamilyTwist h h0b h0 g).barycenter =
      Set.range (nevBoundaryFamily h h0b h0).barycenter :=
  (nevBoundaryFamily h h0b h0).twist_range_barycenter g

/-- The twisted leaves are the original leaves in the relabelled projective coordinate. -/
theorem nevBoundaryFamilyTwist_leaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : OnePoint ℝ) :
    (nevBoundaryFamilyTwist h h0b h0 g).leaf t =
      (nevBoundaryFamily h h0b h0).leaf (g.toGL • t) := rfl

/-- The twisted projective support label is the inverse Möbius image of the original label. -/
theorem nevBoundaryFamilyTwist_projectiveLabel (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : ℝ) :
    (nevBoundaryFamilyTwist h h0b h0 g).matrix.projectiveLabel x =
      (g⁻¹).toGL • (nevBoundaryFamily h h0b h0).matrix.projectiveLabel x :=
  (nevBoundaryFamily h h0b h0).matrix.twist_projectiveLabel g x

end

end HTGeometry
