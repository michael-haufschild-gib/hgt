import GaloisForLFunctions.HTGeometry.ProjectiveHorizonExplicitField

/-!
# The jet frame of a covector span

The initial square block of jets of a span is invertible, because its determinant is the nonzero
jet determinant.  It is therefore a frame: every jet column of the span has unique coordinates in
it, and those coordinates are the normalised quantities of the moving-frame picture.

The frame equation and its uniqueness are the algebraic content behind the codimension count: the
frame absorbs the observer group, and what is left over are the normalised coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The jet frame of a covector span: rows the span, columns the initial jet orders. -/
def jetFrame (t : Finset n) : Matrix ↥t ↥t (HomogeneousJetField n K) :=
  jetArray t fun m => (m : n)

omit [Fintype n] in
theorem jetFrame_det_ne_zero (t : Finset n) : (jetFrame (K := K) t).det ≠ 0 :=
  jetDet_ne_zero t

omit [Fintype n] in
theorem jetFrame_isUnit_det (t : Finset n) : IsUnit (jetFrame (K := K) t).det :=
  (jetFrame_det_ne_zero t).isUnit

/-- The jet column of a covector span at a given jet order. -/
def jetColumn (t : Finset n) (l : ℕ) : ↥t → HomogeneousJetField n K :=
  fun m => freeCoordinate K (n × ℕ) ((m : n), l)

/-- The coordinates of a jet column in the jet frame. -/
def frameCoord (t : Finset n) (l : ℕ) : ↥t → HomogeneousJetField n K :=
  (jetFrame t)⁻¹.mulVec (jetColumn t l)

omit [Fintype n] in
/-- **The frame equation.**  The frame coordinates reproduce the jet column. -/
theorem jetFrame_mulVec_frameCoord (t : Finset n) (l : ℕ) :
    (jetFrame (K := K) t).mulVec (frameCoord t l) = jetColumn t l := by
  rw [frameCoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (jetFrame_isUnit_det t),
    Matrix.one_mulVec]

omit [Fintype n] in
/-- **Uniqueness of frame coordinates.**  A jet frame is a basis: the coordinates of a jet column
are determined. -/
theorem frameCoord_unique {t : Finset n} {l : ℕ} {v : ↥t → HomogeneousJetField n K}
    (hv : (jetFrame (K := K) t).mulVec v = jetColumn t l) : v = frameCoord t l := by
  have hstep := congrArg (fun w => (jetFrame (K := K) t)⁻¹.mulVec w) hv
  simpa [frameCoord, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (jetFrame_isUnit_det t)] using hstep

omit [Fintype n] in
/-- The frame coordinates at the initial jet orders are the standard basis vectors. -/
theorem frameCoord_jetOrder (t : Finset n) (c : ↥t) :
    frameCoord (K := K) t (jetOrder t c) = Pi.single c 1 := by
  refine (frameCoord_unique ?_).symm
  ext m
  rw [Matrix.mulVec_single]
  simp [jetFrame, jetArray, jetColumn]

end

end GaloisForLFunctions.HTGeometry
