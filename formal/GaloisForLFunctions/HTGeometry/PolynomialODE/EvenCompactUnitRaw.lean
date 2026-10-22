import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactRawModel

/-! # Exact fixed-unit transport before expanding the determinant -/
namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- Seven checked source-moment identities transport the full corrected determinant. -/
theorem evenCompactUnitDet_square_eq_raw (u t v : ℝ) :
    evenCompactUnitDet (u^(2 : ℕ)) t v =
      evenCompactRawDet u (evenCompactUnitGap (u^(2 : ℕ)) t) (u*(1+v/4)) := by
  have hQ : evenCompactUnitSourceZero (u^(2 : ℕ)) t =
      oddCompactSourceZero u (evenCompactUnitGap (u^(2 : ℕ)) t) := rfl
  unfold evenCompactUnitDet evenCompactUnitCorrection
  rw [hQ, ← evenCompactSignedMoment_unit_eq 0 u t v,
    ← evenCompactSignedMoment_unit_eq 1 u t v,
    ← evenCompactSignedMoment_unit_eq 2 u t v,
    ← evenCompactSignedMoment_unit_eq 3 u t v,
    ← evenCompactSignedMoment_unit_eq 4 u t v,
    ← evenCompactSignedMoment_unit_eq 5 u t v,
    ← evenCompactSignedMoment_unit_eq 6 u t v]
  norm_num [evenCompactSignedMoment]
  unfold evenCompactRawDet hankelFourDet
  ring1

end
end HTGeometry
