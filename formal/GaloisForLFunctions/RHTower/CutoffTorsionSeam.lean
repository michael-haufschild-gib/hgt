import GaloisForLFunctions.RHTower.CutoffCochain
import GaloisForLFunctions.RHTower.MPlusTorsionSeam

/-!
# Packaging the cutoff-crossing witness as a torsion seam object

`CutoffCochain.lean` proves that a boundary-crossing cochain can be determinant-
transverse and nonfake.  `MPlusTorsionSeam.lean` defines the seam interface needed
by the extended `M+` category.  This file connects them: the cutoff-crossing witness
is packaged as a one-label `TorsionSeamPresentation`, and hence as an extended
`M+` object over any inhabited base.

The result is still abstract algebra.  It does not identify the actual semilocal
Sonin operator with this witness; it proves that the surviving cutoff shape really
lives inside the torsion seam presentation layer.
-/

noncomputable section

namespace RHTower

open Matrix Polynomial

/-- A cutoff-crossing cochain packages as a one-label torsion seam presentation with
determinant-transverse defect and two-sided nonmembership. -/
theorem exists_crossing_cutoffTorsionSeam (m : ℕ) (hm : 0 < m) :
    ∃ (S : TorsionSeamPresentation Unit (Fin 2) ℚ m)
      (e σ : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)),
      IsIdempotentElem e ∧ σ * e ≠ e * σ ∧
      S.A.det = (X : Polynomial ℚ) ^ m ∧
      S.Delta () = crossBoundary e σ ∧
      S.HasDeterminantTransverseDefect ∧
      S.DefectNonmember () ∧ S.DefectLeftNonmember () := by
  obtain ⟨e, σ, A, he, hnotcomm, hdet, hclass⟩ := exists_nonfake_crossBoundary_not_commute m hm
  let S : TorsionSeamPresentation Unit (Fin 2) ℚ m :=
    { A := A
      Delta := fun _ => crossBoundary e σ
      det_eq := hdet }
  have hnotdiv : ¬ (X : Polynomial ℚ) ^ m ∣ fittingBoundaryTrace A (crossBoundary e σ) :=
    (fittingBoundaryClass_ne_zero_iff_not_trace_X_pow_dvd m A (crossBoundary e σ)).mp hclass
  have hpoint : ¬ S.BoundaryTraceDivisible () := by
    simpa [S, TorsionSeamPresentation.BoundaryTraceDivisible,
      TorsionSeamPresentation.boundaryTrace] using hnotdiv
  have htrans : S.HasDeterminantTransverseDefect := ⟨(), hpoint⟩
  exact ⟨S, e, σ, he, hnotcomm, S.det_eq, rfl, htrans,
    S.defectNonmember_of_not_traceDivisible hpoint,
    S.defectLeftNonmember_of_not_traceDivisible hpoint⟩

/-- Over any inhabited regular `M+` base, the cutoff-crossing seam gives an extended
`M+` object whose unique sigma defect is determinant-transverse and nonfake. -/
theorem exists_crossing_cutoffMPlusTorsionSeamObject (Base : Type*) [Inhabited Base]
    (m : ℕ) (hm : 0 < m) :
    ∃ (O : MPlusTorsionSeamObject Base Unit (Fin 2) ℚ m)
      (e σ : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)),
      IsIdempotentElem e ∧ σ * e ≠ e * σ ∧
      O.seam.A.det = (X : Polynomial ℚ) ^ m ∧
      O.seam.Delta () = crossBoundary e σ ∧
      O.seam.HasDeterminantTransverseDefect ∧
      O.seam.DefectNonmember () ∧ O.seam.DefectLeftNonmember () := by
  obtain ⟨S, e, σ, he, hnotcomm, hdet, hDelta, htrans, hright, hleft⟩ :=
    exists_crossing_cutoffTorsionSeam m hm
  exact ⟨{ base := default, seam := S }, e, σ, he, hnotcomm, hdet, hDelta, htrans, hright, hleft⟩

end RHTower
