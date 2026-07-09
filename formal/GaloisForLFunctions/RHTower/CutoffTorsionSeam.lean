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

/-- The one-label sheared torsion seam presentation attached to a concrete defect matrix. -/
def shearedTorsionSeam (m : ℕ) (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    TorsionSeamPresentation Unit (Fin 2) ℚ m where
  A := shearTorsionPresentation m
  Delta := fun _ => Delta
  det_eq := shearTorsionPresentation_det m

/-- The sheared torsion seam has the expected one-coordinate boundary class. -/
theorem shearedTorsionSeam_boundaryClass (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    (shearedTorsionSeam m Delta).boundaryClass () =
      jetClass ℚ m (Delta 0 0 - Delta 1 0) := by
  rw [TorsionSeamPresentation.boundaryClass, shearedTorsionSeam]
  exact fittingBoundaryClass_shearTorsion_apply m Delta

/-- For a sheared torsion seam, determinant compatibility is exactly divisibility of
the entry residue. -/
theorem shearedTorsionSeam_boundaryTraceDivisible_iff (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    (shearedTorsionSeam m Delta).BoundaryTraceDivisible () ↔
      (X : Polynomial ℚ) ^ m ∣ Delta 0 0 - Delta 1 0 := by
  change (X : Polynomial ℚ) ^ m ∣
      fittingBoundaryTrace (shearTorsionPresentation m) Delta ↔
    (X : Polynomial ℚ) ^ m ∣ Delta 0 0 - Delta 1 0
  calc
    (X : Polynomial ℚ) ^ m ∣ fittingBoundaryTrace (shearTorsionPresentation m) Delta
        ↔ fittingBoundaryClass m (shearTorsionPresentation m) Delta = 0 :=
          (fittingBoundaryClass_eq_zero_iff_trace_X_pow_dvd m
            (shearTorsionPresentation m) Delta).symm
    _ ↔ (X : Polynomial ℚ) ^ m ∣ Delta 0 0 - Delta 1 0 :=
          fittingBoundaryClass_shearTorsion_eq_zero_iff m Delta

/-- For the one-label sheared seam, determinant transversality is exactly
nondivisibility of the entry residue. -/
theorem shearedTorsionSeam_hasDeterminantTransverseDefect_iff (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    (shearedTorsionSeam m Delta).HasDeterminantTransverseDefect ↔
      ¬ (X : Polynomial ℚ) ^ m ∣ Delta 0 0 - Delta 1 0 := by
  constructor
  · rintro ⟨p, hp⟩
    cases p
    exact fun hdiv => hp ((shearedTorsionSeam_boundaryTraceDivisible_iff m Delta).mpr hdiv)
  · intro hndiv
    exact ⟨(), fun htrace => hndiv
      ((shearedTorsionSeam_boundaryTraceDivisible_iff m Delta).mp htrace)⟩

/-- A nondivisible sheared entry residue produces a right nonfake torsion seam defect. -/
theorem shearedTorsionSeam_defectNonmember_of_entryResidue_not_dvd (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ))
    (hres : ¬ (X : Polynomial ℚ) ^ m ∣ Delta 0 0 - Delta 1 0) :
    (shearedTorsionSeam m Delta).DefectNonmember () := by
  exact (shearedTorsionSeam m Delta).defectNonmember_of_not_traceDivisible
    (fun htrace => hres ((shearedTorsionSeam_boundaryTraceDivisible_iff m Delta).mp htrace))

/-- A nondivisible sheared entry residue also rules out left-factor fakeness. -/
theorem shearedTorsionSeam_defectLeftNonmember_of_entryResidue_not_dvd (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ))
    (hres : ¬ (X : Polynomial ℚ) ^ m ∣ Delta 0 0 - Delta 1 0) :
    (shearedTorsionSeam m Delta).DefectLeftNonmember () := by
  exact (shearedTorsionSeam m Delta).defectLeftNonmember_of_not_traceDivisible
    (fun htrace => hres ((shearedTorsionSeam_boundaryTraceDivisible_iff m Delta).mp htrace))

/-- In the standard two-region chart, the cross-boundary cochain has only the lower-left entry. -/
theorem standardCutoff_crossBoundary_lowerLeft
    (σ : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    crossBoundary (standardCutoff (R := ℚ)) σ = !![0, 0; σ 1 0, 0] := by
  have hsub : (!![(1 : Polynomial ℚ), 0; 0, 1] - !![(1 : Polynomial ℚ), 0; 0, 0]) =
      !![(0 : Polynomial ℚ), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hleft : (!![(0 : Polynomial ℚ), 0; 0, 1] * σ) =
      !![0, 0; σ 1 0, σ 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  rw [crossBoundary, standardCutoff, Matrix.one_fin_two, hsub, hleft]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- The sheared seam sees a standard-cutoff source action only through the lower-left
crossing entry. -/
theorem fittingBoundaryClass_shearTorsion_standardCutoff_crossBoundary (m : ℕ)
    (σ : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    fittingBoundaryClass m (shearTorsionPresentation m) (crossBoundary (standardCutoff (R := ℚ)) σ) =
      jetClass ℚ m (-(σ 1 0)) := by
  rw [fittingBoundaryClass_shearTorsion_apply]
  rw [standardCutoff_crossBoundary_lowerLeft]
  simp

/-- The packaged sheared seam of a standard-cutoff action is determinant-transverse
exactly when the lower-left crossing entry survives modulo `X^m`, up to sign. -/
theorem shearedStandardCutoffTorsionSeam_hasDeterminantTransverseDefect_iff (m : ℕ)
    (σ : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    (shearedTorsionSeam m (crossBoundary (standardCutoff (R := ℚ)) σ)).HasDeterminantTransverseDefect ↔
      ¬ (X : Polynomial ℚ) ^ m ∣ -(σ 1 0) := by
  rw [shearedTorsionSeam_hasDeterminantTransverseDefect_iff]
  rw [standardCutoff_crossBoundary_lowerLeft]
  simp

/-- A standard-cutoff action with lower-left crossing entry surviving modulo `X^m`
gives a right nonfake sheared torsion seam defect. -/
theorem shearedStandardCutoffTorsionSeam_defectNonmember_of_lowerLeft_not_dvd (m : ℕ)
    (σ : Matrix (Fin 2) (Fin 2) (Polynomial ℚ))
    (h : ¬ (X : Polynomial ℚ) ^ m ∣ -(σ 1 0)) :
    (shearedTorsionSeam m (crossBoundary (standardCutoff (R := ℚ)) σ)).DefectNonmember () := by
  exact shearedTorsionSeam_defectNonmember_of_entryResidue_not_dvd m
    (crossBoundary (standardCutoff (R := ℚ)) σ) (by
      rw [standardCutoff_crossBoundary_lowerLeft]
      simpa using h)

/-- The same lower-left entry condition also rules out left-factor fakeness. -/
theorem shearedStandardCutoffTorsionSeam_defectLeftNonmember_of_lowerLeft_not_dvd (m : ℕ)
    (σ : Matrix (Fin 2) (Fin 2) (Polynomial ℚ))
    (h : ¬ (X : Polynomial ℚ) ^ m ∣ -(σ 1 0)) :
    (shearedTorsionSeam m (crossBoundary (standardCutoff (R := ℚ)) σ)).DefectLeftNonmember () := by
  exact shearedTorsionSeam_defectLeftNonmember_of_entryResidue_not_dvd m
    (crossBoundary (standardCutoff (R := ℚ)) σ) (by
      rw [standardCutoff_crossBoundary_lowerLeft]
      simpa using h)

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
