import GaloisForLFunctions.HTGeometry.NavierStokesFiveBumpMomentSolve

/-!
# Five-moment profile Jacobian

Corollary A.3 of the supplied Navier--Stokes paper linearizes the five cumulative
moments into a two-row `U` block with weights `(1, x^(α+1/2))` and a three-row
`E` block with weights `(x^(1/2), x^α, x^(α-1))`.  These blocks are invertible
exactly away from the stated collisions `α = -1/2, 1/2, 3/2`.

This file first removes an artificial ordering restriction from the reusable
ordered-bump theorem by allowing exponent-row permutations.  It then proves
both Corollary A.3 blocks invertible and obtains the unique combined
five-coefficient solve for arbitrary targets.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesFiveMomentJacobian

open GaloisForLFunctions.HTGeometry.NavierStokesOrderedBumpMoments
open GaloisForLFunctions.HTGeometry.NavierStokesFiveBumpMomentSolve

noncomputable section

/-- Moment-matrix invertibility is unchanged by a permutation used to sort the exponent rows. -/
theorem isUnit_momentMatrix_of_reindex_strictMono {n : ℕ}
    (family : OrderedBumpFamily n) (alpha : Fin n → ℝ) (e : Equiv.Perm (Fin n))
    (halpha : StrictMono fun i ↦ alpha (e i)) :
    IsUnit (family.momentMatrix alpha) := by
  let sorted : Fin n → ℝ := fun i ↦ alpha (e i)
  have hsorted : IsUnit (family.momentMatrix sorted) :=
    family.isUnit_momentMatrix sorted halpha
  have hreindex :
      Matrix.reindex e.symm (Equiv.refl (Fin n)) (family.momentMatrix alpha) =
        family.momentMatrix sorted := by
    ext i j
    simp [OrderedBumpFamily.momentMatrix, realPowerMomentMatrix, sorted]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hdetSorted : (family.momentMatrix sorted).det ≠ 0 := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hsorted
    exact hsorted
  intro hdet
  apply hdetSorted
  rw [← hreindex, Matrix.det_reindex, hdet, mul_zero]

/-- Two linearized `U`-moment exponents from Corollary A.3. -/
def axialProfileMomentExponents (alpha : ℝ) : Fin 2 → ℝ :=
  ![0, alpha + 1 / 2]

/-- Three linearized `E`-moment exponents from Corollary A.3. -/
def azimuthalProfileMomentExponents (alpha : ℝ) : Fin 3 → ℝ :=
  ![1 / 2, alpha, alpha - 1]

theorem isUnit_axialProfileMomentMatrix {alpha : ℝ} (halpha : alpha ≠ -(1 / 2))
    (family : OrderedBumpFamily 2) :
    IsUnit (family.momentMatrix (axialProfileMomentExponents alpha)) := by
  by_cases h : alpha < -(1 / 2)
  · apply isUnit_momentMatrix_of_reindex_strictMono family
      (axialProfileMomentExponents alpha) (Equiv.swap 0 1)
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simp [axialProfileMomentExponents]
    linarith
  · have h' : -(1 / 2) < alpha := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm halpha)
    apply family.isUnit_momentMatrix (axialProfileMomentExponents alpha)
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simp [axialProfileMomentExponents]
    linarith

theorem isUnit_azimuthalProfileMomentMatrix {alpha : ℝ}
    (halphaHalf : alpha ≠ 1 / 2) (halphaThreeHalves : alpha ≠ 3 / 2)
    (family : OrderedBumpFamily 3) :
    IsUnit (family.momentMatrix (azimuthalProfileMomentExponents alpha)) := by
  by_cases hlow : alpha < 1 / 2
  · apply isUnit_momentMatrix_of_reindex_strictMono family
      (azimuthalProfileMomentExponents alpha) (Equiv.swap 0 2)
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;>
      simp [azimuthalProfileMomentExponents, Equiv.swap_apply_def]
    linarith
  · have hhalf : 1 / 2 < alpha := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm halphaHalf)
    by_cases hhigh : alpha < 3 / 2
    · let e : Equiv.Perm (Fin 3) := (Equiv.swap 0 2).trans (Equiv.swap 0 1)
      apply isUnit_momentMatrix_of_reindex_strictMono family
        (azimuthalProfileMomentExponents alpha) e
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      fin_cases i <;>
        simp [azimuthalProfileMomentExponents, e, Equiv.swap_apply_def] <;> linarith
    · have hthree : 3 / 2 < alpha :=
        lt_of_le_of_ne (le_of_not_gt hhigh) (Ne.symm halphaThreeHalves)
      apply isUnit_momentMatrix_of_reindex_strictMono family
        (azimuthalProfileMomentExponents alpha) (Equiv.swap 1 2)
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      fin_cases i <;>
        simp [azimuthalProfileMomentExponents, Equiv.swap_apply_def]
      linarith

/-- Corollary A.3: the two profile blocks have a unique five-coefficient solve. -/
theorem existsUnique_profileMomentCoefficients {alpha : ℝ}
    (halphaNegHalf : alpha ≠ -(1 / 2)) (halphaHalf : alpha ≠ 1 / 2)
    (halphaThreeHalves : alpha ≠ 3 / 2)
    (axial : OrderedBumpFamily 2) (azimuthal : OrderedBumpFamily 3)
    (targetAxial : Fin 2 → ℝ) (targetAzimuthal : Fin 3 → ℝ) :
    ∃! c : (Fin 2 → ℝ) × (Fin 3 → ℝ),
      (axial.momentMatrix (axialProfileMomentExponents alpha)).mulVec c.1 =
          targetAxial ∧
        (azimuthal.momentMatrix (azimuthalProfileMomentExponents alpha)).mulVec c.2 =
          targetAzimuthal := by
  have haxial := isUnit_axialProfileMomentMatrix halphaNegHalf axial
  have hazimuthal := isUnit_azimuthalProfileMomentMatrix halphaHalf halphaThreeHalves azimuthal
  obtain ⟨ca, hca⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr haxial targetAxial
  obtain ⟨ce, hce⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hazimuthal targetAzimuthal
  refine ⟨(ca, ce), ⟨hca, hce⟩, ?_⟩
  rintro ⟨da, de⟩ ⟨hda, hde⟩
  apply Prod.ext
  · exact Matrix.mulVec_injective_of_isUnit haxial (hda.trans hca.symm)
  · exact Matrix.mulVec_injective_of_isUnit hazimuthal (hde.trans hce.symm)

end

end GaloisForLFunctions.HTGeometry.NavierStokesFiveMomentJacobian
