import GaloisForLFunctions.HTGeometry.AdditiveCocycleTriangleSupportHasse
import GaloisForLFunctions.RHTower.ResidueJetSpectralSuspension
import GaloisForLFunctions.RHTower.XiPairwiseShiftValueReflection

/-!
# Hasse support for residue and completed-Xi pair cocycles

Three corpus pair-groupoid cocycles are packaged as finite reciprocity profiles: corrected
completed-Xi shift differences, logarithmic residue-jet torsions, and logarithmic relative
determinant torsions.  Each profile has zero sum, so no one local comparison can be active alone.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Corrected completed-Xi shift differences -/

/-- Three corrected completed-Xi shift differences as an additive reciprocity packet. -/
def xiPairwiseShiftTriangleProfile (a b c : ℕ) (s : ℂ) : Fin 3 →₀ ℂ :=
  additiveCocycleTriangleProfile
    (fun m n => xiPairwiseShiftPrimeDifference m n s) a b c

@[simp]
theorem xiPairwiseShiftTriangleProfile_zero (a b c : ℕ) (s : ℂ) :
    xiPairwiseShiftTriangleProfile a b c s 0 = xiPairwiseShiftPrimeDifference a b s := rfl

@[simp]
theorem xiPairwiseShiftTriangleProfile_one (a b c : ℕ) (s : ℂ) :
    xiPairwiseShiftTriangleProfile a b c s 1 = xiPairwiseShiftPrimeDifference b c s := rfl

@[simp]
theorem xiPairwiseShiftTriangleProfile_two (a b c : ℕ) (s : ℂ) :
    xiPairwiseShiftTriangleProfile a b c s 2 = -xiPairwiseShiftPrimeDifference a c s := rfl

/-- Corrected completed-Xi shift differences obey three-place reciprocity. -/
theorem xiPairwiseShiftTriangleProfile_sum_eq_zero (a b c : ℕ) (s : ℂ) :
    (xiPairwiseShiftTriangleProfile a b c s).sum (fun _ z => z) = 0 :=
  additiveCocycleTriangleProfile_sum_eq_zero
    (fun m n => xiPairwiseShiftPrimeDifference m n s) a b c
    (xiPairwiseShiftPrimeDifference_cocycle a b c s)

/-- A nonzero corrected Xi shift comparison forces another nonzero comparison in its triangle. -/
theorem xiPairwiseShiftPrimeDifference_nonzero_has_triangle_partner
    (a b c : ℕ) (s : ℂ) (hab : xiPairwiseShiftPrimeDifference a b s ≠ 0) :
    xiPairwiseShiftPrimeDifference b c s ≠ 0 ∨
      xiPairwiseShiftPrimeDifference a c s ≠ 0 := by
  obtain ⟨j, hj0, hj⟩ := additiveCocycleTriangleProfile_exists_other_nonzero
    (fun m n => xiPairwiseShiftPrimeDifference m n s) a b c
    (xiPairwiseShiftPrimeDifference_cocycle a b c s) (i := 0) (by simpa using hab)
  fin_cases j
  · exact absurd rfl hj0
  · left
    simpa using hj
  · right
    simpa using hj

/-- A nonzero completed-Xi comparison triangle occupies at least two comparison channels. -/
theorem xiPairwiseShiftTriangleProfile_two_le_support_card
    (a b c : ℕ) (s : ℂ) (hne : xiPairwiseShiftTriangleProfile a b c s ≠ 0) :
    2 ≤ (xiPairwiseShiftTriangleProfile a b c s).support.card :=
  additiveCocycleTriangleProfile_two_le_support_card
    (fun m n => xiPairwiseShiftPrimeDifference m n s) a b c
    (xiPairwiseShiftPrimeDifference_cocycle a b c s) hne

/-! ## Residue-jet logarithmic torsion -/

/-- Arguments of three residue-jet torsions before exponentiation, as a reciprocity packet. -/
def residueJetLogTorsionTriangleProfile
    (p : ℕ) (b c d : ℕ → ℂ) (z : ℂ) : Fin 3 →₀ ℂ :=
  pairDescentTriangleProfile (fun e => residueJetPolynomial p e z) b c d

@[simp]
theorem residueJetLogTorsionTriangleProfile_zero
    (p : ℕ) (b c d : ℕ → ℂ) (z : ℂ) :
    residueJetLogTorsionTriangleProfile p b c d z 0 =
      residueJetPolynomial p b z - residueJetPolynomial p c z := rfl

@[simp]
theorem residueJetLogTorsionTriangleProfile_one
    (p : ℕ) (b c d : ℕ → ℂ) (z : ℂ) :
    residueJetLogTorsionTriangleProfile p b c d z 1 =
      residueJetPolynomial p c z - residueJetPolynomial p d z := rfl

@[simp]
theorem residueJetLogTorsionTriangleProfile_two
    (p : ℕ) (b c d : ℕ → ℂ) (z : ℂ) :
    residueJetLogTorsionTriangleProfile p b c d z 2 =
      -(residueJetPolynomial p b z - residueJetPolynomial p d z) := rfl

/-- Residue-jet logarithmic torsions obey the three-place reciprocity sum. -/
theorem residueJetLogTorsionTriangleProfile_sum_eq_zero
    (p : ℕ) (b c d : ℕ → ℂ) (z : ℂ) :
    (residueJetLogTorsionTriangleProfile p b c d z).sum (fun _ q => q) = 0 :=
  pairDescentTriangleProfile_sum_eq_zero (fun e => residueJetPolynomial p e z) b c d

/-- A nonzero residue-jet log torsion forces another nonzero comparison in its triangle. -/
theorem residueJetLogTorsion_nonzero_has_triangle_partner
    (p : ℕ) (b c d : ℕ → ℂ) (z : ℂ)
    (hbc : residueJetPolynomial p b z - residueJetPolynomial p c z ≠ 0) :
    residueJetPolynomial p c z - residueJetPolynomial p d z ≠ 0 ∨
      residueJetPolynomial p b z - residueJetPolynomial p d z ≠ 0 := by
  obtain ⟨j, hj0, hj⟩ := pairDescentTriangleProfile_exists_other_nonzero
    (fun e => residueJetPolynomial p e z) b c d (i := 0)
      (by simpa [pairDescentDefect] using hbc)
  fin_cases j
  · exact absurd rfl hj0
  · left
    simpa [pairDescentDefect] using hj
  · right
    have hj' :
        residueJetPolynomial p d z - residueJetPolynomial p b z ≠ 0 := by
      simpa [pairDescentDefect] using hj
    intro hzero
    apply hj'
    linear_combination -hzero

/-- A nonzero residue-jet log-torsion triangle occupies at least two channels. -/
theorem residueJetLogTorsionTriangleProfile_two_le_support_card
    (p : ℕ) (b c d : ℕ → ℂ) (z : ℂ)
    (hne : residueJetLogTorsionTriangleProfile p b c d z ≠ 0) :
    2 ≤ (residueJetLogTorsionTriangleProfile p b c d z).support.card :=
  pairDescentTriangleProfile_two_le_support_card
    (fun e => residueJetPolynomial p e z) b c d hne

/-- Residue-jet torsions obey the multiplicative three-place product formula. -/
theorem residueJetTorsion_triangle_product_eq_one
    (p : ℕ) (b c d : ℕ → ℂ) (z : ℂ) :
    residueJetTorsion p b c z * residueJetTorsion p c d z *
      (residueJetTorsion p b d z)⁻¹ = 1 := by
  rw [residueJetTorsion_cocycle]
  exact mul_inv_cancel₀ (residueJetTorsion_ne_zero p b d z)

/-- A nonunit residue-jet torsion forces another nonunit comparison in its triangle. -/
theorem residueJetTorsion_ne_one_has_triangle_partner
    (p : ℕ) (b c d : ℕ → ℂ) (z : ℂ)
    (hbc : residueJetTorsion p b c z ≠ 1) :
    residueJetTorsion p c d z ≠ 1 ∨ residueJetTorsion p b d z ≠ 1 := by
  by_contra h
  push Not at h
  have hcocycle := residueJetTorsion_cocycle p b c d z
  rw [h.1, h.2] at hcocycle
  apply hbc
  simpa using hcocycle

/-! ## Relative determinant logarithmic torsion -/

/-- Arguments of three relative determinant torsions before exponentiation. -/
def residueRelativeDeterminantLogTorsionTriangleProfile
    (a b c z : ℂ) : Fin 3 →₀ ℂ :=
  pairDescentTriangleProfile (fun q => -(q * z)) a b c

@[simp]
theorem residueRelativeDeterminantLogTorsionTriangleProfile_zero
    (a b c z : ℂ) :
    residueRelativeDeterminantLogTorsionTriangleProfile a b c z 0 = (b - a) * z := by
  simp [residueRelativeDeterminantLogTorsionTriangleProfile, pairDescentTriangleProfile,
    additiveCocycleTriangleProfile, pairDescentDefect]
  ring

@[simp]
theorem residueRelativeDeterminantLogTorsionTriangleProfile_one
    (a b c z : ℂ) :
    residueRelativeDeterminantLogTorsionTriangleProfile a b c z 1 = (c - b) * z := by
  simp [residueRelativeDeterminantLogTorsionTriangleProfile, pairDescentTriangleProfile,
    additiveCocycleTriangleProfile, pairDescentDefect]
  ring

@[simp]
theorem residueRelativeDeterminantLogTorsionTriangleProfile_two
    (a b c z : ℂ) :
    residueRelativeDeterminantLogTorsionTriangleProfile a b c z 2 = -((c - a) * z) := by
  simp [residueRelativeDeterminantLogTorsionTriangleProfile, pairDescentTriangleProfile,
    additiveCocycleTriangleProfile, pairDescentDefect]
  ring

/-- Relative determinant logarithmic torsions obey the three-place reciprocity sum. -/
theorem residueRelativeDeterminantLogTorsionTriangleProfile_sum_eq_zero
    (a b c z : ℂ) :
    (residueRelativeDeterminantLogTorsionTriangleProfile a b c z).sum (fun _ q => q) = 0 :=
  pairDescentTriangleProfile_sum_eq_zero (fun q => -(q * z)) a b c

/-- A nonzero relative determinant log-torsion triangle occupies at least two channels. -/
theorem residueRelativeDeterminantLogTorsionTriangleProfile_two_le_support_card
    (a b c z : ℂ)
    (hne : residueRelativeDeterminantLogTorsionTriangleProfile a b c z ≠ 0) :
    2 ≤ (residueRelativeDeterminantLogTorsionTriangleProfile a b c z).support.card :=
  pairDescentTriangleProfile_two_le_support_card (fun q => -(q * z)) a b c hne

/-- Relative determinant torsions obey the multiplicative three-place product formula. -/
theorem residueRelativeDeterminantTorsion_triangle_product_eq_one
    (a b c z : ℂ) :
    residueRelativeDeterminantTorsion a b z *
        residueRelativeDeterminantTorsion b c z *
      (residueRelativeDeterminantTorsion a c z)⁻¹ = 1 := by
  rw [residueRelativeDeterminantTorsion_cocycle]
  exact mul_inv_cancel₀ (residueRelativeDeterminantTorsion_ne_zero a c z)

/-- A nonunit relative determinant torsion forces another nonunit triangle comparison. -/
theorem residueRelativeDeterminantTorsion_ne_one_has_triangle_partner
    (a b c z : ℂ) (hab : residueRelativeDeterminantTorsion a b z ≠ 1) :
    residueRelativeDeterminantTorsion b c z ≠ 1 ∨
      residueRelativeDeterminantTorsion a c z ≠ 1 := by
  by_contra h
  push Not at h
  have hcocycle := residueRelativeDeterminantTorsion_cocycle a b c z
  rw [h.1, h.2] at hcocycle
  apply hab
  simpa using hcocycle

end


end RHTower
