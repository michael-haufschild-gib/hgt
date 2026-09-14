import GaloisForLFunctions.HTGeometry.NavierStokesOrderedBumpMoments
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Navier-Stokes five-bump moment solve

This file formalizes the finite-dimensional solve in Lemma 8.7 of the supplied Navier-Stokes
paper.  The five constraints split into an azimuthal block with powers
`(-2 - 2 * decay, -2 * decay, 2)` and an axial block with powers
`(1 - 2 * decay, 1)`.  For positive `decay`, both lists are strictly ordered after this harmless
row ordering.  Lemma A.1, already formalized in `NavierStokesOrderedBumpMoments`, therefore
makes both moment blocks invertible.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesFiveBumpMomentSolve

noncomputable section

open NavierStokesOrderedBumpMoments

/-- Data for nonnegative nonzero bumps on strictly ordered positive intervals. -/
structure OrderedBumpFamily (n : ℕ) where
  lower : Fin n → ℝ
  upper : Fin n → ℝ
  bump : Fin n → ℝ → ℝ
  lower_pos : ∀ j, 0 < lower j
  lower_lt_upper : ∀ j, lower j < upper j
  separated : ∀ {i j}, i < j → upper i < lower j
  continuous_bump : ∀ j, Continuous (bump j)
  bump_nonneg : ∀ j x, 0 ≤ bump j x
  bump_ne_zero : ∀ j, bump j ≠ 0
  support_bump : ∀ j,
    Function.support (bump j) ⊆ Set.Ioc (lower j) (upper j)

namespace OrderedBumpFamily

/-- Real-power moment matrix carried by an ordered bump family. -/
def momentMatrix {n : ℕ} (family : OrderedBumpFamily n) (α : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  realPowerMomentMatrix α family.bump

/-- Every strictly ordered exponent list gives an invertible moment matrix. -/
theorem isUnit_momentMatrix {n : ℕ} (family : OrderedBumpFamily n)
    (α : Fin n → ℝ) (hα : StrictMono α) : IsUnit (family.momentMatrix α) := by
  exact isUnit_realPowerMomentMatrix α family.lower family.upper family.bump hα
    family.lower_pos family.lower_lt_upper family.separated family.continuous_bump
    family.bump_nonneg family.bump_ne_zero family.support_bump

/-- Every target moment vector has unique bump coefficients. -/
theorem existsUnique_coefficients {n : ℕ} (family : OrderedBumpFamily n)
    (α : Fin n → ℝ) (hα : StrictMono α) (target : Fin n → ℝ) :
    ∃! c : Fin n → ℝ, (family.momentMatrix α).mulVec c = target := by
  have hunit := family.isUnit_momentMatrix α hα
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit target
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact Matrix.mulVec_injective_of_isUnit hunit (hd.trans hc.symm)

end OrderedBumpFamily

/-- Ordered version of the three azimuthal powers in Lemma 8.7. -/
def azimuthalMomentExponents (decay : ℝ) : Fin 3 → ℝ :=
  ![-2 - 2 * decay, -2 * decay, 2]

/-- Ordered version of the two axial powers in Lemma 8.7. -/
def axialMomentExponents (decay : ℝ) : Fin 2 → ℝ :=
  ![1 - 2 * decay, 1]

theorem strictMono_azimuthalMomentExponents {decay : ℝ} (hdecay : 0 < decay) :
    StrictMono (azimuthalMomentExponents decay) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> simp [azimuthalMomentExponents] <;> linarith

theorem strictMono_axialMomentExponents {decay : ℝ} (hdecay : 0 < decay) :
    StrictMono (axialMomentExponents decay) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  simp [axialMomentExponents]
  linarith

/-- **Lemma 8.7, five-bump linear solve.** Every three-component azimuthal target and
two-component axial target have a unique pair of bump-coefficient vectors. -/
theorem existsUnique_fiveBumpMomentCoefficients {decay : ℝ} (hdecay : 0 < decay)
    (azimuthal : OrderedBumpFamily 3) (axial : OrderedBumpFamily 2)
    (targetAzimuthal : Fin 3 → ℝ) (targetAxial : Fin 2 → ℝ) :
    ∃! c : (Fin 3 → ℝ) × (Fin 2 → ℝ),
      (azimuthal.momentMatrix (azimuthalMomentExponents decay)).mulVec c.1 =
          targetAzimuthal ∧
        (axial.momentMatrix (axialMomentExponents decay)).mulVec c.2 = targetAxial := by
  obtain ⟨ca, hca, hcaUnique⟩ := azimuthal.existsUnique_coefficients
    (azimuthalMomentExponents decay) (strictMono_azimuthalMomentExponents hdecay)
      targetAzimuthal
  obtain ⟨cz, hcz, hczUnique⟩ := axial.existsUnique_coefficients
    (axialMomentExponents decay) (strictMono_axialMomentExponents hdecay) targetAxial
  refine ⟨(ca, cz), ⟨hca, hcz⟩, ?_⟩
  rintro ⟨da, dz⟩ ⟨hda, hdz⟩
  rw [hcaUnique da hda, hczUnique dz hdz]

end

end GaloisForLFunctions.HTGeometry.NavierStokesFiveBumpMomentSolve
