import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaVerticalClosure
import Mathlib.Tactic

/-!
# Parameter families selected by vertical closure

The integral function `Q` now constructs actual nonzero `q₀` units.  Classical closure parameters
have zero vertical drift but provably fail physical Region I.  On the extended branch, packaging the
paper's two strict Region II inequalities produces closed parameter data with zero drift and
strictly positive reconstructed speed and torsion squares.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Every classical modulus supplies a nonzero vertical-closure scale. -/
noncomputable def classicalClosureParameters (m : ClassicalModulus) : Parameters where
  modulus := m
  q₀ := Units.mk0 (closureQ m) (ne_of_gt (closureQ_classical_pos m))

@[simp] theorem classicalClosureParameters_modulus (m : ClassicalModulus) :
    (classicalClosureParameters m).modulus = (m : ℝ) := rfl

@[simp] theorem classicalClosureParameters_q₀ (m : ClassicalModulus) :
    ((classicalClosureParameters m).q₀ : ℝ) = closureQ m := rfl

theorem classicalClosureParameters_verticalDrift (m : ClassicalModulus) :
    verticalClosureDrift (classicalClosureParameters m) = 0 := by
  rw [verticalClosureDrift_eq_zero_iff]
  rfl

/-- Closure alone never turns a classical modulus into a physical Region I traveling knot. -/
theorem classicalClosureParameters_not_regionI (m : ClassicalModulus) :
    ¬ (0 < ((classicalClosureParameters m).q₀ : ℝ) ∧
      (classicalClosureParameters m).modulus <
        ((classicalClosureParameters m).q₀ : ℝ) ∧
      3 * ((classicalClosureParameters m).q₀ : ℝ) <
        1 + (classicalClosureParameters m).modulus) := by
  intro hregion
  let P : PhysicalRegionI := ⟨classicalClosureParameters m, hregion⟩
  exact physicalRegionI_verticalClosureDrift_ne_zero P
    (classicalClosureParameters_verticalDrift m)

/-- Negative moduli at which the closed-knot scale itself is negative and lies beyond speed wall. -/
structure ExtendedTravelingClosure where
  modulus : NegativeModulus
  closure_negative : closureQ modulus < 0
  speed_wall : 1 + (modulus : ℝ) < 3 * closureQ modulus

/-- Paper's extended closed-traveling parameter family, with nonzero scale encoded as a unit. -/
noncomputable def extendedTravelingClosureParameters (M : ExtendedTravelingClosure) : Parameters where
  modulus := M.modulus
  q₀ := Units.mk0 (closureQ M.modulus) (ne_of_lt M.closure_negative)

@[simp] theorem extendedTravelingClosureParameters_modulus (M : ExtendedTravelingClosure) :
    (extendedTravelingClosureParameters M).modulus = (M.modulus : ℝ) := rfl

@[simp] theorem extendedTravelingClosureParameters_q₀ (M : ExtendedTravelingClosure) :
    ((extendedTravelingClosureParameters M).q₀ : ℝ) = closureQ M.modulus := rfl

/-- Extended closure data inhabit paper Region II. -/
noncomputable def extendedTravelingClosureRegionII (M : ExtendedTravelingClosure) :
    PhysicalRegionII :=
  ⟨extendedTravelingClosureParameters M, ⟨M.closure_negative, M.speed_wall⟩⟩

theorem extendedTravelingClosure_verticalDrift (M : ExtendedTravelingClosure) :
    verticalClosureDrift (extendedTravelingClosureParameters M) = 0 := by
  rw [verticalClosureDrift_eq_zero_iff]
  rfl

theorem extendedTravelingClosure_gammaSq_pos (M : ExtendedTravelingClosure) :
    0 < gammaSq (extendedTravelingClosureParameters M) :=
  physicalRegionII_gammaSq_pos (extendedTravelingClosureRegionII M)

theorem extendedTravelingClosure_nuSq_pos (M : ExtendedTravelingClosure) :
    0 < nuSq (extendedTravelingClosureParameters M) :=
  physicalRegionII_nuSq_pos (extendedTravelingClosureRegionII M)

/-- Equation (92) on the constructed closure family. -/
theorem extendedTravelingClosure_nuSq (M : ExtendedTravelingClosure) :
    nuSq (extendedTravelingClosureParameters M) =
      (1 - closureQ M.modulus) *
        (closureQ M.modulus - (M.modulus : ℝ)) / closureQ M.modulus ^ 2 := by
  rfl

/-- Equation (93) on the constructed closure family. -/
theorem extendedTravelingClosure_gammaSq (M : ExtendedTravelingClosure) :
    gammaSq (extendedTravelingClosureParameters M) =
      (1 + (M.modulus : ℝ)) / closureQ M.modulus - 3 := by
  rfl

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
