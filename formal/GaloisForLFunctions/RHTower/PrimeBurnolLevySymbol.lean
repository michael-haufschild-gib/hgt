import GaloisForLFunctions.HTGeometry.LevyFiniteJumpMeasure
import GaloisForLFunctions.RHTower.PrimeBurnolAccretiveEvolution
import GaloisForLFunctions.RHTower.PrimeBurnolJumpEvolution

/-! Positive Lévy data on the literal Burnol carrier, with unrestricted jump activity. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ComplexOrder
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

/-- The control measure is finite; the corresponding jump measure need not be finite. -/
structure BurnolLevyData where
  control : Measure ℝ≥0
  finite : IsFiniteMeasure control
  zero_atom : control {0} = 0
  killing : ℝ≥0
  drift : ℝ≥0

attribute [instance] BurnolLevyData.finite

namespace BurnolLevyData
variable (D : BurnolLevyData)

def exponent (z : ℂ) : ℂ :=
  ((D.killing : ℝ) : ℂ) + ((D.drift : ℝ) : ℂ) * z + levyLaplaceJump D.control z

def symbol : BurnolAccretiveSymbol where
  toFun := D.exponent
  analytic := by
    intro z hz
    exact (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).add
      (analyticOnNhd_levyLaplaceJump D.control z hz)
  nonneg := by
    intro z hz
    simp only [exponent, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact add_nonneg (add_nonneg D.killing.coe_nonneg
      (mul_nonneg D.drift.coe_nonneg (le_of_lt hz)))
      (levyLaplaceJump_re_nonneg D.control (le_of_lt hz))

@[simp] theorem symbol_apply (z : ℂ) : D.symbol z = D.exponent z := rfl

def withoutDrift : BurnolLevyData := { D with drift := 0 }

@[simp] theorem withoutDrift_exponent (z : ℂ) :
    D.withoutDrift.exponent z = ((D.killing : ℝ) : ℂ) + levyLaplaceJump D.control z := by
  simp [exponent, withoutDrift]

def tailSymbol (n : ℕ) : BurnolAccretiveSymbol where
  toFun := levyLaplaceJump (levySmallControl D.control n)
  analytic := analyticOnNhd_levyLaplaceJump _
  nonneg := fun _ hz => levyLaplaceJump_re_nonneg _ (le_of_lt hz)

@[simp] theorem tailSymbol_apply (n : ℕ) (z : ℂ) :
    D.tailSymbol n z = levyLaplaceJump (levySmallControl D.control n) z := rfl

def finiteJumpData (n : ℕ) : BurnolJumpData where
  measure := levyFiniteJumpMeasure D.control n
  finite := inferInstance
  zero_atom := levyFiniteJumpMeasure_zero_atom D.control D.zero_atom n
  killing := D.killing

def evolution (t : ℝ≥0) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 := D.symbol.evolution t

theorem evolution_prime (t : ℝ≥0) (p : Nat.Primes) :
    D.evolution t (primeLogCriticalLaplaceFeatureL2 p) =
      Complex.exp (-((t : ℝ) : ℂ) * D.exponent (Real.log (p : ℝ))) •
        primeLogCriticalLaplaceFeatureL2 p := D.symbol.evolution_prime t p

theorem norm_evolution_le (t : ℝ≥0) : ‖D.evolution t‖ ≤ 1 := D.symbol.norm_evolution_le t

theorem continuous_evolution (f : BurnolHalfLineL2) :
    Continuous (fun t : ℝ≥0 => D.evolution t f) := D.symbol.continuous_evolution f

theorem evolution_zero : D.evolution 0 = 1 := D.symbol.evolution_zero

theorem evolution_add (s t : ℝ≥0) :
    D.evolution (s + t) = D.evolution s * D.evolution t := D.symbol.evolution_add s t

end BurnolLevyData
end RHTower
