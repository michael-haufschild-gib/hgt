import GaloisForLFunctions.RHTower.PMPowerDampedMobiusMean
import GaloisForLFunctions.RHTower.FermiNymanBeurlingHaarTarget
import GaloisForLFunctions.HTGeometry.PaperFourierLiteralConvergence

/-! # Literal Fourier profiles of the FZZ alternating approximation problem

The Haar target and the actual alternating Nyman generators are bounded measurable
functions. No smooth replacement of their infinitely many jumps is made.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology Set GaloisForLFunctions.HTGeometry
open scoped BigOperators

theorem paperFermiGenerator_memLp (a : ℝ) :
    MemLp (fermiNymanGen a) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  MemLp.of_bound (measurable_fermiNymanGen a).aestronglyMeasurable 1
    (Eventually.of_forall (pm_norm_fermiNymanGen_le_one a))

theorem paperFermiHaar_memLp :
    MemLp dyadicHaar 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  MemLp.of_bound measurable_dyadicHaar.aestronglyMeasurable 1
    (Eventually.of_forall (fun t => (norm_dyadicHaar t).le))

theorem paperFermiCombination_memLp {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    MemLp (fermiNymanCombination c a) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  MemLp.of_bound (measurable_fermiNymanCombination c a).aestronglyMeasurable
    (∑ j, ‖c j‖ * 3) (Eventually.of_forall (norm_fermiNymanCombination_le c a))

def paperFermiResidual {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (t : ℝ) : ℂ :=
  dyadicHaar t - fermiNymanCombination c a t

theorem paperFermiResidual_measurable {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    Measurable (paperFermiResidual c a) :=
  measurable_dyadicHaar.sub (measurable_fermiNymanCombination c a)

theorem paperFermiResidual_memLp {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    MemLp (paperFermiResidual c a) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  paperFermiHaar_memLp.sub (paperFermiCombination_memLp c a)

def paperFermiGeneratorCoeff (a : ℝ) (k : ℤ) : ℂ :=
  fourierCoeffOn zero_lt_one (fermiNymanGen a) k

def paperFermiHaarCoeff (k : ℤ) : ℂ := fourierCoeffOn zero_lt_one dyadicHaar k

def paperFermiResidualCoeff {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (k : ℤ) : ℂ :=
  fourierCoeffOn zero_lt_one (paperFermiResidual c a) k

/-- `none` retains the Haar target; every other index retains its literal source generator. -/
def paperFermiFourierFamily {κ : Type*} (a : κ → ℝ) : Option κ → ℝ → ℂ
  | none => dyadicHaar
  | some j => fermiNymanGen (a j)

theorem paperFermiFourierFamily_memLp {κ : Type*} (a : κ → ℝ) (j : Option κ) :
    MemLp (paperFermiFourierFamily a j) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  cases j with
  | none => exact paperFermiHaar_memLp
  | some j => exact paperFermiGenerator_memLp (a j)

end
end RHTower
