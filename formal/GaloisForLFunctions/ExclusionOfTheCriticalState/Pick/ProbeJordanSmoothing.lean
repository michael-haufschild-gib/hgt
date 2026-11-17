import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSectorGrams
import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyJordanInverse

/-!
# Reversible Cauchy smoothing of the actual Weil probe matrix

The positive and negative sector Grams admit positive Cauchy smoothing.
Their difference smooths the actual indefinite Weil matrix. Jordan
multiplication recovers that matrix exactly, while the smoothed Hilbert
Gram still bounds it on both sides. No positivity assertion about the
unsmoothed Weil matrix is needed.
-/

noncomputable section
open Matrix
open scoped ComplexOrder
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open HilbertMetric.CauchyJordan

/-- Cauchy-smoothed actual Weil matrix, with independently chosen positive rates. -/
def smoothedProbeGram {n : ℕ} (r : Fin n → ℝ) (p : Fin n → {x : ℝ // 1 ≤ x}) :
    Matrix (Fin n) (Fin n) ℂ := inverseJordan r (probeGram (fun i => (p i).val))

/-- Jordan multiplication recovers the full arithmetic matrix from its smoothed image. -/
theorem smoothedProbeGram_recovery {n : ℕ} (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    jordan r (smoothedProbeGram r p) = probeGram (fun i => (p i).val) :=
  jordan_inverseJordan r _

/-- Smoothing preserves the positive reflection-sector Gram. -/
theorem smoothed_positiveProbeGram_posSemidef {n : ℕ} (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    (inverseJordan r (positiveProbeGram p)).PosSemidef := by
  rw [inverseJordan_eq_hadamard]
  exact ((positiveProbeGram_posSemidef p).hadamard (cauchySymbol_posSemidef r)).smul
    (by norm_num : 0 ≤ (2 : ℂ))

/-- Smoothing preserves the negative-sector Gram as an ordinary positive matrix. -/
theorem smoothed_negativeProbeGram_posSemidef {n : ℕ} (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    (inverseJordan r (negativeProbeGram p)).PosSemidef := by
  rw [inverseJordan_eq_hadamard]
  exact ((negativeProbeGram_posSemidef p).hadamard (cauchySymbol_posSemidef r)).smul
    (by norm_num : 0 ≤ (2 : ℂ))

/-- The signed-sector decomposition survives the reversible smoothing. -/
theorem smoothedProbeGram_sector_difference {n : ℕ} (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    smoothedProbeGram r p =
      inverseJordan r (positiveProbeGram p) - inverseJordan r (negativeProbeGram p) := by
  rw [smoothedProbeGram, probeGram_eq_sector_difference, inverseJordan_sub]

/-- Both Hilbert bounds survive in the smoothed coordinates. -/
theorem smoothedProbeGram_hilbert_sandwich {n : ℕ} (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    (inverseJordan r (hilbertProbeGram p) + smoothedProbeGram r p).PosSemidef ∧
      (inverseJordan r (hilbertProbeGram p) - smoothedProbeGram r p).PosSemidef := by
  have hadd (A B : Matrix (Fin n) (Fin n) ℂ) :
      inverseJordan r (A + B) = inverseJordan r A + inverseJordan r B := by
    simpa only [one_smul] using inverseJordan_add_smul r A B 1
  constructor
  · rw [smoothedProbeGram, ← hadd, inverseJordan_eq_hadamard]
    exact ((hilbertProbeGram_add_probeGram_posSemidef p).hadamard
      (cauchySymbol_posSemidef r)).smul (by norm_num : 0 ≤ (2 : ℂ))
  · rw [smoothedProbeGram, ← inverseJordan_sub, inverseJordan_eq_hadamard]
    exact ((hilbertProbeGram_sub_probeGram_posSemidef p).hadamard
      (cauchySymbol_posSemidef r)).smul (by norm_num : 0 ≤ (2 : ℂ))

#print axioms smoothedProbeGram_recovery
#print axioms smoothedProbeGram_sector_difference
#print axioms smoothedProbeGram_hilbert_sandwich

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
