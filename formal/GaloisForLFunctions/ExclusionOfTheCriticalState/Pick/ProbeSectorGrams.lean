import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeReflectionWalk
import GaloisForLFunctions.HTGeometry.PSDKernelOperations

/-!
# Positive Gram bounds for the actual Weil probe matrix

Split every zero-coordinate probe into its positive and negative reflection
components. Their ordinary Gram matrices are positive. Their sum is the
ordinary probe Gram matrix, and their difference is the actual Weil matrix.
Consequently both `G+K` and `G-K` are positive semidefinite, in the original
probe coordinates, without an independence assumption.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open scoped ComplexOrder

private def reflectionIsometry : ZeroSpace →ₗᵢ[ℂ] ZeroSpace where
  toLinearMap := zeroReflection.toLinearMap
  norm_map' := norm_zeroReflection

theorem zeroReflection_inner_map_map (x y : ZeroSpace) :
    inner ℂ (zeroReflection x) (zeroReflection y) = inner ℂ x y :=
  reflectionIsometry.inner_map_map x y

theorem zeroReflection_inner_left (x y : ZeroSpace) :
    inner ℂ (zeroReflection x) y = inner ℂ x (zeroReflection y) := by
  have h := zeroReflection_inner_map_map x (zeroReflection y)
  rwa [zeroReflection_involutive] at h

/-- The two actual eigensector components of a zero-coordinate vector. -/
def positivePart (x : ZeroSpace) : ZeroSpace := (1 / 2 : ℂ) • (x + zeroReflection x)
def negativePart (x : ZeroSpace) : ZeroSpace := (1 / 2 : ℂ) • (x - zeroReflection x)

theorem zeroReflection_positivePart (x : ZeroSpace) :
    zeroReflection (positivePart x) = positivePart x := by
  rw [positivePart, map_smul, map_add, zeroReflection_involutive]
  module

theorem zeroReflection_negativePart (x : ZeroSpace) :
    zeroReflection (negativePart x) = -negativePart x := by
  rw [negativePart, map_smul, map_sub, zeroReflection_involutive]
  module

theorem sector_inner_sum (x y : ZeroSpace) :
    inner ℂ (positivePart y) (positivePart x) +
      inner ℂ (negativePart y) (negativePart x) = inner ℂ y x := by
  simp only [positivePart, negativePart, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    map_div₀, map_one, map_ofNat, zeroReflection_inner_map_map]
  ring

theorem sector_inner_difference (x y : ZeroSpace) :
    inner ℂ (positivePart y) (positivePart x) -
      inner ℂ (negativePart y) (negativePart x) = inner ℂ (zeroReflection y) x := by
  simp only [positivePart, negativePart, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    map_div₀, map_one, map_ofNat, zeroReflection_inner_left]
  ring

/-- Ordinary positive Gram matrix of the actual zero-coordinate probes. -/
def hilbertProbeGram {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => inner ℂ (probeVec (p j).property) (probeVec (p i).property)

def positiveProbeGram {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => inner ℂ (positivePart (probeVec (p j).property))
    (positivePart (probeVec (p i).property))

def negativeProbeGram {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => inner ℂ (negativePart (probeVec (p j).property))
    (negativePart (probeVec (p i).property))

theorem positiveProbeGram_posSemidef {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    (positiveProbeGram p).PosSemidef :=
  (HTGeometry.isPSDKernel_gram (fun i : Fin N => positivePart (probeVec (p i).property))).posSemidef
    (fun i => i)

theorem negativeProbeGram_posSemidef {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    (negativeProbeGram p).PosSemidef :=
  (HTGeometry.isPSDKernel_gram (fun i : Fin N => negativePart (probeVec (p i).property))).posSemidef
    (fun i => i)

theorem hilbertProbeGram_eq_sector_sum {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    hilbertProbeGram p = positiveProbeGram p + negativeProbeGram p := by
  ext i j
  exact (sector_inner_sum (probeVec (p i).property) (probeVec (p j).property)).symm

/-- The indefinite arithmetic matrix is exactly the difference of two positive sector Grams. -/
theorem probeGram_eq_sector_difference {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    probeGram (fun i => (p i).val) = positiveProbeGram p - negativeProbeGram p := by
  ext i j
  rw [probeGram, bareMixedEnergy_probe_eq_inner (p i).property (p j).property]
  exact (sector_inner_difference (probeVec (p i).property) (probeVec (p j).property)).symm

/-- The ordinary Gram form bounds the Weil form below on every coefficient vector. -/
theorem hilbertProbeGram_add_probeGram_posSemidef {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    (hilbertProbeGram p + probeGram (fun i => (p i).val)).PosSemidef := by
  have h := (positiveProbeGram_posSemidef p).add (positiveProbeGram_posSemidef p)
  convert h using 1
  rw [hilbertProbeGram_eq_sector_sum, probeGram_eq_sector_difference]
  abel

/-- The ordinary Gram form bounds the Weil form above on every coefficient vector. -/
theorem hilbertProbeGram_sub_probeGram_posSemidef {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) :
    (hilbertProbeGram p - probeGram (fun i => (p i).val)).PosSemidef := by
  have h := (negativeProbeGram_posSemidef p).add (negativeProbeGram_posSemidef p)
  convert h using 1
  rw [hilbertProbeGram_eq_sector_sum, probeGram_eq_sector_difference]
  abel

#print axioms probeGram_eq_sector_difference
#print axioms hilbertProbeGram_add_probeGram_posSemidef
#print axioms hilbertProbeGram_sub_probeGram_posSemidef

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
