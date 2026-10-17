import GaloisForLFunctions.BiScaleUncertainty.CollarMeshBounds
import GaloisForLFunctions.BiScaleUncertainty.CollarRadialPenalty

/-!
# Radial comparison for full signed logarithmic arrays

Padding and coordinatewise restriction preserve the odd-coset geometry.
Perturbation mass controls radial growth after the reciprocal origin singularity
has been absorbed by the physical offset.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

def logarithmicArrayBlockNorm (n : ℕ) (a : Bool → ℕ → ℝ) : ℝ :=
  blockWeightNorm (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => a j.2 k)

theorem logarithmicArrayBlockNorm_nonneg (n : ℕ) (a : Bool → ℕ → ℝ) :
    0 ≤ logarithmicArrayBlockNorm n a := blockWeightNorm_nonneg _ _ _

theorem logarithmicArrayMass_nonneg (n : ℕ) (a : Bool → ℕ → ℝ)
    (ha : ∀ σ k, 0 ≤ a σ k) : 0 ≤ logarithmicArrayMass n a :=
  Finset.sum_nonneg (fun k _ => add_nonneg (ha false k) (ha true k))

theorem logarithmicArrayBlockNorm_le_mass (n : ℕ) (a : Bool → ℕ → ℝ)
    (ha : ∀ σ k, 0 ≤ a σ k) :
    logarithmicArrayBlockNorm n a ≤ logarithmicArrayMass n a := by
  rw [logarithmicArrayMass, ← sum_logarithmicSignedCosets n a]
  apply Finset.sum_le_sum
  intro j _
  apply Real.sqrt_le_iff.mpr
  exact ⟨Finset.sum_nonneg (fun k _ => ha j.2 k),
    Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => ha j.2 k)⟩

theorem logarithmicArrayBlockNorm_pad {n m : ℕ} (hm : n ≤ m) (a : Bool → ℕ → ℝ) :
    logarithmicArrayBlockNorm m (collarArrayPad n a) = logarithmicArrayBlockNorm n a :=
  blockWeightNorm_collarArrayPad hm a

theorem logarithmicArrayBlockNorm_mono (n : ℕ) (a b : Bool → ℕ → ℝ)
    (ha : ∀ σ k, 0 ≤ a σ k) (hab : ∀ σ k, a σ k ≤ b σ k) :
    logarithmicArrayBlockNorm n a ≤ logarithmicArrayBlockNorm n b :=
  blockWeightNorm_mono _ _ _ _ (fun j _ k _ => ha j.2 k) (fun j _ k _ => hab j.2 k)

theorem logarithmicArrayBlockNorm_le_add_mass (n : ℕ) (a b e : Bool → ℕ → ℝ)
    (hb : ∀ σ k, 0 ≤ b σ k) (he : ∀ σ k, 0 ≤ e σ k)
    (hab : ∀ σ k, b σ k ≤ a σ k + e σ k) :
    logarithmicArrayBlockNorm n b ≤ logarithmicArrayBlockNorm n a + logarithmicArrayMass n e := by
  have h := blockWeightNorm_le_add_mass (logarithmicSignedCosets n)
    (fun j => logarithmicCosetNodes n j.1)
    (fun j k => a j.2 k) (fun j k => b j.2 k) (fun j k => e j.2 k)
    (fun j _ k _ => hb j.2 k) (fun j _ k _ => he j.2 k) (fun j _ k _ => hab j.2 k)
  rw [sum_logarithmicSignedCosets n e] at h
  exact h

theorem collarRadialPenalty_increment_offset {W A B G y : ℝ} (hW : 0 < W)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hBG : B ≤ A + G)
    (hy : 0 ≤ y) (hY : 1 ≤ 2 * y * W) :
    collarRadialPenalty W B - collarRadialPenalty W A ≤ y * (2 * A * G + G ^ 2) := by
  let Q := collarRadialPenalty W B - collarRadialPenalty W A
  have hinc := collarRadialPenalty_increment hW hA hB hG hBG
  by_cases hQ : 0 ≤ Q
  · calc
      Q = 1 * Q := by ring
      _ ≤ (2 * y * W) * Q := mul_le_mul_of_nonneg_right hY hQ
      _ = y * (2 * W * Q) := by ring
      _ ≤ y * (2 * A * G + G ^ 2) := mul_le_mul_of_nonneg_left hinc hy
  · exact (le_of_not_ge hQ).trans (by positivity)

/-- Offset-scaled mass bounds give a uniform radial increment. -/
theorem collarRadialPenalty_increment_scaled {W A B G y a g : ℝ} (hW : 0 < W)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hBG : B ≤ A + G)
    (hy : 0 ≤ y) (hY : 1 ≤ 2 * y * W) (ha : 0 ≤ a) (hg : 0 ≤ g)
    (hAy : A * Real.sqrt y ≤ a) (hGy : G * Real.sqrt y ≤ g) :
    collarRadialPenalty W B - collarRadialPenalty W A ≤ 2 * a * g + g ^ 2 := by
  have h := collarRadialPenalty_increment_offset hW hA hB hG hBG hy hY
  have hprod := mul_le_mul hAy hGy (mul_nonneg hG (Real.sqrt_nonneg y)) ha
  have hsq := mul_le_mul hGy hGy (mul_nonneg hG (Real.sqrt_nonneg y)) hg
  have heq : y * (2 * A * G + G ^ 2) =
      2 * (A * Real.sqrt y) * (G * Real.sqrt y) + (G * Real.sqrt y) ^ 2 := by
    calc
      _ = (Real.sqrt y) ^ 2 * (2 * A * G + G ^ 2) := by rw [Real.sq_sqrt hy]
      _ = _ := by ring
  rw [heq] at h
  nlinarith

end
end GaloisForLFunctions.BiScaleUncertainty
