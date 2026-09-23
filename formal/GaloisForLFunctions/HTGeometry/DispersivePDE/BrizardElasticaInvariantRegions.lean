import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaInvariantSigns
import Mathlib.Tactic

/-!
# Exact sign regions for Brizard's third invariant

The paper describes signs of `g₃` across its two elastica-knot parameter regions.  Factoring the
weight-six invariant reduces the entire classification to the signs of `q₀` and
`(2m-1)(m+1)(m-2)`.  This module proves the global positive/negative criteria and then certifies
strict positivity throughout both paper regions, without relying on plotted or decimal boundaries.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

def g₃SignFactor (m : ℝ) : ℝ := (2 * m - 1) * (m + 1) * (m - 2)

theorem g₃_factor' (P : Parameters) :
    g₃ P = 4 * g₃SignFactor P.modulus / (27 * (P.q₀ : ℝ) ^ (3 : ℕ)) := by
  rw [g₃_factor, g₃SignFactor]
  ring

/-- Global strict-positive classification, including either sign of the scale. -/
theorem g₃_pos_iff (P : Parameters) :
    0 < g₃ P ↔
      (0 < g₃SignFactor P.modulus ∧ 0 < (P.q₀ : ℝ)) ∨
      (g₃SignFactor P.modulus < 0 ∧ (P.q₀ : ℝ) < 0) := by
  rw [g₃_factor', div_pos_iff]
  have hnumpos : 0 < 4 * g₃SignFactor P.modulus ↔ 0 < g₃SignFactor P.modulus := by
    constructor <;> intro h <;> nlinarith
  have hnumneg : 4 * g₃SignFactor P.modulus < 0 ↔ g₃SignFactor P.modulus < 0 := by
    constructor <;> intro h <;> nlinarith
  have hpowpos : 0 < (P.q₀ : ℝ) ^ (3 : ℕ) ↔ 0 < (P.q₀ : ℝ) :=
    (show Odd 3 by decide).pow_pos_iff
  have hpowneg : (P.q₀ : ℝ) ^ (3 : ℕ) < 0 ↔ (P.q₀ : ℝ) < 0 :=
    (show Odd 3 by decide).pow_neg_iff
  have hdenpos : 0 < 27 * (P.q₀ : ℝ) ^ (3 : ℕ) ↔ 0 < (P.q₀ : ℝ) := by
    rw [mul_pos_iff]
    simp [hpowpos]
  have hdenneg : 27 * (P.q₀ : ℝ) ^ (3 : ℕ) < 0 ↔ (P.q₀ : ℝ) < 0 := by
    rw [mul_neg_iff]
    simp [hpowneg]
  rw [hnumpos, hnumneg, hdenpos, hdenneg]

/-- Global strict-negative classification, including either sign of the scale. -/
theorem g₃_neg_iff (P : Parameters) :
    g₃ P < 0 ↔
      (0 < g₃SignFactor P.modulus ∧ (P.q₀ : ℝ) < 0) ∨
      (g₃SignFactor P.modulus < 0 ∧ 0 < (P.q₀ : ℝ)) := by
  rw [g₃_factor', div_neg_iff]
  have hnumpos : 0 < 4 * g₃SignFactor P.modulus ↔ 0 < g₃SignFactor P.modulus := by
    constructor <;> intro h <;> nlinarith
  have hnumneg : 4 * g₃SignFactor P.modulus < 0 ↔ g₃SignFactor P.modulus < 0 := by
    constructor <;> intro h <;> nlinarith
  have hpowpos : 0 < (P.q₀ : ℝ) ^ (3 : ℕ) ↔ 0 < (P.q₀ : ℝ) :=
    (show Odd 3 by decide).pow_pos_iff
  have hpowneg : (P.q₀ : ℝ) ^ (3 : ℕ) < 0 ↔ (P.q₀ : ℝ) < 0 :=
    (show Odd 3 by decide).pow_neg_iff
  have hdenpos : 0 < 27 * (P.q₀ : ℝ) ^ (3 : ℕ) ↔ 0 < (P.q₀ : ℝ) := by
    rw [mul_pos_iff]
    simp [hpowpos]
  have hdenneg : 27 * (P.q₀ : ℝ) ^ (3 : ℕ) < 0 ↔ (P.q₀ : ℝ) < 0 := by
    rw [mul_neg_iff]
    simp [hpowneg]
  rw [hnumpos, hnumneg, hdenpos, hdenneg]

/-- Paper region I: positive scale and `-1 < m < 1/2`. -/
abbrev RegionIParameters :=
  {P : Parameters // -1 < P.modulus ∧ P.modulus < 1 / 2 ∧ 0 < (P.q₀ : ℝ)}

/-- Paper region II: negative scale and `m < -1`. -/
abbrev RegionIIParameters :=
  {P : Parameters // P.modulus < -1 ∧ (P.q₀ : ℝ) < 0}

theorem regionI_g₃_pos (P : RegionIParameters) : 0 < g₃ P := by
  rw [g₃_pos_iff]
  left
  constructor
  · rw [g₃SignFactor]
    have h1 : 2 * P.val.modulus - 1 < 0 := by linarith [P.property.2.1]
    have h2 : 0 < P.val.modulus + 1 := by linarith [P.property.1]
    have h3 : P.val.modulus - 2 < 0 := by linarith [P.property.2.1]
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos h1 h2) h3
  · exact P.property.2.2

theorem regionII_g₃_pos (P : RegionIIParameters) : 0 < g₃ P := by
  rw [g₃_pos_iff]
  right
  constructor
  · rw [g₃SignFactor]
    have h1 : 2 * P.val.modulus - 1 < 0 := by linarith [P.property.1]
    have h2 : P.val.modulus + 1 < 0 := by linarith [P.property.1]
    have h3 : P.val.modulus - 2 < 0 := by linarith [P.property.1]
    exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg h1 h2) h3
  · exact P.property.2

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
