import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.Tactic

/-!
# Traveling-wave parameter classification for Brizard's elastica NLS

Section VII of arXiv:2607.21750 introduces `μ = 2 + γ²` and
`q₀ = (1+m)/(1+μ)`, obtaining the factored torsion parameter
`ν² = (μ-m)(1-mμ)/(1+m)²`.  This module packages the exceptional value `m = -1` into the
parameter type, verifies both reconstructions exactly, and classifies every real sign branch.

The unrestricted algebra has two nonnegative branches, `m ≤ 1/μ` and `μ ≤ m`; the paper uses
only the first because of its geometric modulus range.  Moreover `1/μ ≤ 1/2`, with equality
exactly for the stationary endpoint `γ = 0`.  Thus the paper's displayed strict inequality is
strict only away from that endpoint.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Moduli on which the paper's traveling scale `q₀` is nonzero. -/
abbrev TravelingModulus := {m : ℝ // m ≠ -1}

/-- Paper parameter `μ = 2 + γ²`. -/
noncomputable def travelingMu (γ : ℝ) : ℝ := 2 + γ ^ 2

theorem travelingMu_ge_two (γ : ℝ) : 2 ≤ travelingMu γ := by
  rw [travelingMu]
  nlinarith [sq_nonneg γ]

theorem travelingMu_pos (γ : ℝ) : 0 < travelingMu γ :=
  lt_of_lt_of_le (by norm_num) (travelingMu_ge_two γ)

theorem three_add_gamma_sq_pos (γ : ℝ) : 0 < 3 + γ ^ 2 := by positivity

/-- Equation (1037), packaged as a nonzero real scale. -/
noncomputable def travelingQ₀ (m : TravelingModulus) (γ : ℝ) : ℝˣ :=
  Units.mk0 ((1 + (m : ℝ)) / (3 + γ ^ 2)) (by
    apply div_ne_zero
    · intro h
      apply m.property
      linarith
    · exact ne_of_gt (three_add_gamma_sq_pos γ))

noncomputable def travelingParameters (m : TravelingModulus) (γ : ℝ) : Parameters where
  modulus := m
  q₀ := travelingQ₀ m γ

@[simp] theorem travelingParameters_modulus (m : TravelingModulus) (γ : ℝ) :
    (travelingParameters m γ).modulus = (m : ℝ) := rfl

@[simp] theorem travelingParameters_q₀ (m : TravelingModulus) (γ : ℝ) :
    ((travelingParameters m γ).q₀ : ℝ) =
      (1 + (m : ℝ)) / (3 + γ ^ 2) := rfl

/-- The two denominators in equation (1037) are identical. -/
theorem traveling_q₀_eq_mu (m : TravelingModulus) (γ : ℝ) :
    ((travelingParameters m γ).q₀ : ℝ) =
      (1 + (m : ℝ)) / (1 + travelingMu γ) := by
  rw [travelingParameters_q₀, travelingMu]
  congr 1
  ring

/-- Equation (1037) exactly reconstructs the selected squared wave speed. -/
theorem traveling_gammaSq (m : TravelingModulus) (γ : ℝ) :
    gammaSq (travelingParameters m γ) = γ ^ 2 := by
  rw [gammaSq]
  simp only [travelingParameters_modulus, travelingParameters_q₀]
  have hm : 1 + (m : ℝ) ≠ 0 := by
    intro h
    apply m.property
    linarith
  have hγ : 3 + γ ^ 2 ≠ 0 := ne_of_gt (three_add_gamma_sq_pos γ)
  field_simp [hm, hγ]
  ring

/-- Equation (1041), obtained from the paper's original `ν²(m,q₀)` formula. -/
theorem traveling_nuSq (m : TravelingModulus) (γ : ℝ) :
    nuSq (travelingParameters m γ) =
      (travelingMu γ - (m : ℝ)) * (1 - (m : ℝ) * travelingMu γ) /
        (1 + (m : ℝ)) ^ 2 := by
  rw [nuSq]
  simp only [travelingParameters_modulus, travelingParameters_q₀]
  have hm : 1 + (m : ℝ) ≠ 0 := by
    intro h
    apply m.property
    linarith
  have hγ : 3 + γ ^ 2 ≠ 0 := ne_of_gt (three_add_gamma_sq_pos γ)
  rw [travelingMu]
  field_simp [hm, hγ]
  ring

/-- Correct closed endpoint form of the bound following equation (1041). -/
theorem one_div_travelingMu_le_half (γ : ℝ) :
    1 / travelingMu γ ≤ 1 / 2 := by
  rw [div_le_div_iff₀ (travelingMu_pos γ) (by norm_num : (0 : ℝ) < 2)]
  nlinarith [travelingMu_ge_two γ]

/-- Equality occurs precisely at the paper's stationary lemniscatic endpoint. -/
theorem one_div_travelingMu_eq_half_iff (γ : ℝ) :
    1 / travelingMu γ = 1 / 2 ↔ γ = 0 := by
  have hμ := travelingMu_pos γ
  constructor
  · intro h
    rw [div_eq_div_iff (ne_of_gt hμ) (by norm_num : (2 : ℝ) ≠ 0)] at h
    rw [travelingMu] at h
    nlinarith [sq_nonneg γ]
  · rintro rfl
    norm_num [travelingMu]

/-- Complete algebraic sign classification; paper's geometric range keeps only the first branch. -/
theorem traveling_nuSq_nonneg_iff (m : TravelingModulus) (γ : ℝ) :
    0 ≤ nuSq (travelingParameters m γ) ↔
      (m : ℝ) ≤ 1 / travelingMu γ ∨ travelingMu γ ≤ (m : ℝ) := by
  rw [traveling_nuSq]
  have hm : 1 + (m : ℝ) ≠ 0 := by
    intro h
    apply m.property
    linarith
  have hden : 0 < (1 + (m : ℝ)) ^ 2 := sq_pos_of_ne_zero hm
  have hμ : 0 < travelingMu γ := travelingMu_pos γ
  have hrecip : 1 / travelingMu γ ≤ travelingMu γ := by
    rw [div_le_iff₀ hμ]
    nlinarith [travelingMu_ge_two γ]
  constructor
  · intro h
    have hprod : 0 ≤
        (travelingMu γ - (m : ℝ)) * (1 - (m : ℝ) * travelingMu γ) := by
      rcases div_nonneg_iff.mp h with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_le_of_gt hden) hneg.2)
    rcases mul_nonneg_iff.mp hprod with hpos | hneg
    · left
      rw [le_div_iff₀ hμ]
      linarith [hpos.2]
    · right
      linarith [hneg.1]
  · rintro (hleft | hright)
    · apply div_nonneg
      · apply mul_nonneg
        · linarith
        · rw [le_div_iff₀ hμ] at hleft
          linarith [hleft]
      · exact le_of_lt hden
    · apply div_nonneg
      · apply mul_nonneg_of_nonpos_of_nonpos
        · exact sub_nonpos.mpr hright
        · have hrecip_m : 1 / travelingMu γ ≤ (m : ℝ) :=
            le_trans hrecip hright
          rw [div_le_iff₀ hμ] at hrecip_m
          linarith
      · exact le_of_lt hden

/-- The two torsionless walls in the unrestricted traveling-wave parameterization. -/
theorem traveling_nuSq_eq_zero_iff (m : TravelingModulus) (γ : ℝ) :
    nuSq (travelingParameters m γ) = 0 ↔
      (m : ℝ) = travelingMu γ ∨ (m : ℝ) = 1 / travelingMu γ := by
  rw [traveling_nuSq, div_eq_zero_iff]
  have hm : (1 + (m : ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by
    intro h
    apply m.property
    linarith)
  simp only [hm, or_false]
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · left
      linarith
    · right
      rw [eq_div_iff (ne_of_gt (travelingMu_pos γ))]
      linarith
  · rintro (h | h)
    · left
      linarith
    · right
      rw [eq_div_iff (ne_of_gt (travelingMu_pos γ))] at h
      linarith

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
