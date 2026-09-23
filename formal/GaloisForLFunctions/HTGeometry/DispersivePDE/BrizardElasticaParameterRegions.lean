import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.Tactic

/-!
# Exact elastica-NLS parameter regions

Equations (64)--(66) of arXiv:2607.21750 define the reconstructed squared speed `γ²` and torsion
`ν²`.  This module gives their complete strict-sign classifications for arbitrary nonzero `q₀`.
It then packages the two physical chambers bounded by the paper's three walls and derives the
displayed triangular bounds, with strict positivity of both reconstructed quantities.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Complete sign classification of the reconstructed squared wave speed. -/
theorem gammaSq_pos_iff (P : Parameters) :
    0 < gammaSq P ↔
      (0 < (P.q₀ : ℝ) ∧ 3 * (P.q₀ : ℝ) < 1 + P.modulus) ∨
      ((P.q₀ : ℝ) < 0 ∧ 1 + P.modulus < 3 * (P.q₀ : ℝ)) := by
  rw [gammaSq, div_sub' P.q₀.ne_zero, div_pos_iff]
  constructor
  · rintro (h | h)
    · left
      constructor <;> linarith [h.1, h.2]
    · right
      constructor <;> linarith [h.1, h.2]
  · rintro (h | h)
    · left
      constructor <;> linarith [h.1, h.2]
    · right
      constructor <;> linarith [h.1, h.2]

/-- Complete sign classification of the reconstructed squared torsion. -/
theorem nuSq_pos_iff (P : Parameters) :
    0 < nuSq P ↔
      (P.modulus < (P.q₀ : ℝ) ∧ (P.q₀ : ℝ) < 1) ∨
      (1 < (P.q₀ : ℝ) ∧ (P.q₀ : ℝ) < P.modulus) := by
  rw [nuSq, div_pos_iff]
  have hden : 0 < (P.q₀ : ℝ) ^ (2 : ℕ) := sq_pos_of_ne_zero P.q₀.ne_zero
  constructor
  · rintro (h | h)
    · rcases mul_pos_iff.mp h.1 with hpos | hneg
      · left
        constructor <;> linarith [hpos.1, hpos.2]
      · right
        constructor <;> linarith [hneg.1, hneg.2]
    · exact False.elim ((not_lt_of_ge (le_of_lt hden)) h.2)
  · rintro (h | h)
    · left
      constructor
      · exact mul_pos (by linarith [h.2]) (by linarith [h.1])
      · exact hden
    · left
      constructor
      · exact mul_pos_of_neg_of_neg (by linarith [h.1]) (by linarith [h.2])
      · exact hden

/-- Positive-scale chamber between the torsion and zero-speed walls. -/
abbrev PhysicalRegionI :=
  {P : Parameters //
    0 < (P.q₀ : ℝ) ∧ P.modulus < (P.q₀ : ℝ) ∧
      3 * (P.q₀ : ℝ) < 1 + P.modulus}

/-- Region I's familiar triangular bounds are consequences, not extra assumptions. -/
theorem physicalRegionI_bounds (P : PhysicalRegionI) :
    -1 < P.val.modulus ∧ P.val.modulus < 1 / 2 ∧
      0 < (P.val.q₀ : ℝ) ∧ (P.val.q₀ : ℝ) < 1 / 2 := by
  rcases P.property with ⟨hq, hmq, hspeed⟩
  constructor
  · linarith
  constructor
  · linarith
  exact ⟨hq, by linarith⟩

theorem physicalRegionI_gammaSq_pos (P : PhysicalRegionI) : 0 < gammaSq P := by
  rw [gammaSq_pos_iff]
  exact Or.inl ⟨P.property.1, P.property.2.2⟩

theorem physicalRegionI_nuSq_pos (P : PhysicalRegionI) : 0 < nuSq P := by
  rw [nuSq_pos_iff]
  left
  have hb := physicalRegionI_bounds P
  exact ⟨P.property.2.1, lt_trans hb.2.2.2 (by norm_num)⟩

/-- Negative-scale chamber on the opposite side of the zero-speed wall. -/
abbrev PhysicalRegionII :=
  {P : Parameters //
    (P.q₀ : ℝ) < 0 ∧ 1 + P.modulus < 3 * (P.q₀ : ℝ)}

/-- Region II's ordering is forced by its two minimal defining inequalities. -/
theorem physicalRegionII_bounds (P : PhysicalRegionII) :
    P.val.modulus < -1 ∧ P.val.modulus < (P.val.q₀ : ℝ) ∧
      (P.val.q₀ : ℝ) < 0 := by
  rcases P.property with ⟨hq, hspeed⟩
  exact ⟨by linarith, by linarith, hq⟩

theorem physicalRegionII_gammaSq_pos (P : PhysicalRegionII) : 0 < gammaSq P := by
  rw [gammaSq_pos_iff]
  exact Or.inr P.property

theorem physicalRegionII_nuSq_pos (P : PhysicalRegionII) : 0 < nuSq P := by
  rw [nuSq_pos_iff]
  left
  have hb := physicalRegionII_bounds P
  exact ⟨hb.2.1, by linarith [hb.2.2]⟩

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
