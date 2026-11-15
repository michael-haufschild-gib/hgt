import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import GaloisForLFunctions.HilbertMetric.QuantumInformation.FermionSpectralEntropy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Occupied and empty modes in an unresolved spectral cell

For the finite spectral compression in §II and Appendix B of
Sun--Liu--Yi--Lian, *Time Direction Entanglement Entropy of Free Fermion
Ground States*, arXiv:2611.13085, a uniformly observed cell with `a` occupied
and `b` empty modes has occupation `a/(a+b)`. Its entropy vanishes precisely
when the cell does not mix the two populations, regardless of its size.
The empty cell is included with zero occupation and zero entropy.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric

/-- Occupation of an unresolved, uniformly weighted spectral cell. -/
def fermionCellOccupation (a b : ℕ) : ℝ := (a : ℝ) / (a + b : ℕ)

/-- Binary entropy of the compressed cell. -/
def fermionCellEntropy (a b : ℕ) : ℝ := Real.binEntropy (fermionCellOccupation a b)

/-- Number fluctuation in the compressed cell. -/
def fermionCellVariance (a b : ℕ) : ℝ :=
  fermionCellOccupation a b * (1 - fermionCellOccupation a b)

theorem fermionCellOccupation_nonneg (a b : ℕ) : 0 ≤ fermionCellOccupation a b := by
  unfold fermionCellOccupation
  positivity

theorem fermionCellOccupation_le_one (a b : ℕ) : fermionCellOccupation a b ≤ 1 := by
  unfold fermionCellOccupation
  exact div_le_one_of_le₀ (by exact_mod_cast Nat.le_add_right a b) (by positivity)

/-- Cell purity is equivalent to having no occupied modes or no empty modes. -/
theorem fermionCellEntropy_eq_zero_iff (a b : ℕ) :
    fermionCellEntropy a b = 0 ↔ a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · subst a
    simp [fermionCellEntropy, fermionCellOccupation]
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hab : (a + b : ℝ) ≠ 0 := by positivity
  simp only [fermionCellEntropy, Real.binEntropy_eq_zero, fermionCellOccupation, Nat.cast_add]
  rw [div_eq_zero_iff, div_eq_one_iff_eq hab]
  simp only [ha, ha', hab, or_self, false_or]
  constructor
  · intro h
    exact_mod_cast (show (b : ℝ) = 0 by linarith)
  · intro h
    rw [h]
    simp

theorem fermionCellEntropy_nonneg (a b : ℕ) : 0 ≤ fermionCellEntropy a b :=
  Real.binEntropy_nonneg (fermionCellOccupation_nonneg a b) (fermionCellOccupation_le_one a b)

/-- Strict entropy detects mixing rather than merely a large number of samples. -/
theorem fermionCellEntropy_pos_iff (a b : ℕ) :
    0 < fermionCellEntropy a b ↔ 0 < a ∧ 0 < b := by
  rw [lt_iff_le_and_ne]
  simp only [fermionCellEntropy_nonneg, true_and]
  rw [ne_comm]
  simp only [ne_eq, fermionCellEntropy_eq_zero_iff, not_or, Nat.pos_iff_ne_zero]

theorem fermionCellEntropy_le_log_two (a b : ℕ) : fermionCellEntropy a b ≤ Real.log 2 :=
  Real.binEntropy_le_log_two

/-- Balanced nonempty cells attain the one-bit entropy ceiling. -/
theorem fermionCellEntropy_max_iff (a b : ℕ) :
    fermionCellEntropy a b = Real.log 2 ↔ a = b ∧ a ≠ 0 := by
  by_cases ha : a = 0
  · subst a
    have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    simp [fermionCellEntropy, fermionCellOccupation, hlog.symm]
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha)
  have hab : (a + b : ℝ) ≠ 0 := by positivity
  rw [fermionCellEntropy, Real.binEntropy_eq_log_two]
  unfold fermionCellOccupation
  rw [Nat.cast_add]
  constructor
  · intro h
    have h' : (a : ℝ) = b := by
      field_simp at h
      linarith
    exact ⟨Nat.cast_injective h', ha⟩
  · rintro ⟨rfl, _⟩
    field_simp
    ring

/-- Entropy of independent orthogonal compressed cells. -/
def aliasedFermionEntropy {ι : Type*} [Fintype ι] (a b : ι → ℕ) : ℝ :=
  ∑ i, fermionCellEntropy (a i) (b i)

/-- Total entropy is nonnegative, without a rank or nonempty-cell assumption. -/
theorem aliasedFermionEntropy_nonneg {ι : Type*} [Fintype ι] (a b : ι → ℕ) :
    0 ≤ aliasedFermionEntropy a b :=
  Finset.sum_nonneg fun i _ => fermionCellEntropy_nonneg (a i) (b i)

/-- Exact saturation criterion: every observed cell is pure. -/
theorem aliasedFermionEntropy_eq_zero_iff {ι : Type*} [Fintype ι] (a b : ι → ℕ) :
    aliasedFermionEntropy a b = 0 ↔ ∀ i, a i = 0 ∨ b i = 0 := by
  rw [aliasedFermionEntropy, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => fermionCellEntropy_nonneg (a i) (b i))]
  simp only [fermionCellEntropy_eq_zero_iff, Finset.mem_univ, forall_true_left]

/-- The effective number of observed cells, rather than the number of samples,
sets the universal entropy ceiling. -/
theorem aliasedFermionEntropy_le {ι : Type*} [Fintype ι] (a b : ι → ℕ) :
    aliasedFermionEntropy a b ≤ Fintype.card ι * Real.log 2 := by
  calc
    aliasedFermionEntropy a b ≤ ∑ _i : ι, Real.log 2 :=
      Finset.sum_le_sum fun i _ => fermionCellEntropy_le_log_two (a i) (b i)
    _ = _ := by simp

/-- These cell entropies are the spectral entropy of the actual diagonal correlation matrix. -/
theorem aliasedFermionEntropy_eq_spectral
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℕ) :
    aliasedFermionEntropy a b = fermionSpectralEntropy
      (Matrix.diagonal (fun i => (fermionCellOccupation (a i) (b i) : ℂ))) := by
  rw [fermionSpectralEntropy_diagonal]
  rfl

/-- Particle-hole exchange preserves entropy, including the empty cell. -/
theorem fermionCellEntropy_swap (a b : ℕ) : fermionCellEntropy a b = fermionCellEntropy b a := by
  by_cases hz : a + b = 0
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hz
    rfl
  have hden : (a + b : ℝ) ≠ 0 := by exact_mod_cast hz
  have he : fermionCellOccupation b a = 1 - fermionCellOccupation a b := by
    unfold fermionCellOccupation
    push_cast
    rw [add_comm (b : ℝ) a]
    field_simp
    ring
  rw [fermionCellEntropy, fermionCellEntropy, he, Real.binEntropy_one_sub]

/-- Number fluctuations count occupied-empty pairs within the same cell. -/
theorem fermionCellVariance_eq (a b : ℕ) :
    fermionCellVariance a b = (a : ℝ) * b / (a + b : ℕ) ^ 2 := by
  by_cases hz : a + b = 0
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hz
    simp [fermionCellVariance, fermionCellOccupation]
  have hden : (a + b : ℝ) ≠ 0 := by exact_mod_cast hz
  unfold fermionCellVariance fermionCellOccupation
  push_cast
  field_simp
  ring

/-- Entropy controls twice the fermion number fluctuation in every cell. -/
theorem fermionCellEntropy_ge_two_variance (a b : ℕ) :
    2 * fermionCellVariance a b ≤ fermionCellEntropy a b := by
  by_cases ha : a = 0
  · subst a
    simp [fermionCellVariance, fermionCellOccupation, fermionCellEntropy]
  by_cases hb : b = 0
  · subst b
    simp [fermionCellVariance, fermionCellOccupation, fermionCellEntropy, ha]
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha)
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)
  have hp : 0 < fermionCellOccupation a b := by unfold fermionCellOccupation; positivity
  have hp1 : fermionCellOccupation a b < 1 := by
    unfold fermionCellOccupation
    rw [div_lt_one (by positivity)]
    push_cast
    linarith only [hb']
  have hq : 0 < 1 - fermionCellOccupation a b := sub_pos.mpr hp1
  have h₁ := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hp) hp.le
  have h₂ := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hq) hq.le
  unfold fermionCellVariance fermionCellEntropy Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  nlinarith only [h₁, h₂]

end GaloisForLFunctions.HilbertMetric
