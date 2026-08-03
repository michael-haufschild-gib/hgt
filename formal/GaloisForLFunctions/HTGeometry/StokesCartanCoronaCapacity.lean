import GaloisForLFunctions.HTGeometry.StokesCartanTypeALegs

/-!
# Corona recursion for Stokes--Cartan capacity

The positive Stokes--Cartan energy is an electrical tree energy after the change of variables
`m_i = r_i x_i`.  This module proves the exact finite parallel-completion identity consumed at
every corona-pruning step and the series-extension invariance of the Lorentz capacity wall.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

namespace CoronaCapacity

noncomputable def conductanceSum {n : ℕ} (resistance : Fin n → ℝ) : ℝ :=
  ∑ i, (resistance i)⁻¹

theorem conductanceSum_pos {n : ℕ} [Nonempty (Fin n)]
    {resistance : Fin n → ℝ} (hres : ∀ i, 0 < resistance i) :
    0 < conductanceSum resistance := by
  apply Finset.sum_pos'
  · intro i _
    exact (inv_pos.mpr (hres i)).le
  · let i : Fin n := Classical.choice inferInstance
    exact ⟨i, Finset.mem_univ _, inv_pos.mpr (hres i)⟩

/-- Exact parallel law.  The first term on the right is the positive fluctuation energy around
the unique current split proportional to conductance; the second is the effective resistance
times total current squared. -/
theorem parallel_completion {n : ℕ} [Nonempty (Fin n)]
    (resistance current : Fin n → ℝ) (total : ℝ)
    (hres : ∀ i, 0 < resistance i) (hsum : ∑ i, current i = total) :
    (∑ i, resistance i * current i ^ 2) =
      (∑ i, (current i -
        (resistance i)⁻¹ * total / conductanceSum resistance) ^ 2 * resistance i) +
      total ^ 2 / conductanceSum resistance := by
  have hS : conductanceSum resistance ≠ 0 :=
    ne_of_gt (conductanceSum_pos hres)
  have hterm : ∀ i,
      (current i - (resistance i)⁻¹ * total / conductanceSum resistance) ^ 2 *
          resistance i =
        resistance i * current i ^ 2 -
          2 * current i * total / conductanceSum resistance +
          (resistance i)⁻¹ * total ^ 2 / conductanceSum resistance ^ 2 := by
    intro i
    have hRi : resistance i ≠ 0 := ne_of_gt (hres i)
    field_simp
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hlinear :
      (∑ i, 2 * current i * total / conductanceSum resistance) =
        2 * total / conductanceSum resistance * total := by
    calc
      (∑ i, 2 * current i * total / conductanceSum resistance) =
          2 * total / conductanceSum resistance * (∑ i, current i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2 * total / conductanceSum resistance * total := by rw [hsum]
  have hconstant :
      (∑ i, (resistance i)⁻¹ * total ^ 2 / conductanceSum resistance ^ 2) =
        conductanceSum resistance * total ^ 2 / conductanceSum resistance ^ 2 := by
    calc
      (∑ i, (resistance i)⁻¹ * total ^ 2 / conductanceSum resistance ^ 2) =
          (∑ i, (resistance i)⁻¹) *
            (total ^ 2 / conductanceSum resistance ^ 2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = conductanceSum resistance * total ^ 2 /
          conductanceSum resistance ^ 2 := by
        rw [conductanceSum]
        ring
  rw [hlinear, hconstant]
  field_simp
  ring

noncomputable def parallelResistance {n : ℕ} (resistance : Fin n → ℝ) : ℝ :=
  (conductanceSum resistance)⁻¹

theorem parallelResistance_pos {n : ℕ} [Nonempty (Fin n)]
    {resistance : Fin n → ℝ} (hres : ∀ i, 0 < resistance i) :
    0 < parallelResistance resistance :=
  inv_pos.mpr (conductanceSum_pos hres)

theorem parallel_completion_effectiveResistance {n : ℕ} [Nonempty (Fin n)]
    (resistance current : Fin n → ℝ) (total : ℝ)
    (hres : ∀ i, 0 < resistance i) (hsum : ∑ i, current i = total) :
    (∑ i, resistance i * current i ^ 2) =
      (∑ i, (current i - (resistance i)⁻¹ * total /
        conductanceSum resistance) ^ 2 * resistance i) +
      parallelResistance resistance * total ^ 2 := by
  rw [parallel_completion resistance current total hres hsum]
  simp [parallelResistance, div_eq_mul_inv, mul_comm]

/-- A common root extension is a series resistance.  It changes reciprocal capacity and root
defect by the same amount, so the Lorentz wall is gauge-independent. -/
theorem series_extension_gap_invariant (resistance defect extension : ℝ) :
    (resistance + extension) - (defect + extension) = resistance - defect := by
  ring

/-- Scalar Sherman--Morrison update used by root extension. -/
theorem capacity_update (capacity extension : ℝ) (hc : capacity ≠ 0) :
    (capacity / (1 + extension * capacity))⁻¹ = capacity⁻¹ + extension := by
  field_simp

theorem capacityGap_update_invariant (capacity defect extension : ℝ)
    (hc : capacity ≠ 0) :
    (capacity / (1 + extension * capacity))⁻¹ - (defect + extension) =
      capacity⁻¹ - defect := by
  rw [capacity_update capacity extension hc]
  ring

/-- Determinant prefactor is unchanged by the simultaneous determinant-lemma and capacity
updates under a root extension. -/
theorem determinant_capacity_prefactor_invariant
    (detPositive capacity extension : ℝ)
    (hden : 1 + extension * capacity ≠ 0) :
    (detPositive * (1 + extension * capacity)) *
        (capacity / (1 + extension * capacity)) =
      detPositive * capacity := by
  field_simp

end CoronaCapacity

end IrregularStokes
end GaloisForLFunctions
