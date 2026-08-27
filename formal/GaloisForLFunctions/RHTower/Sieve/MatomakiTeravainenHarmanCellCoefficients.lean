import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanRectangles
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPieceTypes

/-!
# Exact coefficients of rectangular Harman cells

Each good pair or triple cell contributes the literal number of ordered prime tuples with a given
product.  These coefficients are unconditionally divisor-bounded, with exponents two and three,
and every tuple automatically satisfies the source order and geometry predicates.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Ordered pair factorizations from two fixed prime blocks. -/
def mtHarmanPairCellTuples (S₁ S₂ : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (S₁.product S₂).filter fun q => q.1 * q.2 = m

theorem mem_mtHarmanPairCellTuples
    {S₁ S₂ : Finset ℕ} {m q₁ q₂ : ℕ} :
    (q₁, q₂) ∈ mtHarmanPairCellTuples S₁ S₂ m ↔
      q₁ ∈ S₁ ∧ q₂ ∈ S₂ ∧ q₁ * q₂ = m := by
  simp [mtHarmanPairCellTuples, and_assoc]

/-- Literal pair-cell coefficient. -/
def mtHarmanPairCellCoefficient (S₁ S₂ : Finset ℕ) (m : ℕ) : ℂ :=
  (mtHarmanPairCellTuples S₁ S₂ m).card

theorem mtHarmanPairCellCoefficient_eq_source_sum
    (S₁ S₂ : Finset ℕ) (m : ℕ) :
    mtHarmanPairCellCoefficient S₁ S₂ m =
      ∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, if q₁ * q₂ = m then 1 else 0 := by
  classical
  unfold mtHarmanPairCellCoefficient mtHarmanPairCellTuples
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  exact Finset.sum_product S₁ S₂
    (fun q => if q.1 * q.2 = m then (1 : ℂ) else 0)

/-- Pair-cell coefficients have the unconditional divisor-square bound. -/
theorem card_mtHarmanPairCellTuples_le_divisors_sq
    {S₁ S₂ : Finset ℕ} {m : ℕ} (hm : 0 < m) :
    (mtHarmanPairCellTuples S₁ S₂ m).card ≤ m.divisors.card ^ 2 := by
  have hsubset : mtHarmanPairCellTuples S₁ S₂ m ⊆ m.divisors.product m.divisors := by
    intro q hq
    have htuple := mem_mtHarmanPairCellTuples.mp hq
    exact Finset.mem_product.mpr ⟨by
      · rw [Nat.mem_divisors]
        exact ⟨⟨q.2, htuple.2.2.symm⟩, hm.ne'⟩,
      by
        rw [Nat.mem_divisors]
        exact ⟨⟨q.1, by simpa [Nat.mul_comm] using htuple.2.2.symm⟩, hm.ne'⟩⟩
  calc
    (mtHarmanPairCellTuples S₁ S₂ m).card ≤
        (m.divisors.product m.divisors).card := Finset.card_le_card hsubset
    _ = m.divisors.card ^ 2 := by simp [pow_two]

theorem mtHarmanPairCellCoefficient_polynomialDivisorBounded
    (S₁ S₂ : Finset ℕ) :
    MTPolynomialDivisorBounded (mtHarmanPairCellCoefficient S₁ S₂) := by
  refine ⟨1, by norm_num, 2, ?_⟩
  intro m hm
  have hcard := card_mtHarmanPairCellTuples_le_divisors_sq
    (S₁ := S₁) (S₂ := S₂) hm
  simpa [mtHarmanPairCellCoefficient] using (show
    ((mtHarmanPairCellTuples S₁ S₂ m).card : ℝ) ≤
      (m.divisors.card : ℝ) ^ 2 by exact_mod_cast hcard)

/-- A nonzero adjacent pair-cell coefficient has exactly the product support of its two block
scales. -/
theorem mtHarmanPairCellCoefficient_support
    {t : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 1 ≤ endpoint i)
    {i₁ i₂ : Fin t} {m : ℕ}
    (hm : mtHarmanPairCellCoefficient
      (mtAdjacentPrimeBlock endpoint i₁) (mtAdjacentPrimeBlock endpoint i₂) m ≠ 0) :
    mtAdjacentBlockLowerScale endpoint i₁ *
        mtAdjacentBlockLowerScale endpoint i₂ < (m : ℝ) ∧
      (m : ℝ) ≤ mtAdjacentBlockUpperScale endpoint i₁ *
        mtAdjacentBlockUpperScale endpoint i₂ := by
  have hcard : (mtHarmanPairCellTuples
      (mtAdjacentPrimeBlock endpoint i₁) (mtAdjacentPrimeBlock endpoint i₂) m).card ≠ 0 := by
    intro hzero
    apply hm
    simp [mtHarmanPairCellCoefficient, hzero]
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard)
  have htuple := mem_mtHarmanPairCellTuples.mp hq
  have hq₁ := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₁ q.1).mp htuple.1
  have hq₂ := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₂ q.2).mp htuple.2.1
  have hprodCast : (m : ℝ) = (q.1 : ℝ) * (q.2 : ℝ) := by
    exact_mod_cast htuple.2.2.symm
  rw [hprodCast]
  constructor
  · calc
      mtAdjacentBlockLowerScale endpoint i₁ *
          mtAdjacentBlockLowerScale endpoint i₂ ≤
        (q.1 : ℝ) * mtAdjacentBlockLowerScale endpoint i₂ :=
          mul_le_mul_of_nonneg_right hq₁.2.1.le
            (by simp [mtAdjacentBlockLowerScale])
      _ < (q.1 : ℝ) * (q.2 : ℝ) :=
        mul_lt_mul_of_pos_left hq₂.2.1 (by exact_mod_cast hq₁.1.pos)
  · exact mul_le_mul hq₁.2.2 hq₂.2.2 (Nat.cast_nonneg _)
      (by simp [mtAdjacentBlockUpperScale])

/-- Ordered triple factorizations from three fixed prime blocks. -/
def mtHarmanTripleCellTuples (S₁ S₂ S₃ : Finset ℕ) (m : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  ((S₁.product S₂).product S₃).filter fun q => q.1.1 * q.1.2 * q.2 = m

theorem mem_mtHarmanTripleCellTuples
    {S₁ S₂ S₃ : Finset ℕ} {m q₁ q₂ q₃ : ℕ} :
    ((q₁, q₂), q₃) ∈ mtHarmanTripleCellTuples S₁ S₂ S₃ m ↔
      q₁ ∈ S₁ ∧ q₂ ∈ S₂ ∧ q₃ ∈ S₃ ∧ q₁ * q₂ * q₃ = m := by
  simp [mtHarmanTripleCellTuples, and_assoc]

/-- Literal triple-cell coefficient. -/
def mtHarmanTripleCellCoefficient
    (S₁ S₂ S₃ : Finset ℕ) (m : ℕ) : ℂ :=
  (mtHarmanTripleCellTuples S₁ S₂ S₃ m).card

theorem mtHarmanTripleCellCoefficient_eq_source_sum
    (S₁ S₂ S₃ : Finset ℕ) (m : ℕ) :
    mtHarmanTripleCellCoefficient S₁ S₂ S₃ m =
      ∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, ∑ q₃ ∈ S₃,
        if q₁ * q₂ * q₃ = m then 1 else 0 := by
  classical
  unfold mtHarmanTripleCellCoefficient mtHarmanTripleCellTuples
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  calc
    (∑ q ∈ (S₁.product S₂).product S₃,
        if q.1.1 * q.1.2 * q.2 = m then (1 : ℂ) else 0) =
      ∑ q ∈ S₁.product S₂, ∑ q₃ ∈ S₃,
        if q.1 * q.2 * q₃ = m then 1 else 0 :=
      Finset.sum_product (S₁.product S₂) S₃ _
    _ = ∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, ∑ q₃ ∈ S₃,
        if q₁ * q₂ * q₃ = m then 1 else 0 := by
      exact Finset.sum_product S₁ S₂
        (fun q => ∑ q₃ ∈ S₃, if q.1 * q.2 * q₃ = m then (1 : ℂ) else 0)

/-- Triple-cell coefficients have the unconditional divisor-cube bound. -/
theorem card_mtHarmanTripleCellTuples_le_divisors_cube
    {S₁ S₂ S₃ : Finset ℕ} {m : ℕ} (hm : 0 < m) :
    (mtHarmanTripleCellTuples S₁ S₂ S₃ m).card ≤ m.divisors.card ^ 3 := by
  have hsubset : mtHarmanTripleCellTuples S₁ S₂ S₃ m ⊆
      (m.divisors.product m.divisors).product m.divisors := by
    intro q hq
    have htuple := mem_mtHarmanTripleCellTuples.mp hq
    have hq₁Dvd : q.1.1 ∈ m.divisors := by
      rw [Nat.mem_divisors]
      exact ⟨⟨q.1.2 * q.2, by simpa [Nat.mul_assoc] using htuple.2.2.2.symm⟩,
        hm.ne'⟩
    have hq₂Dvd : q.1.2 ∈ m.divisors := by
      rw [Nat.mem_divisors]
      exact ⟨⟨q.1.1 * q.2, by
        simpa [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
          htuple.2.2.2.symm⟩, hm.ne'⟩
    have hq₃Dvd : q.2 ∈ m.divisors := by
      rw [Nat.mem_divisors]
      exact ⟨⟨q.1.1 * q.1.2, by
        simpa [Nat.mul_comm] using htuple.2.2.2.symm⟩, hm.ne'⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hq₁Dvd, hq₂Dvd⟩, hq₃Dvd⟩
  calc
    (mtHarmanTripleCellTuples S₁ S₂ S₃ m).card ≤
        ((m.divisors.product m.divisors).product m.divisors).card :=
      Finset.card_le_card hsubset
    _ = m.divisors.card ^ 3 := by simp [pow_succ]

theorem mtHarmanTripleCellCoefficient_polynomialDivisorBounded
    (S₁ S₂ S₃ : Finset ℕ) :
    MTPolynomialDivisorBounded (mtHarmanTripleCellCoefficient S₁ S₂ S₃) := by
  refine ⟨1, by norm_num, 3, ?_⟩
  intro m hm
  have hcard := card_mtHarmanTripleCellTuples_le_divisors_cube
    (S₁ := S₁) (S₂ := S₂) (S₃ := S₃) hm
  simpa [mtHarmanTripleCellCoefficient] using (show
    ((mtHarmanTripleCellTuples S₁ S₂ S₃ m).card : ℝ) ≤
      (m.divisors.card : ℝ) ^ 3 by exact_mod_cast hcard)

/-- A nonzero adjacent triple-cell coefficient has exactly the product support of its three block
scales. -/
theorem mtHarmanTripleCellCoefficient_support
    {t : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 1 ≤ endpoint i)
    {i₁ i₂ i₃ : Fin t} {m : ℕ}
    (hm : mtHarmanTripleCellCoefficient
      (mtAdjacentPrimeBlock endpoint i₁) (mtAdjacentPrimeBlock endpoint i₂)
      (mtAdjacentPrimeBlock endpoint i₃) m ≠ 0) :
    mtAdjacentBlockLowerScale endpoint i₁ *
        mtAdjacentBlockLowerScale endpoint i₂ *
          mtAdjacentBlockLowerScale endpoint i₃ < (m : ℝ) ∧
      (m : ℝ) ≤ mtAdjacentBlockUpperScale endpoint i₁ *
        mtAdjacentBlockUpperScale endpoint i₂ *
          mtAdjacentBlockUpperScale endpoint i₃ := by
  have hcard : (mtHarmanTripleCellTuples
      (mtAdjacentPrimeBlock endpoint i₁) (mtAdjacentPrimeBlock endpoint i₂)
      (mtAdjacentPrimeBlock endpoint i₃) m).card ≠ 0 := by
    intro hzero
    apply hm
    simp [mtHarmanTripleCellCoefficient, hzero]
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard)
  have htuple := mem_mtHarmanTripleCellTuples.mp hq
  have hq₁ := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₁ q.1.1).mp htuple.1
  have hq₂ := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₂ q.1.2).mp htuple.2.1
  have hq₃ := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₃ q.2).mp htuple.2.2.1
  have hpairLower : mtAdjacentBlockLowerScale endpoint i₁ *
      mtAdjacentBlockLowerScale endpoint i₂ < (q.1.1 : ℝ) * (q.1.2 : ℝ) :=
    calc
      mtAdjacentBlockLowerScale endpoint i₁ *
          mtAdjacentBlockLowerScale endpoint i₂ ≤
        (q.1.1 : ℝ) * mtAdjacentBlockLowerScale endpoint i₂ :=
          mul_le_mul_of_nonneg_right hq₁.2.1.le
            (by simp [mtAdjacentBlockLowerScale])
      _ < (q.1.1 : ℝ) * (q.1.2 : ℝ) :=
        mul_lt_mul_of_pos_left hq₂.2.1 (by exact_mod_cast hq₁.1.pos)
  have hpairUpper : (q.1.1 : ℝ) * (q.1.2 : ℝ) ≤
      mtAdjacentBlockUpperScale endpoint i₁ * mtAdjacentBlockUpperScale endpoint i₂ :=
    mul_le_mul hq₁.2.2 hq₂.2.2 (Nat.cast_nonneg _)
      (by simp [mtAdjacentBlockUpperScale])
  have hprodCast : (m : ℝ) = (q.1.1 : ℝ) * (q.1.2 : ℝ) * (q.2 : ℝ) := by
    exact_mod_cast htuple.2.2.2.symm
  rw [hprodCast]
  constructor
  · calc
      mtAdjacentBlockLowerScale endpoint i₁ *
          mtAdjacentBlockLowerScale endpoint i₂ *
            mtAdjacentBlockLowerScale endpoint i₃ ≤
        ((q.1.1 : ℝ) * (q.1.2 : ℝ)) *
          mtAdjacentBlockLowerScale endpoint i₃ :=
            mul_le_mul_of_nonneg_right hpairLower.le
              (by simp [mtAdjacentBlockLowerScale])
      _ < (q.1.1 : ℝ) * (q.1.2 : ℝ) * (q.2 : ℝ) :=
        mul_lt_mul_of_pos_left hq₃.2.1
          (mul_pos (by exact_mod_cast hq₁.1.pos) (by exact_mod_cast hq₂.1.pos))
  · exact mul_le_mul hpairUpper hq₃.2.2 (Nat.cast_nonneg _)
      (mul_nonneg (by simp [mtAdjacentBlockUpperScale])
        (by simp [mtAdjacentBlockUpperScale]))

/-- Every tuple counted by a good pair-cell coefficient satisfies the exact Harman predicates. -/
theorem mtHarmanPairCellTuples_admissible
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {E : ℝ} {i₁ i₂ : Fin t}
    (hcell : (i₁, i₂) ∈ mtHarmanGoodPairCells endpoint E)
    {m q₁ q₂ : ℕ}
    (hq : (q₁, q₂) ∈ mtHarmanPairCellTuples
      (mtAdjacentPrimeBlock endpoint i₁) (mtAdjacentPrimeBlock endpoint i₂) m) :
    q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ = m := by
  have htuple := mem_mtHarmanPairCellTuples.mp hq
  have hadm := mtHarmanGoodPairCell_order_geometry
    hendpoint hmono hcell htuple.1 htuple.2.1
  exact ⟨hadm.1, hadm.2, htuple.2.2⟩

/-- Every tuple counted by a good triple-cell coefficient satisfies the exact Harman predicates. -/
theorem mtHarmanTripleCellTuples_admissible
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {E : ℝ} {i₁ i₂ i₃ : Fin t}
    (hcell : ((i₁, i₂), i₃) ∈ mtHarmanGoodTripleCells endpoint E)
    {m q₁ q₂ q₃ : ℕ}
    (hq : ((q₁, q₂), q₃) ∈ mtHarmanTripleCellTuples
      (mtAdjacentPrimeBlock endpoint i₁) (mtAdjacentPrimeBlock endpoint i₂)
      (mtAdjacentPrimeBlock endpoint i₃) m) :
    q₃ < q₂ ∧ q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧
      q₁ * q₂ * q₃ = m := by
  have htuple := mem_mtHarmanTripleCellTuples.mp hq
  have hadm := mtHarmanGoodTripleCell_orders_geometry
    hendpoint hmono hcell htuple.1 htuple.2.1 htuple.2.2.1
  exact ⟨hadm.1, hadm.2.1, hadm.2.2, htuple.2.2.2⟩

end

end RHTower.Sieve
