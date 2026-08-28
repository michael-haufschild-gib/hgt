import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanRectangularSums

/-!
# Aggregate coefficients for rectangular Harman families

The repaired finite iteration must be applied once to each complete good-cell family, not once per
cell.  Ordered source primes make the aggregate pair and triple coefficients zero-one valued.
Their sifted divisor sums are exactly the complete rectangular Harman families.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Sum of all good pair-cell coefficients before the recursive Buchstab iteration. -/
def mtHarmanPairFamilyCoefficient {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (m : ℕ) : ℂ :=
  ∑ cell ∈ mtHarmanActiveGoodPairCells (t := t) endpoint E,
    mtHarmanPairCellCoefficient
      (mtHarmanSourceBlock endpoint P cell.1)
      (mtHarmanSourceBlock endpoint P cell.2) m

/-- Sum of all good triple-cell coefficients before the recursive Buchstab iteration. -/
def mtHarmanTripleFamilyCoefficient {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (m : ℕ) : ℂ :=
  ∑ cell ∈ mtHarmanActiveGoodTripleCells (t := t) endpoint E,
    mtHarmanTripleCellCoefficient
      (mtHarmanSourceBlock endpoint P cell.1.1)
      (mtHarmanSourceBlock endpoint P cell.1.2)
      (mtHarmanSourceBlock endpoint P cell.2) m

theorem mtHarmanPairFamilyCoefficient_eq_card
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (m : ℕ) :
    mtHarmanPairFamilyCoefficient (t := t) endpoint P E m =
      (((mtHarmanPairRectangularTuples (t := t) endpoint P E).filter
        fun q => q.1 * q.2 = m).card : ℕ) := by
  classical
  let cells := mtHarmanActiveGoodPairCells (t := t) endpoint E
  let tuples := fun cell : Fin t × Fin t =>
    mtHarmanPairCellSourceTuples endpoint P cell
  let fibres := fun cell : Fin t × Fin t =>
    (tuples cell).filter fun q => q.1 * q.2 = m
  let R := (mtHarmanPairRectangularTuples (t := t) endpoint P E).filter
    fun q => q.1 * q.2 = m
  have hpair : (↑cells : Set (Fin t × Fin t)).PairwiseDisjoint fibres := by
    apply (pairwiseDisjoint_mtHarmanPairCellSourceTuples
      (t := t) hmono P E).mono
    intro cell
    exact Finset.filter_subset _ _
  have hUnion : cells.biUnion fibres = R := by
    simpa [cells, fibres, R, tuples, mtHarmanPairRectangularTuples] using
      (Finset.filter_biUnion
        (mtHarmanActiveGoodPairCells (t := t) endpoint E)
        (mtHarmanPairCellSourceTuples (t := t) endpoint P)
        (fun q : ℕ × ℕ => q.1 * q.2 = m)).symm
  calc
    mtHarmanPairFamilyCoefficient (t := t) endpoint P E m =
        ∑ cell ∈ cells, ((fibres cell).card : ℂ) := by
      apply Finset.sum_congr rfl
      intro cell hcell
      simp [mtHarmanPairCellCoefficient, fibres, tuples,
        mtHarmanPairCellSourceTuples, mtHarmanPairCellTuples]
    _ = ((cells.biUnion fibres).card : ℕ) := by
      rw [Finset.card_biUnion hpair]
      push_cast
      rfl
    _ = (R.card : ℕ) := by rw [hUnion]

theorem mtHarmanTripleFamilyCoefficient_eq_card
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (m : ℕ) :
    mtHarmanTripleFamilyCoefficient (t := t) endpoint P E m =
      (((mtHarmanTripleRectangularTuples (t := t) endpoint P E).filter
        fun q => q.1.1 * q.1.2 * q.2 = m).card : ℕ) := by
  classical
  let cells := mtHarmanActiveGoodTripleCells (t := t) endpoint E
  let tuples := fun cell : (Fin t × Fin t) × Fin t =>
    mtHarmanTripleCellSourceTuples endpoint P cell
  let fibres := fun cell : (Fin t × Fin t) × Fin t =>
    (tuples cell).filter fun q => q.1.1 * q.1.2 * q.2 = m
  let R := (mtHarmanTripleRectangularTuples (t := t) endpoint P E).filter
    fun q => q.1.1 * q.1.2 * q.2 = m
  have hpair : (↑cells : Set ((Fin t × Fin t) × Fin t)).PairwiseDisjoint fibres := by
    apply (pairwiseDisjoint_mtHarmanTripleCellSourceTuples
      (t := t) hmono P E).mono
    intro cell
    exact Finset.filter_subset _ _
  have hUnion : cells.biUnion fibres = R := by
    simpa [cells, fibres, R, tuples, mtHarmanTripleRectangularTuples] using
      (Finset.filter_biUnion
        (mtHarmanActiveGoodTripleCells (t := t) endpoint E)
        (mtHarmanTripleCellSourceTuples (t := t) endpoint P)
        (fun q : (ℕ × ℕ) × ℕ => q.1.1 * q.1.2 * q.2 = m)).symm
  calc
    mtHarmanTripleFamilyCoefficient (t := t) endpoint P E m =
        ∑ cell ∈ cells, ((fibres cell).card : ℂ) := by
      apply Finset.sum_congr rfl
      intro cell hcell
      simp [mtHarmanTripleCellCoefficient, fibres, tuples,
        mtHarmanTripleCellSourceTuples, mtHarmanTripleCellTuples]
    _ = ((cells.biUnion fibres).card : ℕ) := by
      rw [Finset.card_biUnion hpair]
      push_cast
      rfl
    _ = (R.card : ℕ) := by rw [hUnion]

private theorem mtOrderedPrimePair_eq_of_mul_eq
    {q₁ q₂ r₁ r₂ : ℕ}
    (hq₁Prime : q₁.Prime) (hr₁Prime : r₁.Prime) (hr₂Prime : r₂.Prime)
    (hqOrder : q₂ < q₁) (hrOrder : r₂ < r₁)
    (hprod : q₁ * q₂ = r₁ * r₂) : q₁ = r₁ ∧ q₂ = r₂ := by
  have hq₁Dvd : q₁ ∣ r₁ * r₂ := ⟨q₂, hprod.symm⟩
  rcases hq₁Prime.dvd_mul.mp hq₁Dvd with hq₁r₁ | hq₁r₂
  · have hfirst : q₁ = r₁ :=
      (Nat.prime_dvd_prime_iff_eq hq₁Prime hr₁Prime).mp hq₁r₁
    have hsecond : q₂ = r₂ :=
      Nat.eq_of_mul_eq_mul_left hq₁Prime.pos (by simpa [hfirst] using hprod)
    exact ⟨hfirst, hsecond⟩
  · have hcross : q₁ = r₂ :=
      (Nat.prime_dvd_prime_iff_eq hq₁Prime hr₂Prime).mp hq₁r₂
    have hother : q₂ = r₁ :=
      Nat.eq_of_mul_eq_mul_left hq₁Prime.pos (by
        simpa [hcross, Nat.mul_comm] using hprod)
    omega

private theorem mtHarmanPairRectangularTuple_order_primes
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {P : Finset ℕ} {E : ℝ} {q : ℕ × ℕ}
    (hq : q ∈ mtHarmanPairRectangularTuples (t := t) endpoint P E) :
    q.2 < q.1 ∧ q.1.Prime ∧ q.2.Prime := by
  rw [mtHarmanPairRectangularTuples] at hq
  obtain ⟨cell, hcell, hqCell⟩ := Finset.mem_biUnion.mp hq
  have hqData := Finset.mem_product.mp hqCell
  have hq₁Block := (Finset.mem_inter.mp hqData.1).1
  have hq₂Block := (Finset.mem_inter.mp hqData.2).1
  have horder := (mtHarmanGoodPairCell_order_geometry
    hendpoint hmono (mem_mtHarmanActiveGoodPairCells.mp hcell).1
    hq₁Block hq₂Block).1
  exact ⟨horder, (mem_primesIco.mp hq₁Block).2.2,
    (mem_primesIco.mp hq₂Block).2.2⟩

private theorem mtHarmanTripleRectangularTuple_order_primes
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {P : Finset ℕ} {E : ℝ} {q : (ℕ × ℕ) × ℕ}
    (hq : q ∈ mtHarmanTripleRectangularTuples (t := t) endpoint P E) :
    q.2 < q.1.2 ∧ q.1.2 < q.1.1 ∧
      q.1.1.Prime ∧ q.1.2.Prime ∧ q.2.Prime := by
  rw [mtHarmanTripleRectangularTuples] at hq
  obtain ⟨cell, hcell, hqCell⟩ := Finset.mem_biUnion.mp hq
  have hqData := Finset.mem_product.mp hqCell
  have hqPair := Finset.mem_product.mp hqData.1
  have hq₁Block := (Finset.mem_inter.mp hqPair.1).1
  have hq₂Block := (Finset.mem_inter.mp hqPair.2).1
  have hq₃Block := (Finset.mem_inter.mp hqData.2).1
  have horder := mtHarmanGoodTripleCell_orders_geometry
    hendpoint hmono (mem_mtHarmanActiveGoodTripleCells.mp hcell).1
    hq₁Block hq₂Block hq₃Block
  exact ⟨horder.1, horder.2.1, (mem_primesIco.mp hq₁Block).2.2,
    (mem_primesIco.mp hq₂Block).2.2, (mem_primesIco.mp hq₃Block).2.2⟩

theorem card_mtHarmanPairFamilyCoefficient_fibre_le_one
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (m : ℕ) :
    ((mtHarmanPairRectangularTuples (t := t) endpoint P E).filter
      fun q => q.1 * q.2 = m).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro q hq r hr
  have hq' := Finset.mem_filter.mp hq
  have hr' := Finset.mem_filter.mp hr
  have hqData := mtHarmanPairRectangularTuple_order_primes hendpoint hmono hq'.1
  have hrData := mtHarmanPairRectangularTuple_order_primes hendpoint hmono hr'.1
  have heq := mtOrderedPrimePair_eq_of_mul_eq hqData.2.1 hrData.2.1 hrData.2.2
    hqData.1 hrData.1 (hq'.2.trans hr'.2.symm)
  exact Prod.ext heq.1 heq.2

theorem card_mtHarmanTripleFamilyCoefficient_fibre_le_one
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (m : ℕ) :
    ((mtHarmanTripleRectangularTuples (t := t) endpoint P E).filter
      fun q => q.1.1 * q.1.2 * q.2 = m).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro q hq r hr
  have hq' := Finset.mem_filter.mp hq
  have hr' := Finset.mem_filter.mp hr
  have hqData := mtHarmanTripleRectangularTuple_order_primes hendpoint hmono hq'.1
  have hrData := mtHarmanTripleRectangularTuple_order_primes hendpoint hmono hr'.1
  have hprod : q.1.1 * q.1.2 * q.2 = r.1.1 * r.1.2 * r.2 :=
    hq'.2.trans hr'.2.symm
  have hq₁Dvd : q.1.1 ∣ r.1.1 * r.1.2 * r.2 :=
    ⟨q.1.2 * q.2, by simpa [Nat.mul_assoc] using hprod.symm⟩
  have hq₁Cases : q.1.1 = r.1.1 ∨ q.1.1 = r.1.2 ∨ q.1.1 = r.2 := by
    rcases hqData.2.2.1.dvd_mul.mp hq₁Dvd with hprefix | hlast
    · rcases hqData.2.2.1.dvd_mul.mp hprefix with hfirst | hmiddle
      · exact Or.inl
          ((Nat.prime_dvd_prime_iff_eq hqData.2.2.1 hrData.2.2.1).mp hfirst)
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hqData.2.2.1 hrData.2.2.2.1).mp hmiddle))
    · exact Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hqData.2.2.1 hrData.2.2.2.2).mp hlast))
  have hr₁Dvd : r.1.1 ∣ q.1.1 * q.1.2 * q.2 :=
    ⟨r.1.2 * r.2, by simpa [Nat.mul_assoc] using hprod⟩
  have hr₁Cases : r.1.1 = q.1.1 ∨ r.1.1 = q.1.2 ∨ r.1.1 = q.2 := by
    rcases hrData.2.2.1.dvd_mul.mp hr₁Dvd with hprefix | hlast
    · rcases hrData.2.2.1.dvd_mul.mp hprefix with hfirst | hmiddle
      · exact Or.inl
          ((Nat.prime_dvd_prime_iff_eq hrData.2.2.1 hqData.2.2.1).mp hfirst)
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hrData.2.2.1 hqData.2.2.2.1).mp hmiddle))
    · exact Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hrData.2.2.1 hqData.2.2.2.2).mp hlast))
  have hq₁le : q.1.1 ≤ r.1.1 := by rcases hq₁Cases with h | h | h <;> omega
  have hr₁le : r.1.1 ≤ q.1.1 := by rcases hr₁Cases with h | h | h <;> omega
  have hfirst : q.1.1 = r.1.1 := Nat.le_antisymm hq₁le hr₁le
  have htailProd : q.1.2 * q.2 = r.1.2 * r.2 := by
    apply Nat.eq_of_mul_eq_mul_left hqData.2.2.1.pos
    calc
      q.1.1 * (q.1.2 * q.2) = q.1.1 * q.1.2 * q.2 := by
        rw [Nat.mul_assoc]
      _ = r.1.1 * r.1.2 * r.2 := hprod
      _ = q.1.1 * (r.1.2 * r.2) := by rw [hfirst, Nat.mul_assoc]
  have htail := mtOrderedPrimePair_eq_of_mul_eq hqData.2.2.2.1
    hrData.2.2.2.1 hrData.2.2.2.2 hqData.1 hrData.1 htailProd
  exact Prod.ext (Prod.ext hfirst htail.1) htail.2

theorem norm_mtHarmanPairFamilyCoefficient_le_one
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (m : ℕ) :
    ‖mtHarmanPairFamilyCoefficient (t := t) endpoint P E m‖ ≤ 1 := by
  rw [mtHarmanPairFamilyCoefficient_eq_card hmono]
  simpa using (show
    ((((mtHarmanPairRectangularTuples (t := t) endpoint P E).filter
      fun q => q.1 * q.2 = m).card : ℕ) : ℝ) ≤ 1 by
        exact_mod_cast card_mtHarmanPairFamilyCoefficient_fibre_le_one
          hendpoint hmono P E m)

theorem norm_mtHarmanTripleFamilyCoefficient_le_one
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (m : ℕ) :
    ‖mtHarmanTripleFamilyCoefficient (t := t) endpoint P E m‖ ≤ 1 := by
  rw [mtHarmanTripleFamilyCoefficient_eq_card hmono]
  simpa using (show
    ((((mtHarmanTripleRectangularTuples (t := t) endpoint P E).filter
      fun q => q.1.1 * q.1.2 * q.2 = m).card : ℕ) : ℝ) ≤ 1 by
        exact_mod_cast card_mtHarmanTripleFamilyCoefficient_fibre_le_one
          hendpoint hmono P E m)

theorem mtHarmanPairCellFamilySiftSum_eq_divisorSiftSum_familyCoefficient
    {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ)
    (z : ℕ) {n : ℕ} (hn : 0 < n) :
    mtHarmanPairCellFamilySiftSum (t := t) endpoint P E z n =
      mtDivisorSiftSum (mtHarmanPairFamilyCoefficient (t := t) endpoint P E) z n := by
  classical
  rw [mtHarmanPairCellFamilySiftSum]
  calc
    (∑ cell ∈ mtHarmanActiveGoodPairCells (t := t) endpoint E,
        mtHarmanPairCellSiftSum
          (mtHarmanSourceBlock endpoint P cell.1)
          (mtHarmanSourceBlock endpoint P cell.2) z n) =
      ∑ cell ∈ mtHarmanActiveGoodPairCells (t := t) endpoint E,
        mtDivisorSiftSum
          (mtHarmanPairCellCoefficient
            (mtHarmanSourceBlock endpoint P cell.1)
            (mtHarmanSourceBlock endpoint P cell.2)) z n := by
      apply Finset.sum_congr rfl
      intro cell hcell
      exact mtHarmanPairCellSiftSum_eq_divisorSiftSum _ _ z hn
    _ = mtDivisorSiftSum
        (mtHarmanPairFamilyCoefficient (t := t) endpoint P E) z n := by
      unfold mtDivisorSiftSum mtHarmanPairFamilyCoefficient
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_mul]

theorem mtHarmanTripleCellFamilySiftSum_eq_divisorSiftSum_familyCoefficient
    {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ)
    (z : ℕ) {n : ℕ} (hn : 0 < n) :
    mtHarmanTripleCellFamilySiftSum (t := t) endpoint P E z n =
      mtDivisorSiftSum (mtHarmanTripleFamilyCoefficient (t := t) endpoint P E) z n := by
  classical
  rw [mtHarmanTripleCellFamilySiftSum]
  calc
    (∑ cell ∈ mtHarmanActiveGoodTripleCells (t := t) endpoint E,
        mtHarmanTripleCellSiftSum
          (mtHarmanSourceBlock endpoint P cell.1.1)
          (mtHarmanSourceBlock endpoint P cell.1.2)
          (mtHarmanSourceBlock endpoint P cell.2) z n) =
      ∑ cell ∈ mtHarmanActiveGoodTripleCells (t := t) endpoint E,
        mtDivisorSiftSum
          (mtHarmanTripleCellCoefficient
            (mtHarmanSourceBlock endpoint P cell.1.1)
            (mtHarmanSourceBlock endpoint P cell.1.2)
            (mtHarmanSourceBlock endpoint P cell.2)) z n := by
      apply Finset.sum_congr rfl
      intro cell hcell
      exact mtHarmanTripleCellSiftSum_eq_divisorSiftSum _ _ _ z hn
    _ = mtDivisorSiftSum
        (mtHarmanTripleFamilyCoefficient (t := t) endpoint P E) z n := by
      unfold mtDivisorSiftSum mtHarmanTripleFamilyCoefficient
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_mul]

end

end RHTower.Sieve
