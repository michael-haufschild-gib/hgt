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

/-- A pair product has only one free divisor: the second factor is forced by the first. -/
theorem card_mtHarmanPairCellTuples_le_divisors
    {S₁ S₂ : Finset ℕ} {m : ℕ} (hm : 0 < m) :
    (mtHarmanPairCellTuples S₁ S₂ m).card ≤ m.divisors.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro q hq
    have htuple := mem_mtHarmanPairCellTuples.mp hq
    exact Nat.mem_divisors.mpr ⟨⟨q.2, htuple.2.2.symm⟩, hm.ne'⟩
  · intro q hq r hr hfirst
    have hqTuple := mem_mtHarmanPairCellTuples.mp hq
    have hrTuple := mem_mtHarmanPairCellTuples.mp hr
    have hqDvd : q.1 ∣ m := ⟨q.2, hqTuple.2.2.symm⟩
    have hqPos : 0 < q.1 := Nat.pos_of_dvd_of_pos hqDvd hm
    apply Prod.ext hfirst
    exact Nat.eq_of_mul_eq_mul_left hqPos (by
      calc
        q.1 * q.2 = m := hqTuple.2.2
        _ = r.1 * r.2 := hrTuple.2.2.symm
        _ = q.1 * r.2 := by rw [hfirst])

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

/-- Two disjoint prime blocks give at most one ordered factorization of a fixed product. -/
theorem card_mtHarmanPairCellTuples_le_one_of_disjoint
    {S₁ S₂ : Finset ℕ}
    (hdisjoint : Disjoint S₁ S₂)
    (hprime₁ : ∀ q ∈ S₁, q.Prime)
    (hprime₂ : ∀ q ∈ S₂, q.Prime)
    (m : ℕ) :
    (mtHarmanPairCellTuples S₁ S₂ m).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro q hq r hr
  have hq' := mem_mtHarmanPairCellTuples.mp hq
  have hr' := mem_mtHarmanPairCellTuples.mp hr
  have hprod : q.1 * q.2 = r.1 * r.2 := hq'.2.2.trans hr'.2.2.symm
  have hq₁Prime := hprime₁ q.1 hq'.1
  have hq₂Prime := hprime₂ q.2 hq'.2.1
  have hr₁Prime := hprime₁ r.1 hr'.1
  have hr₂Prime := hprime₂ r.2 hr'.2.1
  have hq₁Dvd : q.1 ∣ r.1 * r.2 := ⟨q.2, hprod.symm⟩
  rcases hq₁Prime.dvd_mul.mp hq₁Dvd with hq₁r₁ | hq₁r₂
  · have hfirst : q.1 = r.1 :=
      (Nat.prime_dvd_prime_iff_eq hq₁Prime hr₁Prime).mp hq₁r₁
    have hsecond : q.2 = r.2 := by
      exact Nat.eq_of_mul_eq_mul_left hq₁Prime.pos (hfirst ▸ hprod)
    exact Prod.ext hfirst hsecond
  · have hcross : q.1 = r.2 :=
      (Nat.prime_dvd_prime_iff_eq hq₁Prime hr₂Prime).mp hq₁r₂
    exact False.elim ((Finset.disjoint_left.mp hdisjoint) hq'.1 (hcross ▸ hr'.2.1))

theorem norm_mtHarmanPairCellCoefficient_le_one_of_disjoint
    {S₁ S₂ : Finset ℕ}
    (hdisjoint : Disjoint S₁ S₂)
    (hprime₁ : ∀ q ∈ S₁, q.Prime)
    (hprime₂ : ∀ q ∈ S₂, q.Prime)
    (m : ℕ) :
    ‖mtHarmanPairCellCoefficient S₁ S₂ m‖ ≤ 1 := by
  have hcard := card_mtHarmanPairCellTuples_le_one_of_disjoint
    hdisjoint hprime₁ hprime₂ m
  simpa [mtHarmanPairCellCoefficient] using (show
    ((mtHarmanPairCellTuples S₁ S₂ m).card : ℝ) ≤ 1 by exact_mod_cast hcard)

/-- Every good adjacent pair-cell coefficient is uniformly bounded by one, as required by the
repaired finite Lemma 2.3 iteration. -/
theorem norm_mtHarmanPairCellCoefficient_le_one
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    {E : ℝ} {i₁ i₂ : Fin t}
    (hcell : (i₁, i₂) ∈ mtHarmanGoodPairCells endpoint E)
    (m : ℕ) :
    ‖mtHarmanPairCellCoefficient
      (mtAdjacentPrimeBlock endpoint i₁) (mtAdjacentPrimeBlock endpoint i₂) m‖ ≤ 1 := by
  have hidx : i₁ ≠ i₂ := by
    have := (mem_mtHarmanGoodPairCells.mp hcell).1
    omega
  have hdisjoint := mtAdjacentPrimeBlock_disjoint endpoint hmono i₁ i₂ hidx
  have hprime : ∀ i : Fin t, ∀ q ∈ mtAdjacentPrimeBlock endpoint i, q.Prime := by
    intro i q hq
    exact (mem_primesIco.mp hq).2.2
  exact norm_mtHarmanPairCellCoefficient_le_one_of_disjoint hdisjoint
    (hprime i₁) (hprime i₂) m

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

/-- A triple product has only two free divisors: the last factor is forced by the first pair. -/
theorem card_mtHarmanTripleCellTuples_le_divisors_sq
    {S₁ S₂ S₃ : Finset ℕ} {m : ℕ} (hm : 0 < m) :
    (mtHarmanTripleCellTuples S₁ S₂ S₃ m).card ≤ m.divisors.card ^ 2 := by
  calc
    (mtHarmanTripleCellTuples S₁ S₂ S₃ m).card ≤
        (m.divisors.product m.divisors).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro q hq
        have htuple := mem_mtHarmanTripleCellTuples.mp hq
        exact Finset.mem_product.mpr ⟨
          Nat.mem_divisors.mpr ⟨⟨q.1.2 * q.2, by
            simpa [Nat.mul_assoc] using htuple.2.2.2.symm⟩, hm.ne'⟩,
          Nat.mem_divisors.mpr ⟨⟨q.1.1 * q.2, by
            simpa [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
              htuple.2.2.2.symm⟩, hm.ne'⟩⟩
      · intro q hq r hr hpair
        have hqTuple := mem_mtHarmanTripleCellTuples.mp hq
        have hrTuple := mem_mtHarmanTripleCellTuples.mp hr
        have hprefixDvd : q.1.1 * q.1.2 ∣ m :=
          ⟨q.2, hqTuple.2.2.2.symm⟩
        have hprefixPos : 0 < q.1.1 * q.1.2 :=
          Nat.pos_of_dvd_of_pos hprefixDvd hm
        apply Prod.ext hpair
        exact Nat.eq_of_mul_eq_mul_left hprefixPos (by
          calc
            q.1.1 * q.1.2 * q.2 = m := hqTuple.2.2.2
            _ = r.1.1 * r.1.2 * r.2 := hrTuple.2.2.2.symm
            _ = q.1.1 * q.1.2 * r.2 := by rw [hpair])
    _ = m.divisors.card ^ 2 := by simp [pow_two]

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

/-- Three pairwise-disjoint prime blocks give at most one ordered factorization of a fixed
product. -/
theorem card_mtHarmanTripleCellTuples_le_one_of_pairwise_disjoint
    {S₁ S₂ S₃ : Finset ℕ}
    (hdisjoint₁₂ : Disjoint S₁ S₂)
    (hdisjoint₁₃ : Disjoint S₁ S₃)
    (hdisjoint₂₃ : Disjoint S₂ S₃)
    (hprime₁ : ∀ q ∈ S₁, q.Prime)
    (hprime₂ : ∀ q ∈ S₂, q.Prime)
    (hprime₃ : ∀ q ∈ S₃, q.Prime)
    (m : ℕ) :
    (mtHarmanTripleCellTuples S₁ S₂ S₃ m).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro q hq r hr
  have hq' := mem_mtHarmanTripleCellTuples.mp hq
  have hr' := mem_mtHarmanTripleCellTuples.mp hr
  have hprod : q.1.1 * q.1.2 * q.2 = r.1.1 * r.1.2 * r.2 :=
    hq'.2.2.2.trans hr'.2.2.2.symm
  have hq₁Prime := hprime₁ q.1.1 hq'.1
  have hq₂Prime := hprime₂ q.1.2 hq'.2.1
  have hr₁Prime := hprime₁ r.1.1 hr'.1
  have hr₂Prime := hprime₂ r.1.2 hr'.2.1
  have hr₃Prime := hprime₃ r.2 hr'.2.2.1
  have hq₁Dvd : q.1.1 ∣ r.1.1 * (r.1.2 * r.2) := by
    refine ⟨q.1.2 * q.2, ?_⟩
    simpa only [Nat.mul_assoc] using hprod.symm
  have hfirst : q.1.1 = r.1.1 := by
    rcases hq₁Prime.dvd_mul.mp hq₁Dvd with hq₁r₁ | hq₁tail
    · exact (Nat.prime_dvd_prime_iff_eq hq₁Prime hr₁Prime).mp hq₁r₁
    · rcases hq₁Prime.dvd_mul.mp hq₁tail with hq₁r₂ | hq₁r₃
      · have hcross := (Nat.prime_dvd_prime_iff_eq hq₁Prime hr₂Prime).mp hq₁r₂
        exact False.elim
          ((Finset.disjoint_left.mp hdisjoint₁₂) hq'.1 (hcross ▸ hr'.2.1))
      · have hcross := (Nat.prime_dvd_prime_iff_eq hq₁Prime hr₃Prime).mp hq₁r₃
        exact False.elim
          ((Finset.disjoint_left.mp hdisjoint₁₃) hq'.1 (hcross ▸ hr'.2.2.1))
  have htailProd : q.1.2 * q.2 = r.1.2 * r.2 := by
    apply Nat.eq_of_mul_eq_mul_left hq₁Prime.pos
    simpa only [Nat.mul_assoc, hfirst] using hprod
  have hq₂Dvd : q.1.2 ∣ r.1.2 * r.2 := ⟨q.2, htailProd.symm⟩
  have hsecond : q.1.2 = r.1.2 := by
    rcases hq₂Prime.dvd_mul.mp hq₂Dvd with hq₂r₂ | hq₂r₃
    · exact (Nat.prime_dvd_prime_iff_eq hq₂Prime hr₂Prime).mp hq₂r₂
    · have hcross := (Nat.prime_dvd_prime_iff_eq hq₂Prime hr₃Prime).mp hq₂r₃
      exact False.elim
        ((Finset.disjoint_left.mp hdisjoint₂₃) hq'.2.1 (hcross ▸ hr'.2.2.1))
  have hthird : q.2 = r.2 := by
    exact Nat.eq_of_mul_eq_mul_left hq₂Prime.pos (hsecond ▸ htailProd)
  exact Prod.ext (Prod.ext hfirst hsecond) hthird

theorem norm_mtHarmanTripleCellCoefficient_le_one_of_pairwise_disjoint
    {S₁ S₂ S₃ : Finset ℕ}
    (hdisjoint₁₂ : Disjoint S₁ S₂)
    (hdisjoint₁₃ : Disjoint S₁ S₃)
    (hdisjoint₂₃ : Disjoint S₂ S₃)
    (hprime₁ : ∀ q ∈ S₁, q.Prime)
    (hprime₂ : ∀ q ∈ S₂, q.Prime)
    (hprime₃ : ∀ q ∈ S₃, q.Prime)
    (m : ℕ) :
    ‖mtHarmanTripleCellCoefficient S₁ S₂ S₃ m‖ ≤ 1 := by
  have hcard := card_mtHarmanTripleCellTuples_le_one_of_pairwise_disjoint
    hdisjoint₁₂ hdisjoint₁₃ hdisjoint₂₃ hprime₁ hprime₂ hprime₃ m
  simpa [mtHarmanTripleCellCoefficient] using (show
    ((mtHarmanTripleCellTuples S₁ S₂ S₃ m).card : ℝ) ≤ 1 by exact_mod_cast hcard)

/-- Every good adjacent triple-cell coefficient is uniformly bounded by one. -/
theorem norm_mtHarmanTripleCellCoefficient_le_one
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    {E : ℝ} {i₁ i₂ i₃ : Fin t}
    (hcell : ((i₁, i₂), i₃) ∈ mtHarmanGoodTripleCells endpoint E)
    (m : ℕ) :
    ‖mtHarmanTripleCellCoefficient
      (mtAdjacentPrimeBlock endpoint i₁) (mtAdjacentPrimeBlock endpoint i₂)
      (mtAdjacentPrimeBlock endpoint i₃) m‖ ≤ 1 := by
  have hidx := mem_mtHarmanGoodTripleCells.mp hcell
  have hne₁₂ : i₁ ≠ i₂ := by omega
  have hne₁₃ : i₁ ≠ i₃ := by omega
  have hne₂₃ : i₂ ≠ i₃ := by omega
  have hprime : ∀ i : Fin t, ∀ q ∈ mtAdjacentPrimeBlock endpoint i, q.Prime := by
    intro i q hq
    exact (mem_primesIco.mp hq).2.2
  exact norm_mtHarmanTripleCellCoefficient_le_one_of_pairwise_disjoint
    (mtAdjacentPrimeBlock_disjoint endpoint hmono i₁ i₂ hne₁₂)
    (mtAdjacentPrimeBlock_disjoint endpoint hmono i₁ i₃ hne₁₃)
    (mtAdjacentPrimeBlock_disjoint endpoint hmono i₂ i₃ hne₂₃)
    (hprime i₁) (hprime i₂) (hprime i₃) m

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
