import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseCollisionTwoScale

/-!
# Reverse closure of the Heath--Brown two-scale collision aggregate
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Unit dense coefficient, intrinsically valued in `[0,1]`. -/
def heathBrownDenseUnitWeight : ℕ → Set.Icc (0 : ℝ) 1 :=
  fun _ => ⟨1, by constructor <;> norm_num⟩

/-- Positive half-height. -/
def heathBrownHalfHeight (T : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(T : ℝ) / (2 : ℝ),
    div_pos T.property (show (0 : ℝ) < 2 by norm_num)⟩

/-- Total lift from natural numbers to positive naturals; it is the identity on positive inputs. -/
def heathBrownPositivePart (n : ℕ) : ℕ+ :=
  ⟨max 1 n, lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 n)⟩

@[simp]
theorem coe_heathBrownPositivePart_of_pos {n : ℕ} (hn : 1 ≤ n) :
    (heathBrownPositivePart n : ℕ) = n := by
  simp [heathBrownPositivePart, max_eq_right hn]

/-- Full positive interval through `N`. -/
def heathBrownPositiveInterval (N : ℕ) (hN : 1 ≤ N) : Finset ℕ+ :=
  Finset.Icc 1 ⟨N, Nat.zero_lt_of_lt hN⟩

theorem heathBrownPositivePart_mem_positiveInterval {n N : ℕ} (hN : 1 ≤ N)
    (hn : n ∈ Finset.Icc 1 N) :
    heathBrownPositivePart n ∈ heathBrownPositiveInterval N hN := by
  rw [heathBrownPositiveInterval, Finset.mem_Icc]
  have hn' := Finset.mem_Icc.mp hn
  constructor
  · change (1 : ℕ) ≤ (heathBrownPositivePart n : ℕ)
    simpa [coe_heathBrownPositivePart_of_pos hn'.1] using hn'.1
  · change (heathBrownPositivePart n : ℕ) ≤ N
    simpa [coe_heathBrownPositivePart_of_pos hn'.1] using hn'.2

/-- The unit-weight collision sum is exactly the strict collision cardinality. -/
theorem heathBrownPositiveWeightedCollision_unit_eq_card
    (A B : Finset ℕ+) (T : Set.Ioi (0 : ℝ)) :
    heathBrownPositiveWeightedCollision A B heathBrownDenseUnitWeight T =
      (#(heathBrownPositiveStrictCollisionFinset A B ((T : ℝ)⁻¹)) : ℝ) := by
  let S := A.product B
  let P : (ℕ+ × ℕ+) × (ℕ+ × ℕ+) → Prop := fun z =>
    |Real.log (((z.1.1 : ℕ) * (z.1.2 : ℕ) : ℕ) : ℝ) -
      Real.log (((z.2.1 : ℕ) * (z.2.2 : ℕ) : ℕ) : ℝ)| < ((T : ℝ)⁻¹)
  let f : (ℕ+ × ℕ+) × (ℕ+ × ℕ+) → ℝ := fun z => if P z then 1 else 0
  rw [heathBrownPositiveWeightedCollision]
  simp only [heathBrownDenseUnitWeight, one_mul]
  calc
    (∑ p ∈ S, ∑ r ∈ S, if P (p, r) then (1 : ℝ) else 0) =
        ∑ z ∈ S.product S, f z := (Finset.sum_product S S f).symm
    _ = (#((S.product S).filter P) : ℝ) := by rw [Finset.sum_boole]
    _ = (#(heathBrownPositiveStrictCollisionFinset A B ((T : ℝ)⁻¹)) : ℝ) := by
      rfl

/-- A closed full-square collision at height `T` is a strict collision at half-height. -/
theorem card_heathBrownPositiveProductLogCollisionAggregate_le_halfHeightStrict
    (A : Finset ℕ+) (T : Set.Ioi (0 : ℝ)) {N : ℕ} (hN : 1 ≤ N) :
    heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) ≤
      #(heathBrownPositiveStrictCollisionFinset A (heathBrownPositiveInterval N hN)
          ((heathBrownHalfHeight T : ℝ)⁻¹)) := by
  let f : ((ℕ+ × ℕ) × (ℕ+ × ℕ)) → ((ℕ+ × ℕ+) × (ℕ+ × ℕ+)) := fun z =>
    ((z.1.1, heathBrownPositivePart z.1.2),
      (z.2.1, heathBrownPositivePart z.2.2))
  let C := heathBrownPositiveProductLogCollisionAggregateFinset A N ((T : ℝ)⁻¹)
  have hinj : Set.InjOn f (C : Set ((ℕ+ × ℕ) × (ℕ+ × ℕ))) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxmem := Finset.mem_product.mp hx'.1
    have hymem := Finset.mem_product.mp hy'.1
    have hx1 := Finset.mem_product.mp hxmem.1
    have hx2 := Finset.mem_product.mp hxmem.2
    have hy1 := Finset.mem_product.mp hymem.1
    have hy2 := Finset.mem_product.mp hymem.2
    have hxn1 := (Finset.mem_Icc.mp hx1.2).1
    have hxn2 := (Finset.mem_Icc.mp hx2.2).1
    have hyn1 := (Finset.mem_Icc.mp hy1.2).1
    have hyn2 := (Finset.mem_Icc.mp hy2.2).1
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z => z.1.1) hxy
      · have hp := congrArg (fun z => (z.1.2 : ℕ)) hxy
        simpa [f, coe_heathBrownPositivePart_of_pos hxn1,
          coe_heathBrownPositivePart_of_pos hyn1] using hp
    · apply Prod.ext
      · exact congrArg (fun z => z.2.1) hxy
      · have hp := congrArg (fun z => (z.2.2 : ℕ)) hxy
        simpa [f, coe_heathBrownPositivePart_of_pos hxn2,
          coe_heathBrownPositivePart_of_pos hyn2] using hp
  have hsub : C.image f ⊆
      heathBrownPositiveStrictCollisionFinset A (heathBrownPositiveInterval N hN)
        ((heathBrownHalfHeight T : ℝ)⁻¹) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hx' := Finset.mem_filter.mp hx
    have hxmem := Finset.mem_product.mp hx'.1
    have hx1 := Finset.mem_product.mp hxmem.1
    have hx2 := Finset.mem_product.mp hxmem.2
    have hxn1 := (Finset.mem_Icc.mp hx1.2).1
    have hxn2 := (Finset.mem_Icc.mp hx2.2).1
    rw [heathBrownPositiveStrictCollisionFinset]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨hx1.1, heathBrownPositivePart_mem_positiveInterval hN hx1.2⟩
    · exact Finset.mem_product.mpr
        ⟨hx2.1, heathBrownPositivePart_mem_positiveInterval hN hx2.2⟩
    · have hhalfInv : ((T : ℝ) / 2)⁻¹ = 2 * (T : ℝ)⁻¹ := by
        have hTpos : (0 : ℝ) < (T : ℝ) := T.property
        field_simp [ne_of_gt hTpos]
      have hinv : (T : ℝ)⁻¹ < ((T : ℝ) / 2)⁻¹ := by
        rw [hhalfInv]
        have hpos : 0 < (T : ℝ)⁻¹ := inv_pos.mpr T.property
        linarith
      simpa [f, heathBrownHalfHeight,
        coe_heathBrownPositivePart_of_pos hxn1,
        coe_heathBrownPositivePart_of_pos hxn2] using hx'.2.trans_lt hinv
  calc
    heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) = #C :=
      (card_heathBrownPositiveProductLogCollisionAggregateFinset A N ((T : ℝ)⁻¹)).symm
    _ = #(C.image f) := (Finset.card_image_of_injOn hinj).symm
    _ ≤ #(heathBrownPositiveStrictCollisionFinset A (heathBrownPositiveInterval N hN)
          ((heathBrownHalfHeight T : ℝ)⁻¹)) := Finset.card_le_card hsub

/-- Closed full-square aggregate is bounded by the unit-weight collision mass at half-height. -/
theorem cast_heathBrownPositiveProductLogCollisionAggregate_le_halfHeightCollision
    (A : Finset ℕ+) (T : Set.Ioi (0 : ℝ)) {N : ℕ} (hN : 1 ≤ N) :
    (heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) : ℝ) ≤
      heathBrownPositiveWeightedCollision A (heathBrownPositiveInterval N hN)
        heathBrownDenseUnitWeight (heathBrownHalfHeight T) := by
  rw [heathBrownPositiveWeightedCollision_unit_eq_card]
  exact_mod_cast
    card_heathBrownPositiveProductLogCollisionAggregate_le_halfHeightStrict A T hN

/-- Reverse mean-value closure of the smaller Heath--Brown collision aggregate. -/
theorem cast_heathBrownPositiveProductLogCollisionAggregate_le_halfHeightIntegral
    (A : Finset ℕ+) (T : Set.Ioi (0 : ℝ)) {N : ℕ} (hN : 1 ≤ N) :
    (heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) : ℝ) ≤
      (5 / (2 * (T : ℝ))) *
        ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ)) (heathBrownHalfHeight T : ℝ),
          ‖heathBrownSparseFactor A (fun _ => 1) t *
            heathBrownDenseFactor (heathBrownPositiveInterval N hN)
              heathBrownDenseUnitWeight t‖ ^ 2 := by
  calc
    (heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) : ℝ) ≤
        heathBrownPositiveWeightedCollision A (heathBrownPositiveInterval N hN)
          heathBrownDenseUnitWeight (heathBrownHalfHeight T) :=
      cast_heathBrownPositiveProductLogCollisionAggregate_le_halfHeightCollision A T hN
    _ ≤ (5 / (4 * (heathBrownHalfHeight T : ℝ))) *
        ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ)) (heathBrownHalfHeight T : ℝ),
          ‖heathBrownSparseFactor A (fun _ => 1) t *
            heathBrownDenseFactor (heathBrownPositiveInterval N hN)
              heathBrownDenseUnitWeight t‖ ^ 2 :=
      heathBrownPositiveWeightedCollision_le_integral_Icc_factors
        A (heathBrownPositiveInterval N hN) heathBrownDenseUnitWeight
          (heathBrownHalfHeight T)
    _ = (5 / (2 * (T : ℝ))) *
        ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ)) (heathBrownHalfHeight T : ℝ),
          ‖heathBrownSparseFactor A (fun _ => 1) t *
            heathBrownDenseFactor (heathBrownPositiveInterval N hN)
              heathBrownDenseUnitWeight t‖ ^ 2 := by
      have hcoef : 5 / (4 * ((T : ℝ) / 2)) = 5 / (2 * (T : ℝ)) := by
        have hTpos : (0 : ℝ) < (T : ℝ) := T.property
        field_simp [ne_of_gt hTpos]
        ring
      rw [show (heathBrownHalfHeight T : ℝ) = (T : ℝ) / 2 by rfl, hcoef]

/-- Fully integral form of the Heath--Brown two-scale sparse mean-value inequality. -/
theorem integral_Icc_normSq_heathBrown_factors_le_twoScaleIntegral
    (A B : Finset ℕ+) (ε : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {N N0 : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    (hN0 : 1 ≤ N0) (hN0N : N0 ≤ N) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          ((N / N0 + 1 : ℕ) : ℝ) *
            ((5 / (2 * (T : ℝ))) *
              ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
                  (heathBrownHalfHeight T : ℝ),
                ‖heathBrownSparseFactor A (fun _ => 1) t *
                  heathBrownDenseFactor (heathBrownPositiveInterval N0 hN0)
                    heathBrownDenseUnitWeight t‖ ^ 2) +
          ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2) := by
  calc
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          ((N / N0 + 1 : ℕ) : ℝ) *
            (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
          ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2) :=
      integral_Icc_normSq_heathBrown_factors_le_twoScaleAggregate
        A B ε q T hT hB hN0 hN0N
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
        (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          ((N / N0 + 1 : ℕ) : ℝ) *
            ((5 / (2 * (T : ℝ))) *
              ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
                  (heathBrownHalfHeight T : ℝ),
                ‖heathBrownSparseFactor A (fun _ => 1) t *
                  heathBrownDenseFactor (heathBrownPositiveInterval N0 hN0)
                    heathBrownDenseUnitWeight t‖ ^ 2) +
          ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2) := by
      gcongr
      exact cast_heathBrownPositiveProductLogCollisionAggregate_le_halfHeightIntegral
        A T hN0

end

end RHTower.Sieve
