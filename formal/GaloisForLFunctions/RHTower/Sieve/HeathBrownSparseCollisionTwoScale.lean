import GaloisForLFunctions.RHTower.Sieve.HeathBrownPositiveCollisionRayReindex
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueReverse

/-!
# Heath--Brown sparse collision two-scale assembly

The literal closed collision-square count is summed over every ordered sparse cofactor pair.  The
result is the finite two-scale comparison underlying Heath--Brown Theorem 4(iii).  A final bridge
dominates the corpus's existing `[0,1]` coefficient-weighted strict collision mass by this closed
aggregate on any bounded dense support.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Closed dense collision-square count summed over all ordered sparse cofactor pairs. -/
def heathBrownPositiveProductLogCollisionAggregate
    (A : Finset ℕ+) (N : ℕ) (delta : ℝ) : ℕ :=
  ∑ m1 ∈ A, ∑ m2 ∈ A,
    #(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta)

/-- **Heath--Brown aggregate two-scale collision inequality.** -/
theorem cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale
    (A : Finset ℕ+) {N N0 : ℕ} (hN0 : 1 ≤ N0) (hN0N : N0 ≤ N)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (heathBrownPositiveProductLogCollisionAggregate A N delta : ℝ) ≤
      15 * delta * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
        ((N / N0 + 1 : ℕ) : ℝ) *
          (heathBrownPositiveProductLogCollisionAggregate A N0 delta : ℝ) +
        ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ (2 : ℕ) := by
  unfold heathBrownPositiveProductLogCollisionAggregate
  push_cast
  calc
    ∑ m1 ∈ A, ∑ m2 ∈ A,
        (#(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta) : ℝ) ≤
      ∑ m1 ∈ A, ∑ m2 ∈ A,
        (15 * delta * (N : ℝ) ^ (2 : ℕ) +
          (((N / N0 : ℕ) : ℝ) + 1) *
            (#(heathBrownPositiveProductLogCollisionSquare N0 m1 m2 delta) : ℝ) +
          (2 * ((N / N0 : ℕ) : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro m1 hm1
      apply Finset.sum_le_sum
      intro m2 hm2
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using
        (cast_card_heathBrownPositiveProductLogCollisionSquare_le_twoScale
          hN0 hN0N m1 m2 hdelta0 hdelta1)
    _ = 15 * delta * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
        (((N / N0 : ℕ) : ℝ) + 1) *
          (∑ m1 ∈ A, ∑ m2 ∈ A,
            (#(heathBrownPositiveProductLogCollisionSquare N0 m1 m2 delta) : ℝ)) +
        (2 * ((N / N0 : ℕ) : ℝ) + 1) * (A.card : ℝ) ^ (2 : ℕ) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      simp_rw [← Finset.mul_sum]
      ring

/-- Single finite set underlying the closed aggregate count. -/
def heathBrownPositiveProductLogCollisionAggregateFinset
    (A : Finset ℕ+) (N : ℕ) (delta : ℝ) :
    Finset ((ℕ+ × ℕ) × (ℕ+ × ℕ)) :=
  ((A.product (Finset.Icc 1 N)).product (A.product (Finset.Icc 1 N))).filter fun z =>
    |Real.log (((z.1.1 : ℕ) * z.1.2 : ℕ) : ℝ) -
      Real.log (((z.2.1 : ℕ) * z.2.2 : ℕ) : ℝ)| ≤ delta

theorem sum_indicator_heathBrownPositiveProductLogCollisionSquare_eq_card
    (N : ℕ) (m1 m2 : ℕ+) (delta : ℝ) :
    (∑ y ∈ Finset.Icc 1 N, ∑ y_1 ∈ Finset.Icc 1 N,
      if |Real.log (((m1 : ℕ) * y : ℕ) : ℝ) -
          Real.log (((m2 : ℕ) * y_1 : ℕ) : ℝ)| ≤ delta then 1 else 0) =
      #(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta) := by
  let I := Finset.Icc 1 N
  let P : ℕ × ℕ → Prop := fun p =>
    |Real.log (((m1 : ℕ) * p.1 : ℕ) : ℝ) -
      Real.log (((m2 : ℕ) * p.2 : ℕ) : ℝ)| ≤ delta
  have hprod :
      (∑ p ∈ I.product I, if P p then 1 else 0) =
        ∑ y ∈ I, ∑ y_1 ∈ I, if P (y, y_1) then 1 else 0 :=
    Finset.sum_product I I (fun p => if P p then 1 else 0)
  change (∑ y ∈ I, ∑ y_1 ∈ I, if P (y, y_1) then 1 else 0) = _
  rw [← hprod, ← Finset.sum_filter]
  simp [heathBrownPositiveProductLogCollisionSquare, I, P]

/-- The single-set and iterated cofactor-pair presentations of the aggregate agree. -/
theorem card_heathBrownPositiveProductLogCollisionAggregateFinset
    (A : Finset ℕ+) (N : ℕ) (delta : ℝ) :
    #(heathBrownPositiveProductLogCollisionAggregateFinset A N delta) =
      heathBrownPositiveProductLogCollisionAggregate A N delta := by
  let B := A.product (Finset.Icc 1 N)
  let f : ((ℕ+ × ℕ) × (ℕ+ × ℕ)) → ℕ := fun z =>
    if |Real.log (((z.1.1 : ℕ) * z.1.2 : ℕ) : ℝ) -
      Real.log (((z.2.1 : ℕ) * z.2.2 : ℕ) : ℝ)| ≤ delta then 1 else 0
  have houter :
      Finset.sum (B.product B) f =
        Finset.sum B (fun p => Finset.sum B fun r => f (p, r)) :=
    Finset.sum_product B B f
  have hexpand :
      Finset.sum B (fun p => Finset.sum B fun r => f (p, r)) =
        ∑ x ∈ A, ∑ y ∈ Finset.Icc 1 N, ∑ x_1 ∈ A, ∑ y_1 ∈ Finset.Icc 1 N,
          f ((x, y), (x_1, y_1)) := by
    dsimp [B]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.sum_product]
  have hreorder : (∑ x ∈ A, ∑ y ∈ Finset.Icc 1 N, ∑ x_1 ∈ A, ∑ y_1 ∈ Finset.Icc 1 N,
      if |Real.log (((x : ℕ) * y : ℕ) : ℝ) -
          Real.log (((x_1 : ℕ) * y_1 : ℕ) : ℝ)| ≤ delta then 1 else 0) =
      ∑ x ∈ A, ∑ x_1 ∈ A, ∑ y ∈ Finset.Icc 1 N, ∑ y_1 ∈ Finset.Icc 1 N,
      if |Real.log (((x : ℕ) * y : ℕ) : ℝ) -
          Real.log (((x_1 : ℕ) * y_1 : ℕ) : ℝ)| ≤ delta then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
  calc
    #(heathBrownPositiveProductLogCollisionAggregateFinset A N delta) =
        Finset.sum ((B.product B).filter fun z => f z = 1) (fun _ => 1) := by
      simp [heathBrownPositiveProductLogCollisionAggregateFinset, B, f]
    _ = Finset.sum (B.product B) f := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z hz
      dsimp [f]
      split <;> simp_all
    _ = Finset.sum B (fun p => Finset.sum B fun r => f (p, r)) := houter
    _ = ∑ x ∈ A, ∑ y ∈ Finset.Icc 1 N, ∑ x_1 ∈ A, ∑ y_1 ∈ Finset.Icc 1 N,
          f ((x, y), (x_1, y_1)) := hexpand
    _ = ∑ x ∈ A, ∑ x_1 ∈ A, ∑ y ∈ Finset.Icc 1 N, ∑ y_1 ∈ Finset.Icc 1 N,
        if |Real.log (((x : ℕ) * y : ℕ) : ℝ) -
            Real.log (((x_1 : ℕ) * y_1 : ℕ) : ℝ)| ≤ delta then 1 else 0 := by
      dsimp [f]
      exact hreorder
    _ = heathBrownPositiveProductLogCollisionAggregate A N delta := by
      rw [heathBrownPositiveProductLogCollisionAggregate]
      apply Finset.sum_congr rfl
      intro m1 hm1
      apply Finset.sum_congr rfl
      intro m2 hm2
      exact sum_indicator_heathBrownPositiveProductLogCollisionSquare_eq_card N m1 m2 delta

/-- Strict near-product collisions on arbitrary sparse and dense positive supports. -/
def heathBrownPositiveStrictCollisionFinset
    (A B : Finset ℕ+) (delta : ℝ) : Finset ((ℕ+ × ℕ+) × (ℕ+ × ℕ+)) :=
  ((A.product B).product (A.product B)).filter fun z =>
    |Real.log (((z.1.1 : ℕ) * (z.1.2 : ℕ) : ℕ) : ℝ) -
      Real.log (((z.2.1 : ℕ) * (z.2.2 : ℕ) : ℕ) : ℝ)| < delta

/-- `[0,1]` coefficient weights are bounded by the literal strict collision count. -/
theorem heathBrownPositiveWeightedCollision_le_card_strictCollision
    (A B : Finset ℕ+) (q : ℕ → Set.Icc (0 : ℝ) 1) (T : Set.Ioi (0 : ℝ)) :
    heathBrownPositiveWeightedCollision A B q T ≤
      (#(heathBrownPositiveStrictCollisionFinset A B ((T : ℝ)⁻¹)) : ℝ) := by
  let S := A.product B
  let P : (ℕ+ × ℕ+) × (ℕ+ × ℕ+) → Prop := fun z =>
    |Real.log (((z.1.1 : ℕ) * (z.1.2 : ℕ) : ℕ) : ℝ) -
      Real.log (((z.2.1 : ℕ) * (z.2.2 : ℕ) : ℕ) : ℝ)| < ((T : ℝ)⁻¹)
  let w : (ℕ+ × ℕ+) × (ℕ+ × ℕ+) → ℝ := fun z =>
    (q (z.1.2 : ℕ) : ℝ) * (q (z.2.2 : ℕ) : ℝ)
  have hprod :
      (∑ z ∈ S.product S, if P z then w z else 0) =
        ∑ p ∈ S, ∑ r ∈ S, if P (p, r) then w (p, r) else 0 :=
    Finset.sum_product S S (fun z => if P z then w z else 0)
  rw [heathBrownPositiveWeightedCollision]
  change (∑ p ∈ S, ∑ r ∈ S, if P (p, r) then w (p, r) else 0) ≤ _
  rw [← hprod, ← Finset.sum_filter]
  change (∑ z ∈ heathBrownPositiveStrictCollisionFinset A B ((T : ℝ)⁻¹), w z) ≤ _
  calc
    (∑ z ∈ heathBrownPositiveStrictCollisionFinset A B ((T : ℝ)⁻¹), w z) ≤
        ∑ z ∈ heathBrownPositiveStrictCollisionFinset A B ((T : ℝ)⁻¹), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      dsimp [w]
      have hq1 := (q (z.1.2 : ℕ)).property
      have hq2 := (q (z.2.2 : ℕ)).property
      exact (mul_le_mul_of_nonneg_right hq1.2 hq2.1).trans (by simpa using hq2.2)
    _ = (#(heathBrownPositiveStrictCollisionFinset A B ((T : ℝ)⁻¹)) : ℝ) := by simp

/-- A bounded dense support embeds every strict collision into the closed full-square aggregate. -/
theorem card_heathBrownPositiveStrictCollisionFinset_le_aggregate
    (A B : Finset ℕ+) {N : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N) (delta : ℝ) :
    #(heathBrownPositiveStrictCollisionFinset A B delta) ≤
      heathBrownPositiveProductLogCollisionAggregate A N delta := by
  let f : ((ℕ+ × ℕ+) × (ℕ+ × ℕ+)) → ((ℕ+ × ℕ) × (ℕ+ × ℕ)) := fun z =>
    ((z.1.1, (z.1.2 : ℕ)), (z.2.1, (z.2.2 : ℕ)))
  have hinj : Set.InjOn f
      (heathBrownPositiveStrictCollisionFinset A B delta :
        Set ((ℕ+ × ℕ+) × (ℕ+ × ℕ+))) := by
    intro x hx y hy hxy
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z => z.1.1) hxy
      · apply PNat.eq
        exact congrArg (fun z => z.1.2) hxy
    · apply Prod.ext
      · exact congrArg (fun z => z.2.1) hxy
      · apply PNat.eq
        exact congrArg (fun z => z.2.2) hxy
  have hsub : (heathBrownPositiveStrictCollisionFinset A B delta).image f ⊆
      heathBrownPositiveProductLogCollisionAggregateFinset A N delta := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hx' := Finset.mem_filter.mp hx
    have hxmem := Finset.mem_product.mp hx'.1
    have hx1 := Finset.mem_product.mp hxmem.1
    have hx2 := Finset.mem_product.mp hxmem.2
    rw [heathBrownPositiveProductLogCollisionAggregateFinset]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨hx1.1, Finset.mem_Icc.mpr ⟨x.1.2.pos, hB x.1.2 hx1.2⟩⟩
    · exact Finset.mem_product.mpr
        ⟨hx2.1, Finset.mem_Icc.mpr ⟨x.2.2.pos, hB x.2.2 hx2.2⟩⟩
    · exact hx'.2.le
  calc
    #(heathBrownPositiveStrictCollisionFinset A B delta) =
        #((heathBrownPositiveStrictCollisionFinset A B delta).image f) :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ #(heathBrownPositiveProductLogCollisionAggregateFinset A N delta) :=
      Finset.card_le_card hsub
    _ = heathBrownPositiveProductLogCollisionAggregate A N delta :=
      card_heathBrownPositiveProductLogCollisionAggregateFinset A N delta

/-- Existing weighted collision mass is bounded by the closed aggregate on any bounded support. -/
theorem heathBrownPositiveWeightedCollision_le_collisionAggregate
    (A B : Finset ℕ+) (q : ℕ → Set.Icc (0 : ℝ) 1) (T : Set.Ioi (0 : ℝ))
    {N : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N) :
    heathBrownPositiveWeightedCollision A B q T ≤
      (heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) : ℝ) := by
  exact (heathBrownPositiveWeightedCollision_le_card_strictCollision A B q T).trans
    (by
      exact_mod_cast (card_heathBrownPositiveStrictCollisionFinset_le_aggregate
        A B hB ((T : ℝ)⁻¹)))

/-- Height-specialized aggregate inequality; logarithmic-window hypotheses are discharged from
`1 ≤ T`. -/
theorem cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale_inv
    (A : Finset ℕ+) (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {N N0 : ℕ} (hN0 : 1 ≤ N0) (hN0N : N0 ≤ N) :
    (heathBrownPositiveProductLogCollisionAggregate A N ((T : ℝ)⁻¹) : ℝ) ≤
      15 * (T : ℝ)⁻¹ * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
        ((N / N0 + 1 : ℕ) : ℝ) *
          (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
        ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ (2 : ℕ) := by
  apply cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale A hN0 hN0N
  · exact inv_pos.mpr T.property
  · exact (inv_le_one₀ T.property).mpr hT

/-- **Weighted Heath--Brown sparse collision comparison.**  Existing `[0,1]`-weighted strict
collision mass is bounded by the explicit two-scale closed collision aggregate. -/
theorem heathBrownPositiveWeightedCollision_le_twoScaleAggregate
    (A B : Finset ℕ+) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {N N0 : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    (hN0 : 1 ≤ N0) (hN0N : N0 ≤ N) :
    heathBrownPositiveWeightedCollision A B q T ≤
      15 * (T : ℝ)⁻¹ * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
        ((N / N0 + 1 : ℕ) : ℝ) *
          (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
        ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ (2 : ℕ) := by
  exact (heathBrownPositiveWeightedCollision_le_collisionAggregate A B q T hB).trans
    (cast_heathBrownPositiveProductLogCollisionAggregate_le_twoScale_inv
      A T hT hN0 hN0N)

/-- **Source-facing Heath--Brown two-scale sparse mean-value bound.**  The exact finite product
integral is controlled by the closed smaller-scale collision aggregate, with no analytic,
lattice, exceptional-direction, or coefficient hypothesis. -/
theorem integral_Icc_normSq_heathBrown_factors_le_twoScaleAggregate
    (A B : Finset ℕ+) (ε : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {N N0 : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    (hN0 : 1 ≤ N0) (hN0N : N0 ≤ N) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t‖ ^ (2 : ℕ)) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
          ((N / N0 + 1 : ℕ) : ℝ) *
            (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
          ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ (2 : ℕ)) := by
  calc
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t‖ ^ (2 : ℕ)) ≤
      (5 * Real.pi / 2) * (T : ℝ) *
        heathBrownPositiveWeightedCollision A B q T :=
      integral_Icc_normSq_heathBrown_factors_le_weightedCollision A B ε q T
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
        (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
          ((N / N0 + 1 : ℕ) : ℝ) *
            (heathBrownPositiveProductLogCollisionAggregate A N0 ((T : ℝ)⁻¹) : ℝ) +
          ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left
        (heathBrownPositiveWeightedCollision_le_twoScaleAggregate
          A B q T hT hB hN0 hN0N) (by positivity)

end


end RHTower.Sieve
