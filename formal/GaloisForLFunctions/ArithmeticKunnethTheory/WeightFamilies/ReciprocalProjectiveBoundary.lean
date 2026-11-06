import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.ReciprocalTorusSingularities

/-!
# The coordinate boundary of the projective reciprocal locus

Clearing denominators gives the homogeneous equation `∑ᵢ ∏ⱼ≠ᵢ xⱼ = 0`.
Its formal line expansion separates the boundary strata: one zero coordinate
cannot occur, two zeros give a nonzero transverse linear term, and three zeros
annihilate every linear term. In the torus its differential agrees with that of
the reciprocal equation, up to the invertible product of the coordinates.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {K ι : Type*} [Field K] [DecidableEq ι]

/-- A coordinate restricted to a formal line. -/
def torusLineFactor (x v : K) : PowerSeries K := PowerSeries.C x + PowerSeries.C v * PowerSeries.X

private theorem line_product_linear_of_zero (s : Finset ι) (x v : ι → K)
    {a : ι} (ha : a ∈ s) (hxa : x a = 0) :
    PowerSeries.coeff 1 (∏ j ∈ s, torusLineFactor (x j) (v j)) =
      v a * ∏ j ∈ s.erase a, x j := by
  rw [← mul_prod_erase s (fun j => torusLineFactor (x j) (v j)) ha,
    PowerSeries.coeff_one_mul]
  simp [torusLineFactor, hxa]

private theorem line_product_linear_of_two_zeros (s : Finset ι) (x v : ι → K)
    {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hxa : x a = 0) (hxb : x b = 0) :
    PowerSeries.coeff 1 (∏ j ∈ s, torusLineFactor (x j) (v j)) = 0 := by
  rw [line_product_linear_of_zero s x v ha hxa]
  have hz : (∏ j ∈ s.erase a, x j) = 0 :=
    prod_eq_zero (mem_erase.mpr ⟨hab.symm, hb⟩) hxb
  rw [hz, mul_zero]

variable [Fintype ι]

/-- The homogeneous polynomial obtained by clearing the reciprocal denominators. -/
def reciprocalClearedValue (x : ι → K) : K := ∑ i, ∏ j ∈ univ.erase i, x j

/-- The cleared equation restricted to a formal line. -/
def reciprocalClearedSeries (x v : ι → K) : PowerSeries K :=
  ∑ i, ∏ j ∈ univ.erase i, torusLineFactor (x j) (v j)

theorem reciprocalClearedSeries_constant (x v : ι → K) :
    PowerSeries.constantCoeff (reciprocalClearedSeries x v) = reciprocalClearedValue x := by
  simp [reciprocalClearedSeries, reciprocalClearedValue, torusLineFactor]

/-- On the torus, clearing denominators is an exact identity of formal series. -/
theorem reciprocalClearedSeries_eq (x v : ι → K) (hx : ∀ i, x i ≠ 0) :
    reciprocalClearedSeries x v =
      (∏ i, torusLineFactor (x i) (v i)) * reciprocalSeries x v := by
  rw [reciprocalClearedSeries, reciprocalSeries, mul_sum]
  apply sum_congr rfl
  intro i _
  symm
  rw [← prod_erase_mul univ (fun j => torusLineFactor (x j) (v j)) (mem_univ i),
    mul_assoc]
  change (∏ j ∈ univ.erase i, torusLineFactor (x j) (v j)) *
    ((PowerSeries.C (x i) + PowerSeries.C (v i) * PowerSeries.X) *
      reciprocalLineInverse (x i) (v i)) = _
  rw [reciprocalLineInverse_mul _ _ (hx i), mul_one]

/-- At a torus point on the reciprocal locus, the cleared differential is the
reciprocal differential times the nonzero coordinate product. -/
theorem reciprocalClearedSeries_linear (x v : ι → K) (hx : ∀ i, x i ≠ 0)
    (hr : (∑ i, (x i)⁻¹) = 0) :
    PowerSeries.coeff 1 (reciprocalClearedSeries x v) =
      (∏ i, x i) * reciprocalLinear x v := by
  have hc : PowerSeries.constantCoeff (reciprocalSeries x v) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, reciprocalSeries_constant, hr]
  rw [reciprocalClearedSeries_eq x v hx, PowerSeries.coeff_one_mul, hc,
    reciprocalSeries_linear, mul_zero, zero_add]
  simp only [map_prod, torusLineFactor, map_add, map_mul,
    PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, mul_zero, add_zero]
  exact mul_comm _ _

/-- With one zero coordinate, the cleared equation is the product of the remaining coordinates. -/
theorem reciprocalClearedValue_of_zero (x : ι → K) {a : ι} (ha : x a = 0) :
    reciprocalClearedValue x = ∏ j ∈ univ.erase a, x j := by
  apply sum_eq_single a
  · intro b _ hba
    exact prod_eq_zero (mem_erase.mpr ⟨hba.symm, mem_univ a⟩) ha
  · simp

/-- Exactly one zero coordinate is excluded from the cleared zero locus. -/
theorem reciprocalClearedValue_ne_zero_of_one_zero (x : ι → K) {a : ι}
    (ha : x a = 0) (hx : ∀ i, i ≠ a → x i ≠ 0) : reciprocalClearedValue x ≠ 0 := by
  rw [reciprocalClearedValue_of_zero x ha]
  exact prod_ne_zero_iff.mpr (fun i hi => hx i (mem_erase.mp hi).1)

/-- Every point with two zero coordinates satisfies the cleared equation. -/
theorem reciprocalClearedValue_of_two_zeros (x : ι → K) {a b : ι}
    (hab : a ≠ b) (ha : x a = 0) (hb : x b = 0) : reciprocalClearedValue x = 0 := by
  rw [reciprocalClearedValue_of_zero x ha]
  exact prod_eq_zero (mem_erase.mpr ⟨hab.symm, mem_univ b⟩) hb

/-- Two zero coordinates leave exactly two first-order monomials. -/
theorem reciprocalClearedSeries_linear_of_two_zeros (x v : ι → K) {a b : ι}
    (hab : a ≠ b) (ha : x a = 0) (hb : x b = 0) :
    PowerSeries.coeff 1 (reciprocalClearedSeries x v) =
      (v a + v b) * ∏ j ∈ (univ.erase a).erase b, x j := by
  let f : ι → K := fun i =>
    PowerSeries.coeff 1 (∏ j ∈ univ.erase i, torusLineFactor (x j) (v j))
  have hfa : f a = v b * ∏ j ∈ (univ.erase a).erase b, x j :=
    line_product_linear_of_zero _ x v (mem_erase.mpr ⟨hab.symm, mem_univ b⟩) hb
  have hfb : f b = v a * ∏ j ∈ (univ.erase a).erase b, x j := by
    dsimp only [f]
    rw [line_product_linear_of_zero _ x v (mem_erase.mpr ⟨hab, mem_univ a⟩) ha]
    have he : ((univ : Finset ι).erase b).erase a = (univ.erase a).erase b := by
      ext j
      simp only [mem_erase]
      constructor
      · rintro ⟨hja, hjb, hj⟩
        exact ⟨hjb, hja, hj⟩
      · rintro ⟨hjb, hja, hj⟩
        exact ⟨hja, hjb, hj⟩
    rw [he]
  have hz : ∀ i, i ≠ a → i ≠ b → f i = 0 := by
    intro i hia hib
    exact line_product_linear_of_two_zeros _ x v
      (mem_erase.mpr ⟨hia.symm, mem_univ a⟩)
      (mem_erase.mpr ⟨hib.symm, mem_univ b⟩) hab ha hb
  have hrest : ∑ i ∈ univ.erase a, f i = f b := by
    apply sum_eq_single b
    · intro i hi hib
      exact hz i (mem_erase.mp hi).1 hib
    · simp [hab.symm]
  have hsum := sum_erase_add univ f (mem_univ a)
  rw [hrest, hfa, hfb] at hsum
  change PowerSeries.coeff 1 (∑ i, _) = _
  rw [map_sum]
  change (∑ i, f i) = _
  rw [← hsum]
  ring

/-- Three zero coordinates kill the entire first-order part of the cleared equation. -/
theorem reciprocalClearedSeries_linear_of_three_zeros (x v : ι → K) {a b c : ι}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : x a = 0) (hb : x b = 0) (hc : x c = 0) :
    PowerSeries.coeff 1 (reciprocalClearedSeries x v) = 0 := by
  rw [reciprocalClearedSeries, map_sum]
  apply sum_eq_zero
  intro i _
  by_cases hia : i = a
  · subst i
    exact line_product_linear_of_two_zeros _ x v
      (mem_erase.mpr ⟨hab.symm, mem_univ b⟩)
      (mem_erase.mpr ⟨hac.symm, mem_univ c⟩) hbc hb hc
  · by_cases hib : i = b
    · subst i
      exact line_product_linear_of_two_zeros _ x v
        (mem_erase.mpr ⟨hab, mem_univ a⟩)
        (mem_erase.mpr ⟨hbc.symm, mem_univ c⟩) hac ha hc
    · exact line_product_linear_of_two_zeros _ x v
        (mem_erase.mpr ⟨Ne.symm hia, mem_univ a⟩)
        (mem_erase.mpr ⟨Ne.symm hib, mem_univ b⟩) hab ha hb

/-- At a nonzero point with exactly two zero coordinates, the cleared equation
has a nonzero differential even after restriction to the sum-zero hyperplane. -/
theorem reciprocalClearedSeries_transverse_of_two_zeros (x : ι → K) {a b c : ι}
    (hab : a ≠ b) (ha : x a = 0) (hb : x b = 0) (hc : x c ≠ 0)
    (hx : ∀ i, i ≠ a → i ≠ b → x i ≠ 0) :
    ∃ v : ι → K, (∑ i, v i) = 0 ∧
      PowerSeries.coeff 1 (reciprocalClearedSeries x v) ≠ 0 := by
  have hca : c ≠ a := by intro h; exact hc (h.symm ▸ ha)
  have hcb : c ≠ b := by intro h; exact hc (h.symm ▸ hb)
  let v : ι → K := fun i => (if i = a then 1 else 0) - (if i = c then 1 else 0)
  refine ⟨v, by simp [v, sum_sub_distrib], ?_⟩
  rw [reciprocalClearedSeries_linear_of_two_zeros x v hab ha hb]
  have hv : v a + v b = 1 := by simp [v, hab.symm, hca.symm, hcb.symm]
  rw [hv, one_mul]
  exact prod_ne_zero_iff.mpr (fun i hi =>
    hx i (mem_erase.mp (mem_erase.mp hi).2).1 (mem_erase.mp hi).1)

/-- The coordinate boundary is critical precisely on strata with at least three
zero coordinates. This classifies differential rank, without a smoothness convention. -/
theorem reciprocalBoundary_critical_iff (x : ι → K)
    (hnonzero : ∃ c, x c ≠ 0) (hboundary : ∃ a, x a = 0)
    (hvalue : reciprocalClearedValue x = 0) :
    (∀ v : ι → K, (∑ i, v i) = 0 →
      PowerSeries.coeff 1 (reciprocalClearedSeries x v) = 0) ↔
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x a = 0 ∧ x b = 0 ∧ x c = 0 := by
  constructor
  · intro hcrit
    obtain ⟨a, ha⟩ := hboundary
    have hb : ∃ b, b ≠ a ∧ x b = 0 := by
      by_contra h
      have hx : ∀ i, i ≠ a → x i ≠ 0 := by
        intro i hia hi
        exact h ⟨i, hia, hi⟩
      exact reciprocalClearedValue_ne_zero_of_one_zero x ha hx hvalue
    obtain ⟨b, hba, hb⟩ := hb
    have hc : ∃ c, c ≠ a ∧ c ≠ b ∧ x c = 0 := by
      by_contra h
      have hx : ∀ i, i ≠ a → i ≠ b → x i ≠ 0 := by
        intro i hia hib hi
        exact h ⟨i, hia, hib, hi⟩
      obtain ⟨d, hd⟩ := hnonzero
      obtain ⟨v, hv, hne⟩ := reciprocalClearedSeries_transverse_of_two_zeros
        x hba.symm ha hb hd hx
      exact hne (hcrit v hv)
    obtain ⟨c, hca, hcb, hc⟩ := hc
    exact ⟨a, b, c, hba.symm, hca.symm, hcb.symm, ha, hb, hc⟩
  · rintro ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ v _
    exact reciprocalClearedSeries_linear_of_three_zeros x v hab hac hbc ha hb hc

/-- In the torus, the cleared polynomial has exactly the reciprocal equation's
critical locus. -/
theorem reciprocalCleared_torus_critical_iff (x : ι → K) (i₀ : ι)
    (hx : ∀ i, x i ≠ 0) (hr : (∑ i, (x i)⁻¹) = 0) :
    (∀ v : ι → K, (∑ i, v i) = 0 →
      PowerSeries.coeff 1 (reciprocalClearedSeries x v) = 0) ↔
      ∀ i, x i ^ 2 = x i₀ ^ 2 := by
  rw [← reciprocal_critical_iff x i₀]
  have hp : (∏ i, x i) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => hx i)
  constructor
  · intro h v hv
    have hlin := h v hv
    rw [reciprocalClearedSeries_linear x v hx hr] at hlin
    exact (mul_eq_zero.mp hlin).resolve_left hp
  · intro h v hv
    rw [reciprocalClearedSeries_linear x v hx hr, h v hv, mul_zero]

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
