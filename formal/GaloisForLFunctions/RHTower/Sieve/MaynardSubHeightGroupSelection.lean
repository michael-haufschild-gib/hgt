import GaloisForLFunctions.RHTower.Sieve.MaynardWitnessedSubHeightPacking
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicGreedyGroup

/-!
# Selected polynomial after removing over-height atoms

Over-height atoms are first removed using their individual amplitude bounds.  Every remaining
atom has logarithmic height exponent below `1`; arbitrary-cap greedy grouping then produces one
large literal group of mass in `[t,1+2t)`.  This is the selected-polynomial mechanism needed by
the global Route-T counts and does not assume every original factor is short.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Generic dyadic selected-polynomial theorem below the height. -/
theorem exists_dyadic_subHeight_large_group
    {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (z : ι → ℂ) {T t e : ℝ}
    (hT : 1 < T) (ht : 0 < t)
    (hsubTotal :
      t ≤ ∑ i ∈ (Finset.univ.filter fun i =>
        dyadicLogExponent T (q i) < 1), dyadicLogExponent T (q i))
    (hover : ∀ i, 1 ≤ dyadicLogExponent T (q i) →
      ‖z i‖ ≤ (((2 ^ q i : ℕ) : ℝ)) ^ e)
    (hlarge : (groupedDyadicLower q : ℝ) ^ e ≤ ‖∏ i, z i‖) :
    ∃ u : Finset ι, u.Nonempty ∧
      (∀ i ∈ u, dyadicLogExponent T (q i) < 1) ∧
      let beta := ∑ i ∈ u, dyadicLogExponent T (q i)
      t ≤ beta ∧ beta < 1 + 2 * t ∧
        ((groupedDyadicLower (fun i : {i // i ∈ u} => q i) : ℕ) : ℝ) =
          T ^ beta ∧
        ((groupedDyadicLower (fun i : {i // i ∈ u} => q i) : ℕ) : ℝ) ^ e ≤
          ‖∏ i : {i // i ∈ u}, z i‖ := by
  classical
  let good : Finset ι := Finset.univ.filter fun i =>
    dyadicLogExponent T (q i) < 1
  let A : ι → ℝ := fun i => (((2 ^ q i : ℕ) : ℝ))
  have hgood : good ⊆ (Finset.univ : Finset ι) := Finset.subset_univ _
  have hA : ∀ i ∈ (Finset.univ : Finset ι), 0 < A i := by
    intro i _
    dsimp only [A]
    positivity
  have hbad : ∀ i ∈ (Finset.univ : Finset ι) \ good,
      ‖z i‖ ≤ A i ^ e := by
    intro i hi
    apply hover i
    have hnot : ¬dyadicLogExponent T (q i) < 1 := by
      have hnotGood : i ∉ good := (Finset.mem_sdiff.mp hi).2
      simpa [good] using hnotGood
    exact le_of_not_gt hnot
  have hlarge' : (∏ i ∈ (Finset.univ : Finset ι), A i) ^ e ≤
      ‖∏ i ∈ (Finset.univ : Finset ι), z i‖ := by
    simpa [A, groupedDyadicLower] using hlarge
  have hgoodLarge := restricted_complex_product_large_of_complement_small
    (Finset.univ : Finset ι) good hgood A z e hA hbad hlarge'
  have hw : ∀ i ∈ good, dyadicLogExponent T (q i) ≤ 1 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.le
  obtain ⟨u, hune, hus, hulower, huupper, hgroup⟩ :=
    exists_bounded_greedy_large_group
      (fun i => dyadicLogExponent T (q i)) t 1 good
      ht hw (by simpa [good] using hsubTotal) A z e
        (fun i hi => hA i (hgood hi)) hgoodLarge
  refine ⟨u, hune, ?_, hulower, huupper, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp (hus hi)).2
  · change (((∏ i : {i // i ∈ u}, 2 ^ q i : ℕ) : ℕ) : ℝ) =
      T ^ ∑ i ∈ u, dyadicLogExponent T (q i)
    rw [← Finset.prod_subtype u (fun _ => Iff.rfl) (fun i => 2 ^ q i)]
    exact cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT q u
  · change (((∏ i : {i // i ∈ u}, 2 ^ q i : ℕ) : ℕ) : ℝ) ^ e ≤
      ‖∏ i : {i // i ∈ u}, z i‖
    rw [← Finset.prod_subtype u (fun _ => Iff.rfl) (fun i => 2 ^ q i),
      ← Finset.prod_subtype u (fun _ => Iff.rfl) z]
    simpa only [A, Nat.cast_prod, Nat.cast_pow, Nat.cast_ofNat] using hgroup

/-- Literal Heath--Brown specialization of the sub-height selected-polynomial theorem. -/
theorem exists_heathBrown_box_subHeight_large_group
    (L X k m : ℕ) (a : Fin (k - m) → ℕ)
    (b : Fin (k - m - 1) → ℕ) (q0 : ℕ)
    {T t e : ℝ} (hT : 1 < T) (ht : 0 < t)
    (hsubTotal :
      t ≤ ∑ i ∈ (Finset.univ.filter fun i : HeathBrownBoxFactorIndex k m =>
        dyadicLogExponent T (heathBrownBoxFactorExponent a b q0 i) < 1),
          dyadicLogExponent T (heathBrownBoxFactorExponent a b q0 i))
    (s : ℂ)
    (hover : ∀ i : HeathBrownBoxFactorIndex k m,
      1 ≤ dyadicLogExponent T (heathBrownBoxFactorExponent a b q0 i) →
      ‖LSeries (complexCoeff (arithmeticDyadicBlock
        (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
        (heathBrownBoxFactorExponent a b q0 i))) s‖ ≤
          (((2 ^ heathBrownBoxFactorExponent a b q0 i : ℕ) : ℝ)) ^ e)
    (hlarge :
      (groupedDyadicLower (heathBrownBoxFactorExponent a b q0) : ℝ) ^ e ≤
        ‖heathBrownDyadicCoreProduct L X k m a b q0 s‖) :
    ∃ u : Finset (HeathBrownBoxFactorIndex k m), u.Nonempty ∧
      (∀ i ∈ u,
        dyadicLogExponent T (heathBrownBoxFactorExponent a b q0 i) < 1) ∧
      let beta := ∑ i ∈ u,
        dyadicLogExponent T (heathBrownBoxFactorExponent a b q0 i)
      t ≤ beta ∧ beta < 1 + 2 * t ∧
        ((groupedDyadicLower
          (fun i : {i // i ∈ u} =>
            heathBrownBoxFactorExponent a b q0 i) : ℕ) : ℝ) = T ^ beta ∧
        ((groupedDyadicLower
          (fun i : {i // i ∈ u} =>
            heathBrownBoxFactorExponent a b q0 i) : ℕ) : ℝ) ^ e ≤
          ‖∏ i : {i // i ∈ u}, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
              (heathBrownBoxFactorExponent a b q0 i))) s‖ := by
  let q : HeathBrownBoxFactorIndex k m → ℕ :=
    heathBrownBoxFactorExponent a b q0
  let z : HeathBrownBoxFactorIndex k m → ℂ := fun i =>
    LSeries (complexCoeff (arithmeticDyadicBlock
      (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
      (heathBrownBoxFactorExponent a b q0 i))) s
  apply exists_dyadic_subHeight_large_group q z hT ht
      (by simpa [q] using hsubTotal) (by simpa [q, z] using hover)
  dsimp only [z]
  rwa [heathBrownBoxFactorProduct_eq_core]

/-- Generic sub-height selector retaining the near-height atom forced in every overweight cell. -/
theorem exists_dyadic_subHeight_large_group_with_cap_witness
    {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (z : ι → ℂ) {T t e : ℝ}
    (hT : 1 < T) (ht : 0 < t)
    (hsubTotal :
      t ≤ ∑ i ∈ (Finset.univ.filter fun i =>
        dyadicLogExponent T (q i) < 1), dyadicLogExponent T (q i))
    (hover : ∀ i, 1 ≤ dyadicLogExponent T (q i) →
      ‖z i‖ ≤ (((2 ^ q i : ℕ) : ℝ)) ^ e)
    (hlarge : (groupedDyadicLower q : ℝ) ^ e ≤ ‖∏ i, z i‖) :
    ∃ u : Finset ι, u.Nonempty ∧
      (∀ i ∈ u, dyadicLogExponent T (q i) < 1) ∧
      let beta := ∑ i ∈ u, dyadicLogExponent T (q i)
      t ≤ beta ∧ beta < 1 + 2 * t ∧
        ((groupedDyadicLower (fun i : {i // i ∈ u} => q i) : ℕ) : ℝ) =
          T ^ beta ∧
        ((groupedDyadicLower (fun i : {i // i ∈ u} => q i) : ℕ) : ℝ) ^ e ≤
          ‖∏ i : {i // i ∈ u}, z i‖ ∧
        (∃ j ∈ u, beta - 2 * t < dyadicLogExponent T (q j)) ∧
        (beta < 1 ∨
          ∃ j ∈ u, 1 - 2 * t < dyadicLogExponent T (q j)) := by
  classical
  let good : Finset ι := Finset.univ.filter fun i =>
    dyadicLogExponent T (q i) < 1
  let A : ι → ℝ := fun i => (((2 ^ q i : ℕ) : ℝ))
  have hgood : good ⊆ (Finset.univ : Finset ι) := Finset.subset_univ _
  have hA : ∀ i ∈ (Finset.univ : Finset ι), 0 < A i := by
    intro i _
    dsimp only [A]
    positivity
  have hbad : ∀ i ∈ (Finset.univ : Finset ι) \ good,
      ‖z i‖ ≤ A i ^ e := by
    intro i hi
    apply hover i
    have hnot : ¬dyadicLogExponent T (q i) < 1 := by
      have hnotGood : i ∉ good := (Finset.mem_sdiff.mp hi).2
      simpa [good] using hnotGood
    exact le_of_not_gt hnot
  have hlarge' : (∏ i ∈ (Finset.univ : Finset ι), A i) ^ e ≤
      ‖∏ i ∈ (Finset.univ : Finset ι), z i‖ := by
    simpa [A, groupedDyadicLower] using hlarge
  have hgoodLarge := restricted_complex_product_large_of_complement_small
    (Finset.univ : Finset ι) good hgood A z e hA hbad hlarge'
  have hw : ∀ i ∈ good, dyadicLogExponent T (q i) ≤ 1 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.le
  obtain ⟨u, hune, hus, hulower, huupper, hgroup, hlocal, hwitness⟩ :=
    exists_witnessed_bounded_greedy_large_group
      (fun i => dyadicLogExponent T (q i)) t 1 good
      ht hw (by simpa [good] using hsubTotal) A z e
        (fun i hi => hA i (hgood hi)) hgoodLarge
  refine ⟨u, hune, ?_, hulower, huupper, ?_, ?_, hlocal, hwitness⟩
  · intro i hi
    exact (Finset.mem_filter.mp (hus hi)).2
  · change (((∏ i : {i // i ∈ u}, 2 ^ q i : ℕ) : ℕ) : ℝ) =
      T ^ ∑ i ∈ u, dyadicLogExponent T (q i)
    rw [← Finset.prod_subtype u (fun _ => Iff.rfl) (fun i => 2 ^ q i)]
    exact cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT q u
  · change (((∏ i : {i // i ∈ u}, 2 ^ q i : ℕ) : ℕ) : ℝ) ^ e ≤
      ‖∏ i : {i // i ∈ u}, z i‖
    rw [← Finset.prod_subtype u (fun _ => Iff.rfl) (fun i => 2 ^ q i),
      ← Finset.prod_subtype u (fun _ => Iff.rfl) z]
    simpa only [A, Nat.cast_prod, Nat.cast_pow, Nat.cast_ofNat] using hgroup

/-- Literal Heath--Brown selector with an explicit near-height witness in the overweight branch. -/
theorem exists_heathBrown_box_subHeight_large_group_with_cap_witness
    (L X k m : ℕ) (a : Fin (k - m) → ℕ)
    (b : Fin (k - m - 1) → ℕ) (q0 : ℕ)
    {T t e : ℝ} (hT : 1 < T) (ht : 0 < t)
    (hsubTotal :
      t ≤ ∑ i ∈ (Finset.univ.filter fun i : HeathBrownBoxFactorIndex k m =>
        dyadicLogExponent T (heathBrownBoxFactorExponent a b q0 i) < 1),
          dyadicLogExponent T (heathBrownBoxFactorExponent a b q0 i))
    (s : ℂ)
    (hover : ∀ i : HeathBrownBoxFactorIndex k m,
      1 ≤ dyadicLogExponent T (heathBrownBoxFactorExponent a b q0 i) →
      ‖LSeries (complexCoeff (arithmeticDyadicBlock
        (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
        (heathBrownBoxFactorExponent a b q0 i))) s‖ ≤
          (((2 ^ heathBrownBoxFactorExponent a b q0 i : ℕ) : ℝ)) ^ e)
    (hlarge :
      (groupedDyadicLower (heathBrownBoxFactorExponent a b q0) : ℝ) ^ e ≤
        ‖heathBrownDyadicCoreProduct L X k m a b q0 s‖) :
    ∃ u : Finset (HeathBrownBoxFactorIndex k m), u.Nonempty ∧
      (∀ i ∈ u,
        dyadicLogExponent T (heathBrownBoxFactorExponent a b q0 i) < 1) ∧
      let beta := ∑ i ∈ u,
        dyadicLogExponent T (heathBrownBoxFactorExponent a b q0 i)
      t ≤ beta ∧ beta < 1 + 2 * t ∧
        ((groupedDyadicLower (fun i : {i // i ∈ u} =>
          heathBrownBoxFactorExponent a b q0 i) : ℕ) : ℝ) = T ^ beta ∧
        ((groupedDyadicLower (fun i : {i // i ∈ u} =>
          heathBrownBoxFactorExponent a b q0 i) : ℕ) : ℝ) ^ e ≤
          ‖∏ i : {i // i ∈ u}, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
              (heathBrownBoxFactorExponent a b q0 i))) s‖ ∧
        (∃ j ∈ u, beta - 2 * t < dyadicLogExponent T
          (heathBrownBoxFactorExponent a b q0 j)) ∧
        (beta < 1 ∨ ∃ j ∈ u,
          1 - 2 * t < dyadicLogExponent T
            (heathBrownBoxFactorExponent a b q0 j)) := by
  let q : HeathBrownBoxFactorIndex k m → ℕ := heathBrownBoxFactorExponent a b q0
  let z : HeathBrownBoxFactorIndex k m → ℂ := fun i =>
    LSeries (complexCoeff (arithmeticDyadicBlock
      (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
      (heathBrownBoxFactorExponent a b q0 i))) s
  apply exists_dyadic_subHeight_large_group_with_cap_witness q z hT ht
      (by simpa [q] using hsubTotal) (by simpa [q, z] using hover)
  dsimp only [z]
  rwa [heathBrownBoxFactorProduct_eq_core]

end RHTower.Sieve
