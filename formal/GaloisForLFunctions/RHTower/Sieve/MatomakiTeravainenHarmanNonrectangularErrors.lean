import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanRectangularSums

/-!
# Literal Harman rectangularization errors

This file connects the exact nonrectangular errors left by the rectangular-cell decomposition to
the divisor-weighted collision and threshold-boundary majorants.  No source predicate is relaxed.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

local instance instDecidableMTHarmanPairRectangularError
    {t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ) (q₁ q₂ : ℕ) :
    Decidable (MTHarmanPairRectangular t endpoint E q₁ q₂) :=
  Classical.propDecidable _

/-- Exact finite set of admissible nonrectangular source pairs dividing `n`. -/
def mtHarmanPairNonrectangularTuples {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (P.product P).filter fun q =>
    q.2 < q.1 ∧ (q.1 : ℝ) * (q.2 : ℝ) ^ 4 < E ∧ q.1 * q.2 ∣ n ∧
      ¬MTHarmanPairRectangular t endpoint E q.1 q.2

/-- Exact real count of admissible nonrectangular source pairs dividing `n`. -/
def mtHarmanPairNonrectangularTupleCount {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (n : ℕ) : ℝ :=
  (mtHarmanPairNonrectangularTuples (t := t) endpoint P E n).card

/-- Global pair obstruction count written on the common source grid.  Same-cell terms retain the
cell index; threshold terms retain the exact boundary fibre. -/
def mtHarmanPairGlobalObstructionCount {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (δ E : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ q₁ ∈ P, ∑ q₂ ∈ P,
    ((∑ i : Fin t,
        if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
          1 else 0) +
      (if q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂ ∧ q₁ * q₂ ∣ n then
        1 else 0))

private theorem sum_if_mem_eq_sum_of_subset
    {α : Type*} [DecidableEq α] (s u : Finset α) (hu : u ⊆ s) (f : α → ℝ) :
    (∑ x ∈ s, if x ∈ u then f x else 0) = ∑ x ∈ u, f x := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun hx => hx.2, fun hx => ⟨hu hx, hx⟩⟩

private theorem mtAdjacentPrimeBlock_subset_source
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint) (i : Fin t) :
    mtAdjacentPrimeBlock endpoint i ⊆ primesIco (endpoint 0) (endpoint t) := by
  intro q hq
  have hq' := mem_primesIco.mp hq
  apply mem_primesIco.mpr
  exact ⟨(hmono (Nat.zero_le i.1)).trans hq'.1,
    hq'.2.1.trans_le (hmono (Nat.succ_le_iff.mpr i.2)), hq'.2.2⟩

private theorem mtHarmanSameCellFibre_subset_source
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (i : Fin t) (q₂ : ℕ) :
    mtHarmanSameCellFibre endpoint i q₂ ⊆ primesIco (endpoint 0) (endpoint t) := by
  intro q₁ hq₁
  exact mtAdjacentPrimeBlock_subset_source hmono i
    (mem_mtHarmanSameCellFibre.mp hq₁).1

private theorem mtHarmanPairGlobalCollisionCount_eq
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint) (n : ℕ) :
    (∑ q₁ ∈ primesIco (endpoint 0) (endpoint t),
      ∑ q₂ ∈ primesIco (endpoint 0) (endpoint t),
        ∑ i : Fin t,
          if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
              q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
            (1 : ℝ) else 0) =
      ∑ i : Fin t, primePairDivisorCount
        (mtAdjacentPrimeBlock endpoint i) (mtHarmanSameCellFibre endpoint i) n := by
  let P := primesIco (endpoint 0) (endpoint t)
  calc
    (∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ i : Fin t,
        if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
          (1 : ℝ) else 0) =
      ∑ q₁ ∈ P, ∑ i : Fin t, ∑ q₂ ∈ P,
        if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
          (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      exact Finset.sum_comm
    _ = ∑ i : Fin t, ∑ q₁ ∈ P, ∑ q₂ ∈ P,
        if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
          (1 : ℝ) else 0 := Finset.sum_comm
    _ = ∑ i : Fin t, ∑ q₂ ∈ P, ∑ q₁ ∈ P,
        if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
          (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ i : Fin t, primePairDivisorCount
        (mtAdjacentPrimeBlock endpoint i) (mtHarmanSameCellFibre endpoint i) n := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold primePairDivisorCount
      calc
        (∑ q₂ ∈ P, ∑ q₁ ∈ P,
            if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
                q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
              (1 : ℝ) else 0) =
          ∑ q₂ ∈ P, if q₂ ∈ mtAdjacentPrimeBlock endpoint i then
            ∑ q₁ ∈ P, if q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ then
              (if q₁ * q₂ ∣ n then (1 : ℝ) else 0) else 0
            else 0 := by
          apply Finset.sum_congr rfl
          intro q₂ hq₂
          by_cases hq₂i : q₂ ∈ mtAdjacentPrimeBlock endpoint i
          · rw [if_pos hq₂i]
            apply Finset.sum_congr rfl
            intro q₁ hq₁
            by_cases hq₁i : q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ <;>
              by_cases hdvd : q₁ * q₂ ∣ n <;> simp [hq₂i, hq₁i, hdvd]
          · simp [hq₂i]
        _ = ∑ q₂ ∈ mtAdjacentPrimeBlock endpoint i,
            ∑ q₁ ∈ P, if q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ then
              (if q₁ * q₂ ∣ n then (1 : ℝ) else 0) else 0 :=
          sum_if_mem_eq_sum_of_subset P (mtAdjacentPrimeBlock endpoint i)
            (mtAdjacentPrimeBlock_subset_source hmono i) _
        _ = ∑ q₂ ∈ mtAdjacentPrimeBlock endpoint i,
            ∑ q₁ ∈ mtHarmanSameCellFibre endpoint i q₂,
              if q₁ * q₂ ∣ n then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro q₂ hq₂
          exact sum_if_mem_eq_sum_of_subset P
            (mtHarmanSameCellFibre endpoint i q₂)
            (mtHarmanSameCellFibre_subset_source hmono i q₂) _
        _ = ∑ q₂ ∈ mtAdjacentPrimeBlock endpoint i,
            ∑ q₁ ∈ mtHarmanSameCellFibre endpoint i q₂,
              if q₂ * q₁ ∣ n then (1 : ℝ) else 0 := by
          simp only [Nat.mul_comm]

private theorem mtHarmanPairGlobalBoundaryCount_eq
    {t : ℕ} (endpoint : ℕ → ℕ) (δ E : ℝ) (n : ℕ) :
    (∑ q₁ ∈ primesIco (endpoint 0) (endpoint t),
      ∑ q₂ ∈ primesIco (endpoint 0) (endpoint t),
        if q₁ ∈ mtHarmanThresholdBoundaryFibre
              (primesIco (endpoint 0) (endpoint t)) δ E q₂ ∧ q₁ * q₂ ∣ n then
          (1 : ℝ) else 0) =
      primePairDivisorCount (primesIco (endpoint 0) (endpoint t))
        (fun q₂ => mtHarmanThresholdBoundaryFibre
          (primesIco (endpoint 0) (endpoint t)) δ E q₂) n := by
  let P := primesIco (endpoint 0) (endpoint t)
  calc
    (∑ q₁ ∈ P, ∑ q₂ ∈ P,
        if q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂ ∧ q₁ * q₂ ∣ n then
          (1 : ℝ) else 0) =
      ∑ q₂ ∈ P, ∑ q₁ ∈ P,
        if q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂ ∧ q₁ * q₂ ∣ n then
          (1 : ℝ) else 0 := Finset.sum_comm
    _ = ∑ q₂ ∈ P, ∑ q₁ ∈ P,
        if q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂ then
          (if q₁ * q₂ ∣ n then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro q₂ hq₂
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      by_cases hq₁b : q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂ <;>
        simp [hq₁b]
    _ = ∑ q₂ ∈ P, ∑ q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂,
        if q₁ * q₂ ∣ n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro q₂ hq₂
      exact sum_if_mem_eq_sum_of_subset P (mtHarmanThresholdBoundaryFibre P δ E q₂)
        (fun q₁ hq₁ => (mem_mtHarmanThresholdBoundaryFibre.mp hq₁).1) _
    _ = primePairDivisorCount P
        (fun q₂ => mtHarmanThresholdBoundaryFibre P δ E q₂) n := by
      unfold primePairDivisorCount
      simp only [Nat.mul_comm]

/-- Grid-form pair obstruction count is exactly the existing divisor-weighted majorant at weight
zero. -/
theorem mtHarmanPairGlobalObstructionCount_eq_weighted_zero
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (δ E : ℝ) (n : ℕ) :
    mtHarmanPairGlobalObstructionCount (t := t) endpoint
        (primesIco (endpoint 0) (endpoint t)) δ E n =
      weightedMTHarmanNonrectangularCount 0 (t := t) endpoint
        (primesIco (endpoint 0) (endpoint t)) δ E n := by
  unfold mtHarmanPairGlobalObstructionCount
  simp only [Finset.sum_add_distrib]
  rw [mtHarmanPairGlobalCollisionCount_eq hmono,
    mtHarmanPairGlobalBoundaryCount_eq]
  simp [weightedMTHarmanNonrectangularCount,
    weightedMTHarmanSameCellCollisionCount,
    weightedMTHarmanThresholdBoundaryCount, weightedPrimePairDivisorCount]

theorem mtHarmanPairNonrectangularTupleCount_eq_sum
    {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (n : ℕ) :
    mtHarmanPairNonrectangularTupleCount (t := t) endpoint P E n =
      ∑ q₁ ∈ P, ∑ q₂ ∈ P,
        if q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ ∣ n ∧
            ¬MTHarmanPairRectangular t endpoint E q₁ q₂ then 1 else 0 := by
  classical
  unfold mtHarmanPairNonrectangularTupleCount mtHarmanPairNonrectangularTuples
  calc
    (((P.product P).filter fun q =>
        q.2 < q.1 ∧ (q.1 : ℝ) * (q.2 : ℝ) ^ 4 < E ∧ q.1 * q.2 ∣ n ∧
          ¬MTHarmanPairRectangular t endpoint E q.1 q.2).card : ℝ) =
      ∑ q ∈ (P.product P).filter fun q =>
        q.2 < q.1 ∧ (q.1 : ℝ) * (q.2 : ℝ) ^ 4 < E ∧ q.1 * q.2 ∣ n ∧
          ¬MTHarmanPairRectangular t endpoint E q.1 q.2, (1 : ℝ) := by simp
    _ = ∑ q ∈ P.product P,
        if q.2 < q.1 ∧ (q.1 : ℝ) * (q.2 : ℝ) ^ 4 < E ∧ q.1 * q.2 ∣ n ∧
            ¬MTHarmanPairRectangular t endpoint E q.1 q.2 then (1 : ℝ) else 0 :=
      Finset.sum_filter _ _
    _ = ∑ q₁ ∈ P, ∑ q₂ ∈ P,
        if q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ ∣ n ∧
            ¬MTHarmanPairRectangular t endpoint E q₁ q₂ then 1 else 0 :=
      Finset.sum_product P P _

/-- Triangle inequality and `rho ≤ 1`: literal pair error is at most its exact tuple count. -/
theorem norm_mtHarmanPairNonrectangularError_le_tupleCount
    {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (z n : ℕ) :
    ‖mtHarmanPairNonrectangularError (t := t) endpoint P E z n‖ ≤
      mtHarmanPairNonrectangularTupleCount (t := t) endpoint P E n := by
  classical
  rw [mtHarmanPairNonrectangularTupleCount_eq_sum]
  unfold mtHarmanPairNonrectangularError
  calc
    ‖∑ q ∈ P.product P,
        if q.2 < q.1 ∧ (q.1 : ℝ) * (q.2 : ℝ) ^ 4 < E ∧ q.1 * q.2 ∣ n ∧
            ¬MTHarmanPairRectangular t endpoint E q.1 q.2 then
          (rho (n / q.1 / q.2) z : ℂ) else 0‖ =
      ‖∑ q₁ ∈ P, ∑ q₂ ∈ P,
        if q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ ∣ n ∧
            ¬MTHarmanPairRectangular t endpoint E q₁ q₂ then
          (rho (n / q₁ / q₂) z : ℂ) else 0‖ :=
      congrArg norm (Finset.sum_product P P _)
    _ ≤
        ∑ q₁ ∈ P, ‖∑ q₂ ∈ P,
          if q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ ∣ n ∧
              ¬MTHarmanPairRectangular t endpoint E q₁ q₂ then
            (rho (n / q₁ / q₂) z : ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ q₁ ∈ P, ∑ q₂ ∈ P,
        ‖if q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ ∣ n ∧
            ¬MTHarmanPairRectangular t endpoint E q₁ q₂ then
          (rho (n / q₁ / q₂) z : ℂ) else 0‖ := by
      apply Finset.sum_le_sum
      intro q₁ hq₁
      exact norm_sum_le _ _
    _ ≤ ∑ q₁ ∈ P, ∑ q₂ ∈ P,
        if q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ ∣ n ∧
            ¬MTHarmanPairRectangular t endpoint E q₁ q₂ then 1 else 0 := by
      apply Finset.sum_le_sum
      intro q₁ hq₁
      apply Finset.sum_le_sum
      intro q₂ hq₂
      split_ifs with h
      · rw [norm_natCast]
        exact_mod_cast rho_le_one (n / q₁ / q₂) z
      · simp

/-- Every literal bad pair is counted by a same-cell or threshold-boundary obstruction. -/
theorem mtHarmanPairNonrectangularTupleCount_le_globalObstruction
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    (δ E : ℝ) (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (n : ℕ) :
    mtHarmanPairNonrectangularTupleCount (t := t) endpoint
        (primesIco (endpoint 0) (endpoint t)) E n ≤
      mtHarmanPairGlobalObstructionCount (t := t) endpoint
        (primesIco (endpoint 0) (endpoint t)) δ E n := by
  classical
  rw [mtHarmanPairNonrectangularTupleCount_eq_sum]
  unfold mtHarmanPairGlobalObstructionCount
  apply Finset.sum_le_sum
  intro q₁ hq₁
  apply Finset.sum_le_sum
  intro q₂ hq₂
  by_cases hbad : q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ ∣ n ∧
      ¬MTHarmanPairRectangular t endpoint E q₁ q₂
  · rw [if_pos hbad]
    rcases matomakiTeravainen_admissiblePair_not_rectangular
        hendpoint hmono hδ hband hq₁ hq₂ hbad.1 hbad.2.1 hbad.2.2.2 with
      hcollision | hboundary
    · obtain ⟨i, hq₁i, hq₂i⟩ := hcollision
      have hfibre : q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ :=
        sameCell_pair_mem_collisionFibre hq₁i hbad.1
      have hone :
          (if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
              q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
            (1 : ℝ) else 0) = 1 := by
        simp [hq₂i, hfibre, hbad.2.2.1]
      calc
        (1 : ℝ) = if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
              q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
            1 else 0 := hone.symm
        _ ≤ ∑ j : Fin t,
            if q₂ ∈ mtAdjacentPrimeBlock endpoint j ∧
                q₁ ∈ mtHarmanSameCellFibre endpoint j q₂ ∧ q₁ * q₂ ∣ n then
              1 else 0 := Finset.single_le_sum
            (f := fun j : Fin t =>
              if q₂ ∈ mtAdjacentPrimeBlock endpoint j ∧
                  q₁ ∈ mtHarmanSameCellFibre endpoint j q₂ ∧ q₁ * q₂ ∣ n then
                (1 : ℝ) else 0)
            (fun j hj => by positivity) (Finset.mem_univ i)
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · have hone :
          (if q₁ ∈ mtHarmanThresholdBoundaryFibre
                (primesIco (endpoint 0) (endpoint t)) δ E q₂ ∧ q₁ * q₂ ∣ n then
            (1 : ℝ) else 0) = 1 := by
        simp [hboundary, hbad.2.2.1]
      rw [hone]
      exact le_add_of_nonneg_left (by positivity)
  · rw [if_neg hbad]
    positivity

/-- A bad pair injects into the ordered square of the divisor set of `n`. -/
theorem mtHarmanPairNonrectangularTupleCount_le_divisors_sq
    {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ)
    {n : ℕ} (hn : n ≠ 0) :
    mtHarmanPairNonrectangularTupleCount (t := t) endpoint P E n ≤
      (n.divisors.card : ℝ) ^ 2 := by
  classical
  have hsubset : mtHarmanPairNonrectangularTuples (t := t) endpoint P E n ⊆
      n.divisors.product n.divisors := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hdvd := hq'.2.2.2.1
    apply Finset.mem_product.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, hn⟩, Nat.mem_divisors.mpr ⟨?_, hn⟩⟩
    · exact dvd_trans (Nat.dvd_mul_right q.1 q.2) hdvd
    · exact dvd_trans (by
        simp) hdvd
  have hcard := Finset.card_le_card hsubset
  have hprod : (n.divisors.product n.divisors).card =
      n.divisors.card * n.divisors.card := Finset.card_product _ _
  rw [hprod] at hcard
  have hcard' :
      (mtHarmanPairNonrectangularTuples (t := t) endpoint P E n).card ≤
        n.divisors.card ^ 2 := by
    simpa only [pow_two] using hcard
  unfold mtHarmanPairNonrectangularTupleCount
  exact_mod_cast hcard'

/-- Changing divisor weight only multiplies the unweighted nonrectangular majorant by the
corresponding divisor power. -/
theorem weightedMTHarmanNonrectangularCount_eq_divisorsPow_mul_zero
    (K : ℕ) {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (δ E : ℝ) (n : ℕ) :
    weightedMTHarmanNonrectangularCount K (t := t) endpoint P δ E n =
      (n.divisors.card : ℝ) ^ K *
        weightedMTHarmanNonrectangularCount 0 (t := t) endpoint P δ E n := by
  unfold weightedMTHarmanNonrectangularCount
    weightedMTHarmanSameCellCollisionCount
    weightedMTHarmanThresholdBoundaryCount weightedPrimePairDivisorCount
  simp only [pow_zero, one_mul]
  rw [mul_add, Finset.mul_sum]

/-- Pointwise squared pair error is absorbed by the existing `K = 2` weighted obstruction
majorant. -/
theorem normSq_mtHarmanPairNonrectangularError_le_weighted
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    (δ E : ℝ) (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (z : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ‖mtHarmanPairNonrectangularError (t := t) endpoint
        (primesIco (endpoint 0) (endpoint t)) E z n‖ ^ 2 ≤
      weightedMTHarmanNonrectangularCount 2 (t := t) endpoint
        (primesIco (endpoint 0) (endpoint t)) δ E n := by
  let P := primesIco (endpoint 0) (endpoint t)
  let C := mtHarmanPairNonrectangularTupleCount (t := t) endpoint P E n
  let M := weightedMTHarmanNonrectangularCount 0 (t := t) endpoint P δ E n
  have hnorm : ‖mtHarmanPairNonrectangularError (t := t) endpoint P E z n‖ ≤ C := by
    exact norm_mtHarmanPairNonrectangularError_le_tupleCount endpoint P E z n
  have hCM : C ≤ M := by
    calc
      C ≤ mtHarmanPairGlobalObstructionCount (t := t) endpoint P δ E n :=
        mtHarmanPairNonrectangularTupleCount_le_globalObstruction
          hendpoint hmono δ E hδ hband n
      _ = M := mtHarmanPairGlobalObstructionCount_eq_weighted_zero hmono δ E n
  have hCd : C ≤ (n.divisors.card : ℝ) ^ 2 :=
    mtHarmanPairNonrectangularTupleCount_le_divisors_sq endpoint P E hn
  have hC0 : 0 ≤ C := by
    dsimp [C, mtHarmanPairNonrectangularTupleCount]
    positivity
  calc
    ‖mtHarmanPairNonrectangularError (t := t) endpoint P E z n‖ ^ 2 ≤ C ^ 2 := by
      simpa only [pow_two] using mul_le_mul hnorm hnorm (norm_nonneg _) hC0
    _ ≤ (n.divisors.card : ℝ) ^ 2 * M := by
      simpa only [pow_two] using
        mul_le_mul hCd hCM hC0 (sq_nonneg (n.divisors.card : ℝ))
    _ = weightedMTHarmanNonrectangularCount 2 (t := t) endpoint P δ E n := by
      rw [weightedMTHarmanNonrectangularCount_eq_divisorsPow_mul_zero]

/-- Paper-aligned pair rectangularization has the exact `66δ_A` mean-square cost inherited from
the collision/boundary majorant. -/
theorem eventually_sum_normSq_mtHarmanPairNonrectangularError_paperAligned_le
    (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (z₁ Y : ℕ) (E : ℝ) (z : ℕ),
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X → 1 ≤ Y →
      let endpoint :=
        mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)
      let P := primesIco (mtLowerCutoffNat X) z₁
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtHarmanPairNonrectangularError
            (t := z₁ - mtLowerCutoffNat X) endpoint P E z n‖ ^ 2 ≤
        (4 : ℝ) ^ 2 * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ 2 - 1) *
            (66 * mtPaperWidth A X) * ∑ q ∈ P, 1 / (q : ℝ) := by
  filter_upwards [
    eventually_sum_weightedMTHarmanNonrectangularCount_paperAligned_le A 2,
    eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hweightedX hprogressX hX
  intro z₁ Y E z hz hzX hY
  dsimp only
  let z₀ := mtLowerCutoffNat X
  let δ := mtPaperWidth A X
  let endpoint := mtPaperAlignedEndpoint z₀ z₁ δ
  let P := primesIco z₀ z₁
  have hlogX : 1 ≤ Real.log X := by
    have hmonoLog := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmonoLog
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, mtPaperWidth]
    exact Real.rpow_nonneg (zero_le_one.trans hlogX) _
  have hzSubPos : 0 < z₀ - 1 := by
    by_contra hnot
    have hzero : z₀ - 1 = 0 := Nat.eq_zero_of_not_pos hnot
    have hfalse : (1 : ℝ) ≤ 0 := by
      simpa only [z₀, δ, hzero, Nat.cast_zero, mul_zero] using hprogressX
    norm_num at hfalse
  have hzOne : 1 ≤ z₀ := by omega
  have hmonoEndpoint : Monotone endpoint := by
    dsimp [endpoint]
    exact mtPaperAlignedEndpoint_monotone hzOne (by simpa only [z₀] using hz) hδ0
      (by simpa only [z₀, δ] using hprogressX)
  have hendpoint : ∀ i, 1 ≤ endpoint i := by
    intro i
    exact hzOne.trans (mtPaperAlignedEndpoint_mem_Icc hzOne
      (by simpa only [z₀] using hz) hδ0
      (by simpa only [z₀, δ] using hprogressX) i).1
  have hband : ∀ i : Fin (z₁ - z₀),
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i := by
    intro i
    simpa only [endpoint, mtAdjacentBlockUpperScale, mtAdjacentBlockLowerScale] using
      mtPaperAlignedEndpoint_band (z₀ := z₀) (z₁ := z₁) hδ0 i.1
  have hterminal : endpoint (z₁ - z₀) = z₁ := by
    dsimp [endpoint]
    exact mtPaperAlignedEndpoint_sub_eq hzOne (by simpa only [z₀] using hz) hδ0
      (by simpa only [z₀, δ] using hprogressX)
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        ‖mtHarmanPairNonrectangularError
          (t := z₁ - z₀) endpoint P E z n‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 Y,
        weightedMTHarmanNonrectangularCount 2
          (t := z₁ - z₀) endpoint P δ E n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := by
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        omega
      have hpoint := normSq_mtHarmanPairNonrectangularError_le_weighted
        (t := z₁ - z₀) hendpoint hmonoEndpoint δ E hδ0 hband z
        (n := n) hn0
      simpa only [P, endpoint, mtPaperAlignedEndpoint_zero, hterminal] using hpoint
    _ ≤ (4 : ℝ) ^ 2 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 2 - 1) *
          (66 * δ) * ∑ q ∈ P, 1 / (q : ℝ) := by
      simpa only [z₀, δ, endpoint, P] using hweightedX z₁ Y E hz hzX hY

local instance instDecidableMTHarmanTripleRectangularError
    {t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ) (q₁ q₂ q₃ : ℕ) :
    Decidable (MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃) :=
  Classical.propDecidable _

/-- Exact finite set of admissible nonrectangular source triples dividing `n`. -/
def mtHarmanTripleNonrectangularTuples {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (n : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact ((P.product P).product P).filter fun q =>
    q.2 < q.1.2 ∧ q.1.2 < q.1.1 ∧
      (q.1.1 : ℝ) * (q.1.2 : ℝ) ^ 4 < E ∧
      q.1.1 * q.1.2 * q.2 ∣ n ∧
      ¬MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2

/-- Exact real count of admissible nonrectangular source triples dividing `n`. -/
def mtHarmanTripleNonrectangularTupleCount {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (n : ℕ) : ℝ :=
  (mtHarmanTripleNonrectangularTuples (t := t) endpoint P E n).card

theorem mtHarmanTripleNonrectangularTupleCount_eq_sum
    {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (n : ℕ) :
    mtHarmanTripleNonrectangularTupleCount (t := t) endpoint P E n =
      ∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ q₃ ∈ P,
        if q₃ < q₂ ∧ q₂ < q₁ ∧
            (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ * q₃ ∣ n ∧
            ¬MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃ then 1 else 0 := by
  classical
  unfold mtHarmanTripleNonrectangularTupleCount mtHarmanTripleNonrectangularTuples
  calc
    ((((P.product P).product P).filter fun q =>
        q.2 < q.1.2 ∧ q.1.2 < q.1.1 ∧
          (q.1.1 : ℝ) * (q.1.2 : ℝ) ^ 4 < E ∧ q.1.1 * q.1.2 * q.2 ∣ n ∧
          ¬MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2).card : ℝ) =
      ∑ q ∈ ((P.product P).product P).filter fun q =>
        q.2 < q.1.2 ∧ q.1.2 < q.1.1 ∧
          (q.1.1 : ℝ) * (q.1.2 : ℝ) ^ 4 < E ∧ q.1.1 * q.1.2 * q.2 ∣ n ∧
          ¬MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2, (1 : ℝ) := by simp
    _ = ∑ q ∈ (P.product P).product P,
        if q.2 < q.1.2 ∧ q.1.2 < q.1.1 ∧
            (q.1.1 : ℝ) * (q.1.2 : ℝ) ^ 4 < E ∧ q.1.1 * q.1.2 * q.2 ∣ n ∧
            ¬MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2 then (1 : ℝ) else 0 :=
      Finset.sum_filter _ _
    _ = ∑ q₁q₂ ∈ P.product P, ∑ q₃ ∈ P,
        if q₃ < q₁q₂.2 ∧ q₁q₂.2 < q₁q₂.1 ∧
            (q₁q₂.1 : ℝ) * (q₁q₂.2 : ℝ) ^ 4 < E ∧
            q₁q₂.1 * q₁q₂.2 * q₃ ∣ n ∧
            ¬MTHarmanTripleRectangular t endpoint E q₁q₂.1 q₁q₂.2 q₃ then 1 else 0 :=
      Finset.sum_product (P.product P) P _
    _ = ∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ q₃ ∈ P,
        if q₃ < q₂ ∧ q₂ < q₁ ∧
            (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ * q₃ ∣ n ∧
            ¬MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃ then 1 else 0 :=
      Finset.sum_product P P _

/-- Triangle inequality and `rho ≤ 1`: literal triple error is at most its exact tuple count. -/
theorem norm_mtHarmanTripleNonrectangularError_le_tupleCount
    {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (z n : ℕ) :
    ‖mtHarmanTripleNonrectangularError (t := t) endpoint P E z n‖ ≤
      mtHarmanTripleNonrectangularTupleCount (t := t) endpoint P E n := by
  classical
  rw [mtHarmanTripleNonrectangularTupleCount_eq_sum]
  unfold mtHarmanTripleNonrectangularError
  calc
    ‖∑ q ∈ (P.product P).product P,
        if q.2 < q.1.2 ∧ q.1.2 < q.1.1 ∧
            (q.1.1 : ℝ) * (q.1.2 : ℝ) ^ 4 < E ∧ q.1.1 * q.1.2 * q.2 ∣ n ∧
            ¬MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2 then
          (rho (n / q.1.1 / q.1.2 / q.2) z : ℂ) else 0‖ =
      ‖∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ q₃ ∈ P,
        if q₃ < q₂ ∧ q₂ < q₁ ∧
            (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ * q₃ ∣ n ∧
            ¬MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃ then
          (rho (n / q₁ / q₂ / q₃) z : ℂ) else 0‖ := by
      apply congrArg norm
      calc
        (∑ q ∈ (P.product P).product P,
            if q.2 < q.1.2 ∧ q.1.2 < q.1.1 ∧
                (q.1.1 : ℝ) * (q.1.2 : ℝ) ^ 4 < E ∧ q.1.1 * q.1.2 * q.2 ∣ n ∧
                ¬MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2 then
              (rho (n / q.1.1 / q.1.2 / q.2) z : ℂ) else 0) =
          ∑ q₁q₂ ∈ P.product P, ∑ q₃ ∈ P,
            if q₃ < q₁q₂.2 ∧ q₁q₂.2 < q₁q₂.1 ∧
                (q₁q₂.1 : ℝ) * (q₁q₂.2 : ℝ) ^ 4 < E ∧
                q₁q₂.1 * q₁q₂.2 * q₃ ∣ n ∧
                ¬MTHarmanTripleRectangular t endpoint E
                  q₁q₂.1 q₁q₂.2 q₃ then
              (rho (n / q₁q₂.1 / q₁q₂.2 / q₃) z : ℂ) else 0 :=
          Finset.sum_product (P.product P) P _
        _ = ∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ q₃ ∈ P,
            if q₃ < q₂ ∧ q₂ < q₁ ∧
                (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ * q₃ ∣ n ∧
                ¬MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃ then
              (rho (n / q₁ / q₂ / q₃) z : ℂ) else 0 :=
          Finset.sum_product P P _
    _ ≤ ∑ q₁ ∈ P, ‖∑ q₂ ∈ P, ∑ q₃ ∈ P,
        if q₃ < q₂ ∧ q₂ < q₁ ∧
            (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ * q₃ ∣ n ∧
            ¬MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃ then
          (rho (n / q₁ / q₂ / q₃) z : ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ q₁ ∈ P, ∑ q₂ ∈ P, ‖∑ q₃ ∈ P,
        if q₃ < q₂ ∧ q₂ < q₁ ∧
            (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ * q₃ ∣ n ∧
            ¬MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃ then
          (rho (n / q₁ / q₂ / q₃) z : ℂ) else 0‖ := by
      apply Finset.sum_le_sum
      intro q₁ hq₁
      exact norm_sum_le _ _
    _ ≤ ∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ q₃ ∈ P,
        ‖if q₃ < q₂ ∧ q₂ < q₁ ∧
            (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ * q₃ ∣ n ∧
            ¬MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃ then
          (rho (n / q₁ / q₂ / q₃) z : ℂ) else 0‖ := by
      apply Finset.sum_le_sum
      intro q₁ hq₁
      apply Finset.sum_le_sum
      intro q₂ hq₂
      exact norm_sum_le _ _
    _ ≤ ∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ q₃ ∈ P,
        if q₃ < q₂ ∧ q₂ < q₁ ∧
            (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ * q₃ ∣ n ∧
            ¬MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃ then 1 else 0 := by
      apply Finset.sum_le_sum
      intro q₁ hq₁
      apply Finset.sum_le_sum
      intro q₂ hq₂
      apply Finset.sum_le_sum
      intro q₃ hq₃
      split_ifs with h
      · rw [norm_natCast]
        exact_mod_cast rho_le_one (n / q₁ / q₂ / q₃) z
      · simp

/-- A bad triple injects into the ordered cube of the divisor set of `n`. -/
theorem mtHarmanTripleNonrectangularTupleCount_le_divisors_cube
    {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ)
    {n : ℕ} (hn : n ≠ 0) :
    mtHarmanTripleNonrectangularTupleCount (t := t) endpoint P E n ≤
      (n.divisors.card : ℝ) ^ 3 := by
  classical
  have hsubset : mtHarmanTripleNonrectangularTuples (t := t) endpoint P E n ⊆
      (n.divisors.product n.divisors).product n.divisors := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hdvd := hq'.2.2.2.2.1
    apply Finset.mem_product.mpr
    apply And.intro (Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hn⟩,
      Nat.mem_divisors.mpr ⟨?_, hn⟩⟩) (Nat.mem_divisors.mpr ⟨?_, hn⟩)
    · exact dvd_trans ⟨q.1.2 * q.2, Nat.mul_assoc _ _ _⟩ hdvd
    · exact dvd_trans ⟨q.1.1 * q.2, by ac_rfl⟩ hdvd
    · exact dvd_trans ⟨q.1.1 * q.1.2, by ac_rfl⟩ hdvd
  have hcard := Finset.card_le_card hsubset
  have hprod : ((n.divisors.product n.divisors).product n.divisors).card =
      n.divisors.card * n.divisors.card * n.divisors.card := by
    calc
      ((n.divisors.product n.divisors).product n.divisors).card =
          (n.divisors.product n.divisors).card * n.divisors.card :=
        Finset.card_product _ _
      _ = n.divisors.card * n.divisors.card * n.divisors.card := by
        have hinner : (n.divisors.product n.divisors).card =
            n.divisors.card * n.divisors.card := Finset.card_product _ _
        rw [hinner]
  rw [hprod] at hcard
  have hcard' :
      (mtHarmanTripleNonrectangularTuples (t := t) endpoint P E n).card ≤
        n.divisors.card ^ 3 := by
    simpa [pow_succ, Nat.mul_assoc] using hcard
  unfold mtHarmanTripleNonrectangularTupleCount
  exact_mod_cast hcard'

/-- Triple obstruction count on the common source grid.  It records the two possible same-cell
collisions and the exact `(q₁,q₂)` threshold-boundary fibre. -/
def mtHarmanTripleGlobalObstructionCount {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (δ E : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ q₃ ∈ P,
    (((∑ i : Fin t,
        if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧
            q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0) +
      (∑ i : Fin t,
        if q₃ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₂ ∈ mtHarmanSameCellFibre endpoint i q₃ ∧
            q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0)) +
      (if q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂ ∧
          q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0))

/-- Every literal bad triple is counted by one of the two collision grids or the pair-threshold
boundary grid. -/
theorem mtHarmanTripleNonrectangularTupleCount_le_globalObstruction
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    (δ E : ℝ) (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (n : ℕ) :
    mtHarmanTripleNonrectangularTupleCount (t := t) endpoint
        (primesIco (endpoint 0) (endpoint t)) E n ≤
      mtHarmanTripleGlobalObstructionCount (t := t) endpoint
        (primesIco (endpoint 0) (endpoint t)) δ E n := by
  classical
  rw [mtHarmanTripleNonrectangularTupleCount_eq_sum]
  unfold mtHarmanTripleGlobalObstructionCount
  apply Finset.sum_le_sum
  intro q₁ hq₁
  apply Finset.sum_le_sum
  intro q₂ hq₂
  apply Finset.sum_le_sum
  intro q₃ hq₃
  by_cases hbad : q₃ < q₂ ∧ q₂ < q₁ ∧
      (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E ∧ q₁ * q₂ * q₃ ∣ n ∧
      ¬MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃
  · rw [if_pos hbad]
    rcases matomakiTeravainen_admissibleTriple_not_rectangular
        hendpoint hmono hδ hband hq₁ hq₂ hq₃ hbad.2.1 hbad.1 hbad.2.2.1
          hbad.2.2.2.2 with hcollision₁₂ | hcollision₂₃ | hboundary
    · obtain ⟨i, hq₁i, hq₂i⟩ := hcollision₁₂
      have hfibre : q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ :=
        sameCell_pair_mem_collisionFibre hq₁i hbad.2.1
      have hone :
          (if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
              q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧
              q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0) = 1 := by
        simp [hq₂i, hfibre, hbad.2.2.2.1]
      have hfirst : (1 : ℝ) ≤ ∑ j : Fin t,
          if q₂ ∈ mtAdjacentPrimeBlock endpoint j ∧
              q₁ ∈ mtHarmanSameCellFibre endpoint j q₂ ∧
              q₁ * q₂ * q₃ ∣ n then 1 else 0 := by
        calc
          (1 : ℝ) = if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
                q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧
                q₁ * q₂ * q₃ ∣ n then 1 else 0 := hone.symm
          _ ≤ _ := Finset.single_le_sum
            (f := fun j : Fin t =>
              if q₂ ∈ mtAdjacentPrimeBlock endpoint j ∧
                  q₁ ∈ mtHarmanSameCellFibre endpoint j q₂ ∧
                  q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0)
            (fun j hj => by positivity) (Finset.mem_univ i)
      exact hfirst.trans (le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity)))
    · obtain ⟨i, hq₂i, hq₃i⟩ := hcollision₂₃
      have hfibre : q₂ ∈ mtHarmanSameCellFibre endpoint i q₃ :=
        sameCell_pair_mem_collisionFibre hq₂i hbad.1
      have hone :
          (if q₃ ∈ mtAdjacentPrimeBlock endpoint i ∧
              q₂ ∈ mtHarmanSameCellFibre endpoint i q₃ ∧
              q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0) = 1 := by
        simp [hq₃i, hfibre, hbad.2.2.2.1]
      have hsecond : (1 : ℝ) ≤ ∑ j : Fin t,
          if q₃ ∈ mtAdjacentPrimeBlock endpoint j ∧
              q₂ ∈ mtHarmanSameCellFibre endpoint j q₃ ∧
              q₁ * q₂ * q₃ ∣ n then 1 else 0 := by
        calc
          (1 : ℝ) = if q₃ ∈ mtAdjacentPrimeBlock endpoint i ∧
                q₂ ∈ mtHarmanSameCellFibre endpoint i q₃ ∧
                q₁ * q₂ * q₃ ∣ n then 1 else 0 := hone.symm
          _ ≤ _ := Finset.single_le_sum
            (f := fun j : Fin t =>
              if q₃ ∈ mtAdjacentPrimeBlock endpoint j ∧
                  q₂ ∈ mtHarmanSameCellFibre endpoint j q₃ ∧
                  q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0)
            (fun j hj => by positivity) (Finset.mem_univ i)
      exact (hsecond.trans (le_add_of_nonneg_left (by positivity))).trans
        (le_add_of_nonneg_right (by positivity))
    · have hone :
          (if q₁ ∈ mtHarmanThresholdBoundaryFibre
                (primesIco (endpoint 0) (endpoint t)) δ E q₂ ∧
              q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0) = 1 := by
        simp [hboundary, hbad.2.2.2.1]
      rw [hone]
      exact le_add_of_nonneg_left (by positivity)
  · rw [if_neg hbad]
    positivity

private theorem sum_tripleDvdIndicator_le_divisors_mul_pairIndicator
    (P : Finset ℕ) (a b : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (∑ q ∈ P, if a * b * q ∣ n then (1 : ℝ) else 0) ≤
      (n.divisors.card : ℝ) * (if a * b ∣ n then 1 else 0) := by
  classical
  by_cases hab : a * b ∣ n
  · rw [if_pos hab, mul_one]
    have hsubset : (P.filter fun q => a * b * q ∣ n) ⊆ n.divisors := by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      apply Nat.mem_divisors.mpr
      refine ⟨dvd_trans ⟨a * b, by ac_rfl⟩ hq'.2, hn⟩
    have hcard := Finset.card_le_card hsubset
    calc
      (∑ q ∈ P, if a * b * q ∣ n then (1 : ℝ) else 0) =
          (((P.filter fun q => a * b * q ∣ n).card : ℕ) : ℝ) := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ (n.divisors.card : ℝ) := by exact_mod_cast hcard
  · rw [if_neg hab, mul_zero]
    have hzero : (∑ q ∈ P, if a * b * q ∣ n then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      rw [if_neg]
      intro htriple
      exact hab (dvd_trans (Nat.dvd_mul_right (a * b) q) htriple)
    rw [hzero]

private theorem mtHarmanTripleFirstCollisionGrid_le
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    {n : ℕ} (hn : n ≠ 0) :
    (∑ q₁ ∈ primesIco (endpoint 0) (endpoint t),
      ∑ q₂ ∈ primesIco (endpoint 0) (endpoint t),
      ∑ q₃ ∈ primesIco (endpoint 0) (endpoint t),
      ∑ i : Fin t,
        if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧
            q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0) ≤
      (n.divisors.card : ℝ) *
        ∑ i : Fin t, primePairDivisorCount
          (mtAdjacentPrimeBlock endpoint i) (mtHarmanSameCellFibre endpoint i) n := by
  let P := primesIco (endpoint 0) (endpoint t)
  let d : ℝ := n.divisors.card
  calc
    (∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ q₃ ∈ P, ∑ i : Fin t,
        if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧
            q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0) =
      ∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ i : Fin t, ∑ q₃ ∈ P,
        if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧
            q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      apply Finset.sum_congr rfl
      intro q₂ hq₂
      exact Finset.sum_comm
    _ ≤ ∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ i : Fin t,
        d * (if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
          (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro q₁ hq₁
      apply Finset.sum_le_sum
      intro q₂ hq₂
      apply Finset.sum_le_sum
      intro i hi
      by_cases hmem : q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
          q₁ ∈ mtHarmanSameCellFibre endpoint i q₂
      · simpa only [hmem, true_and, if_true, d] using
          sum_tripleDvdIndicator_le_divisors_mul_pairIndicator P q₁ q₂ hn
      · have hright : ¬(q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n) := by
          intro h
          exact hmem ⟨h.1, h.2.1⟩
        rw [if_neg hright, mul_zero]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro q₃ hq₃
        rw [if_neg]
        intro h
        exact hmem ⟨h.1, h.2.1⟩
    _ = d * (∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ i : Fin t,
        if q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
            q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ∧ q₁ * q₂ ∣ n then
          (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q₂ hq₂
      rw [Finset.mul_sum]
    _ = d * ∑ i : Fin t, primePairDivisorCount
        (mtAdjacentPrimeBlock endpoint i) (mtHarmanSameCellFibre endpoint i) n := by
      rw [mtHarmanPairGlobalCollisionCount_eq hmono]

private theorem mtHarmanTripleBoundaryGrid_le
    {t : ℕ} (endpoint : ℕ → ℕ) (δ E : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∑ q₁ ∈ primesIco (endpoint 0) (endpoint t),
      ∑ q₂ ∈ primesIco (endpoint 0) (endpoint t),
      ∑ q₃ ∈ primesIco (endpoint 0) (endpoint t),
        if q₁ ∈ mtHarmanThresholdBoundaryFibre
              (primesIco (endpoint 0) (endpoint t)) δ E q₂ ∧
            q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0) ≤
      (n.divisors.card : ℝ) *
        primePairDivisorCount (primesIco (endpoint 0) (endpoint t))
          (fun q₂ => mtHarmanThresholdBoundaryFibre
            (primesIco (endpoint 0) (endpoint t)) δ E q₂) n := by
  let P := primesIco (endpoint 0) (endpoint t)
  let d : ℝ := n.divisors.card
  calc
    (∑ q₁ ∈ P, ∑ q₂ ∈ P, ∑ q₃ ∈ P,
        if q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂ ∧
            q₁ * q₂ * q₃ ∣ n then (1 : ℝ) else 0) ≤
      ∑ q₁ ∈ P, ∑ q₂ ∈ P,
        d * (if q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂ ∧
            q₁ * q₂ ∣ n then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro q₁ hq₁
      apply Finset.sum_le_sum
      intro q₂ hq₂
      by_cases hmem : q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂
      · simpa only [hmem, true_and, if_true, d] using
          sum_tripleDvdIndicator_le_divisors_mul_pairIndicator P q₁ q₂ hn
      · have hright : ¬(q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂ ∧
            q₁ * q₂ ∣ n) := fun h => hmem h.1
        rw [if_neg hright, mul_zero]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro q₃ hq₃
        simp [hmem]
    _ = d * (∑ q₁ ∈ P, ∑ q₂ ∈ P,
        if q₁ ∈ mtHarmanThresholdBoundaryFibre P δ E q₂ ∧
            q₁ * q₂ ∣ n then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      rw [Finset.mul_sum]
    _ = d * primePairDivisorCount P
        (fun q₂ => mtHarmanThresholdBoundaryFibre P δ E q₂) n := by
      rw [mtHarmanPairGlobalBoundaryCount_eq]

end

end RHTower.Sieve
