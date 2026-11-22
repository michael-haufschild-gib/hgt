import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.PathOverlap

/-! # Counting length-two walks in the Pauli overlap graph with coefficient weights -/
namespace GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
noncomputable section
variable {n : ℕ}

private def row (w : PathLabel n → ℝ) (j : PathLabel n) := ∑ i∈pathOverlaps j, w i

private theorem sum_row (w : PathLabel n → ℝ) (hn : ∀ j, 0≤w j) : (∑ j, row w j) ≤ 42*∑ j, w j := by
  classical
  have hs (i j : PathLabel n) : i∈pathOverlaps j ↔ j∈pathOverlaps i := by
    rw [mem_pathOverlaps,mem_pathOverlaps,disjoint_comm]
  have hr (i : PathLabel n) (f : PathLabel n→ℝ) :
      (∑ j∈pathOverlaps i, f j)=∑ j, if j∈pathOverlaps i then f j else 0 := by
    rw [←Finset.sum_filter]; simp
  have hf : (∑ i, row w i)=∑ i, ∑ _j∈pathOverlaps i,w i := by
    simp only [row]; simp_rw [hr]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => if_congr (hs i j) rfl rfl
  rw [hf,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast pathOverlaps_card_le i) (hn i)

private theorem triple_weight (a b c : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    a*b*c ≤ a^3+b^3+c^3 := by
  let m := max a (max b c)
  have hm : 0≤m := ha.trans (le_max_left ..)
  have h : a*b*c ≤ m^3 := by
    rw [pow_succ,pow_two]
    exact mul_le_mul (mul_le_mul (le_max_left ..) ((le_max_left ..).trans (le_max_right ..)) hb hm)
      ((le_max_right ..).trans (le_max_right ..)) hc (mul_nonneg hm hm)
  apply h.trans
  rcases le_total b c with hbc | hcb
  · simp only [m,max_eq_right hbc]
    rcases le_total a c with h | h <;> simp only [max_eq_right h,max_eq_left h] <;>
      linarith only [pow_nonneg ha 3,pow_nonneg hb 3,pow_nonneg hc 3]
  · simp only [m,max_eq_left hcb]
    rcases le_total a b with h | h <;> simp only [max_eq_right h,max_eq_left h] <;>
      linarith only [pow_nonneg ha 3,pow_nonneg hb 3,pow_nonneg hc 3]

/-- Each of the three possible positions of a fixed coefficient occurs in
at most 42² walks with a named middle label. -/
theorem overlap_triple_mass (a : PathLabel n→ℝ) (ha : ∀ i, 0≤a i) :
    (∑ j, ∑ i∈pathOverlaps j, ∑ k∈pathOverlaps j, a i*a j*a k) ≤ 3*42^2*∑ i,(a i)^3 := by
  let w (j) := (a j)^3
  have hn (j) : 0≤w j := pow_nonneg (ha j) _
  have hrow (j) : 0≤row w j := Finset.sum_nonneg fun i _ => hn i
  have h (j) : (∑ i∈pathOverlaps j, ∑ k∈pathOverlaps j, a i*a j*a k) ≤
      42*(row w j)+42^2*w j+42*(row w j) := by
    have hc : ((pathOverlaps j).card:ℝ) ≤ 42 := by exact_mod_cast pathOverlaps_card_le j
    apply (Finset.sum_le_sum (fun i (_ : i∈pathOverlaps j) => Finset.sum_le_sum
      (fun k (_ : k∈pathOverlaps j) => triple_weight (a i) (a j) (a k) (ha i) (ha j) (ha k)))).trans
    change (∑ i∈pathOverlaps j, ∑ k∈pathOverlaps j, (w i+w j+w k)) ≤ _
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_right hc (hrow j)
    have h2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) (hn j)
    dsimp only [row] at h1 ⊢
    nlinarith only [h1,h2]
  apply (Finset.sum_le_sum (fun j _ => h j)).trans
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  change 42*(∑ j,row w j)+42^2*(∑ j,w j)+42*(∑ j,row w j) ≤ 3*42^2*(∑ j,w j)
  linarith only [sum_row w hn]

end
end GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
