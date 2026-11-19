import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CumulativePowerDiscount

/-!
# Reciprocal charges without a mesh bound

On any increasing partition, a block of reciprocal right-endpoint charges
lies between the relative gain at its terminal point and the logarithmic
gain over the block. The lower estimate survives arbitrary jumps: a small
remaining charge forces a bounded remaining mass. The integrability
threshold of the power discount therefore survives arbitrary coarsening.
-/

noncomputable section
open Finset Filter
open scoped Topology

namespace GaloisForLFunctions.CumulativeQuadrature

/-- Finite two-sided estimate for a block, independent of every interior
step length. The lower bound is attained by a single jump. -/
theorem reciprocal_block_bounds {x : ℕ → ℝ} (hx : Monotone x) (h₀ : 0 ≤ x 0) (K n : ℕ) :
    (x (K+n)-x K)/(1+x (K+n)) ≤ ∑ i ∈ range n, powerCharge x 1 (K+i) ∧
      (∑ i ∈ range n, powerCharge x 1 (K+i)) ≤ Real.log (1+x (K+n))-Real.log (1+x K) := by
  have hn (i : ℕ) := h₀.trans (hx (Nat.zero_le i))
  have step (i : ℕ) : powerCharge x 1 (K+i) =
      (x (K+(i+1))-x (K+i))/(1+x (K+(i+1))) := by
    simp only [powerCharge,Real.rpow_neg_one,div_eq_mul_inv,Nat.add_assoc]
  have he := sum_range_sub (fun i => x (K+i)) n
  have hl := sum_range_sub (fun i => Real.log (1+x (K+i))) n
  simp only [Nat.add_zero] at he hl
  constructor
  · rw [←he,Finset.sum_div]
    apply sum_le_sum
    intro i hi
    rw [step]
    apply div_le_div_of_nonneg_left (sub_nonneg.mpr (hx (by omega)))
      (add_pos_of_pos_of_nonneg zero_lt_one (hn _))
    exact add_le_add (le_refl 1) (hx (Nat.add_le_add_left (mem_range.mp hi) K))
  · rw [←hl]
    apply sum_le_sum
    intro i _
    rw [step]
    exact (logarithmic_cell (hn _) (hx (by omega))).1

/-- A total reciprocal charge below b<1 on the rest of a partition
controls all subsequent endpoints by the explicit factor (1-b)⁻¹. -/
theorem mass_bound_of_remaining_charge {x : ℕ → ℝ} (hx : Monotone x) (h₀ : 0 ≤ x 0)
    {K : ℕ} {b : ℝ} (hb : b < 1)
    (h : ∀ n, (∑ i ∈ range n, powerCharge x 1 (K+i)) ≤ b) (n : ℕ) :
    1+x (K+n) ≤ (1+x K)/(1-b) := by
  have hl := ((reciprocal_block_bounds hx h₀ K n).1).trans (h n)
  have hden := add_pos_of_pos_of_nonneg zero_lt_one (h₀.trans (hx (Nat.zero_le (K+n))))
  apply (le_div_iff₀ (sub_pos.mpr hb)).mpr
  linarith only [(div_le_iff₀ hden).mp hl]

/-- The power threshold remains sharp even for unbounded steps. A finite
tail of reciprocal charges is eventually smaller than one half and so
bounds the complete cumulative mass. -/
theorem summable_power_charge_arbitrary_jumps {x : ℕ → ℝ} (hx : Monotone x) (h₀ : 0 ≤ x 0)
    (p : ℝ) : Summable (powerCharge x p) ↔ 1 < p ∨ BddAbove (Set.range x) := by
  have hn (i : ℕ) := h₀.trans (hx (Nat.zero_le i))
  have hd (i : ℕ) := sub_nonneg.mpr (hx (Nat.le_succ i))
  have hpos (q : ℝ) (i : ℕ) : 0 ≤ powerCharge x q i := mul_nonneg (hd i)
    (Real.rpow_nonneg (add_nonneg zero_le_one (hn _)) _)
  constructor
  · intro hs
    by_cases hp : 1 < p
    · exact Or.inl hp
    right
    have hr : Summable (powerCharge x 1) := hs.of_nonneg_of_le (hpos 1) fun i =>
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
        (le_add_of_nonneg_right (hn (i+1))) (neg_le_neg (le_of_not_gt hp))) (hd i)
    let A := ∑' i, powerCharge x 1 i
    obtain ⟨K,hK⟩ := (hr.hasSum.tendsto_sum_nat.eventually_const_lt
      (show A-1/2 < A by linarith only)).exists
    have htail (n : ℕ) : (∑ i ∈ range n, powerCharge x 1 (K+i)) ≤ 1/2 := by
      have ht := hr.sum_le_tsum (range (K+n)) (fun i _ => hpos 1 i)
      rw [sum_range_add] at ht
      change _ ≤ A at ht
      linarith only [ht,hK]
    refine ⟨(1+x K)/(1-1/2),?_⟩
    rintro _ ⟨i,rfl⟩
    have hh := mass_bound_of_remaining_charge hx h₀ (by norm_num : (1/2:ℝ)<1) htail i
    linarith only [hh,hx (Nat.le_add_left i K)]
  · rintro (hp|hB)
    · apply summable_of_sum_range_le (hpos p)
      exact fun n => by simpa only [Nat.zero_add] using power_prefix_bound hx h₀ 0 n hp
    obtain ⟨B,hB'⟩ := hB
    have hm (i : ℕ) : x (i+1)-x i ≤ B := (sub_le_self _ (hn i)).trans (hB' ⟨i+1,rfl⟩)
    exact (summable_power_charge_iff hx h₀ hm p).mpr (Or.inr ⟨B,hB'⟩)

#print axioms reciprocal_block_bounds
#print axioms mass_bound_of_remaining_charge
#print axioms summable_power_charge_arbitrary_jumps

end GaloisForLFunctions.CumulativeQuadrature
