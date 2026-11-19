import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ArbitraryJumpsOfCumulativeMass

/-!
# What a logarithmic discount measures across a large jump

The reciprocal charge on a cell reads its logarithmic length truncated
at one, within a factor of two. This describes the logarithmic discount
on every partition, even when adjacent masses differ by arbitrarily large
factors. Bounded *ratios* already preserve the marginal summability law
of Fino–Majdoub (arXiv:2611.24340, Lemma 2.1).
-/

noncomputable section
open Set Filter
namespace GaloisForLFunctions.CumulativeQuadrature

private theorem log_increment_le_ratio_charge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {R : ℝ} (hR : 1+b ≤ R*(1+a)) :
    Real.log (1+b)-Real.log (1+a) ≤ R*((b-a)/(1+b)) := by
  have hA := add_pos_of_pos_of_nonneg zero_lt_one ha
  have hB := add_pos_of_pos_of_nonneg zero_lt_one (ha.trans hab)
  have h := Real.log_le_sub_one_of_pos (div_pos hB hA)
  rw [Real.log_div hB.ne' hA.ne'] at h
  have he : (1+b)/(1+a)-1 = ((1+b)/(1+a))*((b-a)/(1+b)) := by
    field_simp
    ring
  exact h.trans (he.le.trans (mul_le_mul_of_nonneg_right ((div_le_iff₀ hA).mpr hR)
    (div_nonneg (sub_nonneg.mpr hab) hB.le)))

/-- A reciprocal endpoint charge reads the smaller of one and the logarithmic
cell length. The comparison constants are independent of both endpoints. -/
theorem clipped_logarithmic_cell {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b-a)/(1+b) ≤ min 1 (Real.log (1+b)-Real.log (1+a)) ∧
    min 1 (Real.log (1+b)-Real.log (1+a)) ≤ 2*((b-a)/(1+b)) := by
  have hB := add_pos_of_pos_of_nonneg zero_lt_one (ha.trans hab)
  refine ⟨le_min ((div_le_one hB).mpr (by linarith only [ha])) (logarithmic_cell ha hab).1,?_⟩
  by_cases h : 1+b ≤ 2*(1+a)
  · exact (min_le_right ..).trans (log_increment_le_ratio_charge ha hab h)
  · apply (min_le_left ..).trans
    rw [←mul_div_assoc,le_div_iff₀ hB]
    linarith only [le_of_not_ge h]

/-- The logarithmic discount on an arbitrary partition is summable exactly
when the truncated logarithmic increments with the same weight are summable. -/
theorem log_discount_iff_clipped_increments {x : ℕ → ℝ} (hx : Monotone x) (h₀ : 0 ≤ x 0) (p : ℝ) :
    Summable (logPowerCharge x p) ↔ Summable (fun i : ℕ =>
      min 1 (Real.log (1+x (i+1))-Real.log (1+x i))*(1+Real.log (1+x (i+1)))^(-p)) := by
  let y := fun i => Real.log (1+x i)
  have hn (i : ℕ) := h₀.trans (hx (Nat.zero_le i))
  have hy (i : ℕ) : 0 ≤ y i := Real.log_nonneg (le_add_of_nonneg_right (hn _))
  have hw (i : ℕ) := Real.rpow_nonneg (add_nonneg zero_le_one (hy (i+1))) (-p)
  have hc (i : ℕ) : powerCharge x 1 i ≤ min 1 (y (i+1)-y i) ∧
      min 1 (y (i+1)-y i) ≤ 2*powerCharge x 1 i := by
    simpa only [powerCharge,Real.rpow_neg_one,←div_eq_mul_inv,y] using
      clipped_logarithmic_cell (hn i) (hx (Nat.le_succ i))
  have hq (i : ℕ) : 0 ≤ powerCharge x 1 i :=
    mul_nonneg (sub_nonneg.mpr (hx (Nat.le_succ i))) (Real.rpow_nonneg (by linarith only [hn (i+1)]) _)
  constructor
  · intro hh
    apply (hh.mul_left 2).of_nonneg_of_le
      (fun i => mul_nonneg ((hq i).trans (hc i).1) (hw i))
    exact fun i => (mul_le_mul_of_nonneg_right (hc i).2 (hw i)).trans_eq (mul_assoc ..)
  · intro hh
    exact hh.of_nonneg_of_le (fun i => mul_nonneg (hq i) (hw i))
      (fun i => mul_le_mul_of_nonneg_right (hc i).1 (hw i))

/-- Bounded ratios between successive shifted masses suffice for the exact
logarithmic threshold, even for arbitrarily large additive jumps. -/
theorem log_discount_iff_of_bounded_ratios {x : ℕ → ℝ} (hx : Monotone x) (h₀ : 0 ≤ x 0)
    {R : ℝ} (hr : ∀ i, 1+x (i+1) ≤ R*(1+x i)) (p : ℝ) :
    Summable (logPowerCharge x p) ↔ 1 < p ∨ BddAbove (Set.range x) := by
  let y := fun i => Real.log (1+x i)
  have hn (i : ℕ) := h₀.trans (hx (Nat.zero_le i))
  have hpos (i : ℕ) := add_pos_of_pos_of_nonneg zero_lt_one (hn i)
  have hy₀ (i : ℕ) : 0 ≤ y i := Real.log_nonneg (le_add_of_nonneg_right (hn i))
  have hy : Monotone y := fun i j hij =>
    Real.log_le_log (hpos i) (add_le_add (le_refl 1) (hx hij))
  have hbound : BddAbove (range y) ↔ BddAbove (range x) := by
    constructor
    · rintro ⟨B,hB⟩
      refine ⟨Real.exp B,?_⟩
      rintro _ ⟨i,rfl⟩
      have hh := Real.exp_le_exp.mpr (hB (mem_range_self i))
      change Real.exp (Real.log (1+x i)) ≤ Real.exp B at hh
      rw [Real.exp_log (hpos i)] at hh
      linarith only [hh]
    · rintro ⟨B,hB⟩
      exact ⟨Real.log (1+B),fun _ ⟨i,hi⟩ => hi ▸
        Real.log_le_log (hpos i) (add_le_add_left (hB (mem_range_self i)) 1)⟩
  rw [←hbound,←summable_power_charge_arbitrary_jumps hy (hy₀ 0)]
  have hw (i : ℕ) := Real.rpow_nonneg (add_nonneg zero_le_one (hy₀ (i+1))) (-p)
  have hcell (i : ℕ) : powerCharge x 1 i ≤ y (i+1)-y i ∧
      y (i+1)-y i ≤ R*powerCharge x 1 i := by
    simp only [powerCharge,Real.rpow_neg_one,←div_eq_mul_inv,y]
    exact ⟨(logarithmic_cell (hn i) (hx (Nat.le_succ i))).1,
      log_increment_le_ratio_charge (hn i) (hx (Nat.le_succ i)) (hr i)⟩
  constructor
  · intro h
    exact (h.mul_left R).of_nonneg_of_le (fun i => mul_nonneg (sub_nonneg.mpr (hy (Nat.le_succ i))) (hw i))
      (fun i => (mul_le_mul_of_nonneg_right (hcell i).2 (hw i)).trans_eq (mul_assoc ..))
  · intro h
    apply h.of_nonneg_of_le _ (fun i => mul_le_mul_of_nonneg_right (hcell i).1 (hw i))
    exact fun i => mul_nonneg (mul_nonneg (sub_nonneg.mpr (hx (Nat.le_succ i)))
      (Real.rpow_nonneg (hpos _).le _)) (hw i)

#print axioms clipped_logarithmic_cell
#print axioms log_discount_iff_clipped_increments
#print axioms log_discount_iff_of_bounded_ratios

end GaloisForLFunctions.CumulativeQuadrature
