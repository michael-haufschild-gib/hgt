import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Refinement

/-! # Telescoping a block of clipped levels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

private theorem clip_difference {E : Type*} [AddCommGroup E] (F : ℝ → E) {l u : ℝ} (hlu : l ≤ u) (t : ℝ) :
    F u-F (min u (max l t)) = F (max u t)-F (max l t) := by
  by_cases hl : t ≤ l
  · simp only [max_eq_left hl,max_eq_left (hl.trans hlu),min_eq_right hlu]
  by_cases hu : t ≤ u
  · simp only [max_eq_right (le_of_not_ge hl),min_eq_right hu,max_eq_left hu]
  · simp only [max_eq_right (le_of_not_ge hl),max_eq_right (le_of_not_ge hu),
      min_eq_left (le_of_not_ge hu),sub_self]

/-- Every test function telescopes over one block, including at coincident levels. -/
theorem refined_block_sum {E : Type*} [AddCommGroup E] (F : ℝ → E) (a : ℕ+) (b : SpectralBand 1) (n : ℕ) :
    ∑ r ∈ Finset.range a.val, (F (occupationWeight (sectorStart a n+r))-F (refinedSpectrum a b (sectorStart a n+r)).val) =
      F (sectorWeight a*occupationWeight n)-F (sectorWeight a*(b n).val) := by
  let s := sectorStart a n
  let t := sectorWeight a*(b n).val
  let V (r : ℕ) := F (max (occupationWeight (s+r)) t)
  have he : ∀ r ∈ Finset.range a.val,
      F (occupationWeight (s+r))-F (refinedSpectrum a b (s+r)).val = V r - V (r+1) := by
    intro r hr
    rw [refined_block a b n r (Finset.mem_range.mp hr)]
    simpa only [V,Nat.succ_eq_add_one,Nat.add_assoc] using
      (clip_difference F (occupationWeight_antitone (Nat.le_succ (s+r))) t)
  have ht : t ≤ occupationWeight s := by
    rw [show occupationWeight s = _ from occupationWeight_sectorStart a n]
    exact mul_le_mul_of_nonneg_left (b n).property.2 (sectorWeight_pos a).le
  have hb : occupationWeight (s+a.val) ≤ t := by
    rw [← sectorStart_succ,occupationWeight_sectorStart]
    exact mul_le_mul_of_nonneg_left (b n).property.1 (sectorWeight_pos a).le
  rw [Finset.sum_congr rfl he,Finset.sum_range_sub']
  simp only [V,Nat.add_zero,max_eq_left ht,max_eq_right hb]
  rw [occupationWeight_sectorStart]

private theorem positive_cpow (x : ℝ) (hx : 0 < x) (z : ℂ) :
    (x:ℂ)^z = Complex.exp ((Real.log x:ℂ)*z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),Complex.ofReal_log hx.le]

/-- The complex power of a rescaled positive level factors at all temperatures. -/
theorem sector_cpow (a : ℕ+) {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((sectorWeight a*x:ℝ):ℂ)^z = heat z a*(x:ℂ)^z := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (sectorWeight_pos a).le hx.le,
    positive_cpow _ (sectorWeight_pos a),sectorWeight_eq_inv,Real.log_inv,Complex.ofReal_neg,heat,energy]
  congr 2
  ring

theorem refined_block_drop (a : ℕ+) (b : SpectralBand 1) (n : ℕ) (z : ℂ) :
    ∑ r ∈ Finset.range a.val, complexDrop (refinedSpectrum a b) (sectorStart a n+r) z =
      heat z a*complexDrop b n z := by
  unfold complexDrop
  rw [refined_block_sum (fun x : ℝ => (x:ℂ)^z),sector_cpow a (occupationWeight_pos n),sector_cpow a (band_pos b n),mul_sub]

#print axioms refined_block_sum
#print axioms sector_cpow
#print axioms refined_block_drop

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
