import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBlockProducts

/-!
# Sharp real-power thresholds for products of homogeneous shear blocks

The product lower bound excludes every real exponent larger than the sum
of the block exponents. The product upper bound holds uniformly over all
independent cube centers and proves the converse.
-/

open Filter MeasureTheory

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- The regularized product volume has a uniform real upper bound for all cube centers. -/
theorem exists_regularized_block_volume_upper (m : ι → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (a b : BlockSpace m),
      (1 + |θ|) ^ blockExponent m * (volume (blockOverlap m θ a b)).toReal ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_block_overlap_decay m
  refine ⟨C, hC, fun θ a b => ?_⟩
  have hp : 0 < (1 + |θ|) ^ blockExponent m := by positivity
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound θ a b)
  rw [ENNReal.toReal_ofReal (div_nonneg hC.le hp.le)] at h
  simpa only [mul_comm] using (le_div_iff₀ hp).mp h

/-- At common zero center the regularized product volume has a positive lower bound. -/
theorem exists_regularized_block_volume_lower (m : ι → ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ : ℝ,
      c ≤ (1 + |θ|) ^ blockExponent m * (volume (blockOverlap m θ 0 0)).toReal := by
  obtain ⟨c, C, hc, hC, hbound⟩ := exists_block_overlap_two_sided m
  refine ⟨c, hc, fun θ => ?_⟩
  have hp : 0 < (1 + |θ|) ^ blockExponent m := by positivity
  have hfinite : volume (blockOverlap m θ 0 0) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (volume_blockOverlap_le m θ 0 0)
  have h := ENNReal.toReal_mono hfinite (hbound θ).1
  rw [ENNReal.toReal_ofReal (div_nonneg hc.le hp.le)] at h
  simpa only [mul_comm] using (div_le_iff₀ hp).mp h

/-- The optimal weight for a product of centered blocks is the sum of their exponents. -/
theorem bounded_block_overlap_iff (m : ι → ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ θ : ℝ,
      (1 + |θ|) ^ p * (volume (blockOverlap m θ 0 0)).toReal ≤ C) ↔
        p ≤ (blockExponent m : ℝ) := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨c, hc, hlo⟩ := exists_regularized_block_volume_lower m
    by_contra hp
    have hd : 0 < p - blockExponent m := sub_pos.mpr (lt_of_not_ge hp)
    have hg : ∀ᶠ x : ℝ in atTop, (|C| + 1) / c < x ^ (p - blockExponent m) :=
      (tendsto_rpow_atTop hd).eventually (eventually_gt_atTop ((|C| + 1) / c))
    obtain ⟨x, hxg, hx⟩ := (hg.and (eventually_ge_atTop (1 : ℝ))).exists
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hb : 1 + |x - 1| = x := by rw [abs_of_nonneg (sub_nonneg.mpr hx)]; ring
    have hl := hlo (x - 1)
    have hu := hC (x - 1)
    rw [hb] at hl hu
    have hmul := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hx0.le (p - blockExponent m))
    have he : x ^ (p - blockExponent m) * x ^ blockExponent m = x ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
      congr 1
      ring
    have hbound : x ^ (p - blockExponent m) * c ≤ C := by
      calc
        _ ≤ x ^ (p - blockExponent m) *
            (x ^ blockExponent m * (volume (blockOverlap m (x - 1) 0 0)).toReal) := hmul
        _ = x ^ p * (volume (blockOverlap m (x - 1) 0 0)).toReal := by rw [← mul_assoc, he]
        _ ≤ C := hu
    have hxg' := (div_lt_iff₀ hc).mp hxg
    linarith only [hbound, hxg', le_abs_self C]
  · intro hp
    obtain ⟨C, _, hC⟩ := exists_regularized_block_volume_upper m
    refine ⟨C, fun θ => ?_⟩
    have hb : 1 ≤ 1 + |θ| := by linarith only [abs_nonneg θ]
    have hpow : (1 + |θ|) ^ p ≤ (1 + |θ|) ^ blockExponent m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans (hC θ 0 0)

/-- Uniformity over all cube centers leaves the same sharp summed threshold. -/
theorem bounded_block_overlap_uniform_centers_iff (m : ι → ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ : ℝ) (a b : BlockSpace m),
      (1 + |θ|) ^ p * (volume (blockOverlap m θ a b)).toReal ≤ C) ↔
        p ≤ (blockExponent m : ℝ) := by
  constructor
  · rintro ⟨C, hC⟩
    exact (bounded_block_overlap_iff m p).mp ⟨C, fun θ => hC θ 0 0⟩
  · intro hp
    obtain ⟨C, _, hC⟩ := exists_regularized_block_volume_upper m
    refine ⟨C, fun θ a b => ?_⟩
    have hb : 1 ≤ 1 + |θ| := by linarith only [abs_nonneg θ]
    have hpow : (1 + |θ|) ^ p ≤ (1 + |θ|) ^ blockExponent m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans (hC θ a b)

#print axioms exists_regularized_block_volume_upper
#print axioms exists_regularized_block_volume_lower
#print axioms bounded_block_overlap_iff
#print axioms bounded_block_overlap_uniform_centers_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
