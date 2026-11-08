import GaloisForLFunctions.SelbergClass.Primon.KestenTiltedBetaLaw
import GaloisForLFunctions.HTGeometry.PowerMomentSupport

/-!
# The rational beta likelihood crosses one at its own mean

The reciprocal density is affine in the square coordinate. The prime
moment recurrence identifies its unit level with the mean of the tilted
prime law. Thus the sign of the density change is exactly the sign of
displacement from that mean, at every prime and every degree.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Mean square coordinate under the power-weighted prime law. -/
def kestenTiltedSquareMean (p : Nat.Primes) (n : ℕ) : ℝ :=
  ∫ u : ℝ, u ∂(kestenTiltedSquareLaw p n : Measure ℝ)

/-- The mean is an explicit transform of the prime-to-Catalan moment ratio. -/
theorem kestenTiltedSquareMean_eq (p : Nat.Primes) (n : ℕ) :
    kestenTiltedSquareMean p n =
      (((p : ℝ) + 1) ^ 2 / (p : ℝ) - ((p : ℝ) + 1) / kestenMomentRatio p n) / 4 := by
  have h := integral_kestenTiltedSquareLaw_pow p n 1
  simp only [pow_one] at h
  change kestenTiltedSquareMean p n = _ at h
  rw [h, ← kestenMoment_successive_ratio p n]
  ring

/-- The mean lies strictly inside the unit interval. -/
theorem kestenTiltedSquareMean_mem (p : Nat.Primes) (n : ℕ) :
    kestenTiltedSquareMean p n ∈ Ioo (0 : ℝ) 1 := by
  have hm := integral_kestenTiltedSquareLaw_pow p n 1
  simp only [pow_one] at hm
  have hp : 0 < kestenTiltedSquareMean p n := by
    change 0 < ∫ u : ℝ, u ∂(kestenTiltedSquareLaw p n : Measure ℝ)
    rw [hm]
    exact div_pos (kestenMoment_even_pos p (n + 1))
      (mul_pos (by norm_num) (kestenMoment_even_pos p n))
  have hi : Integrable (fun u : ℝ => u) (kestenTiltedSquareLaw p n : Measure ℝ) := by
    by_contra hn
    have hz : kestenTiltedSquareMean p n = 0 := integral_undef hn
    exact hp.ne' hz
  have hs : ∀ᵐ u ∂(kestenTiltedSquareLaw p n : Measure ℝ), 0 < u ∧ u < 1 := by
    rw [kestenTiltedSquareLaw_eq_beta_withDensity]
    exact (withDensity_absolutelyContinuous _ _)
      (ae_mem_Ioo_betaMeasure ((n : ℝ) + 1 / 2) (3 / 2))
  have hu := _root_.HTGeometry.integral_pow_succ_lt_upper_mul_integral_pow_of_ae_pos_lt
    (mu := (kestenTiltedSquareLaw p n : Measure ℝ)) (f := fun u : ℝ => u) (R := 1) 0
    (by simpa only [pow_zero] using (integrable_const (1 : ℝ)))
    (by simpa only [Nat.zero_add, pow_one] using hi) hs
  refine ⟨hp, ?_⟩
  change (∫ u : ℝ, u ∂(kestenTiltedSquareLaw p n : Measure ℝ)) < 1
  simpa only [Nat.zero_add, pow_one, pow_zero, integral_const, probReal_univ,
    one_smul, mul_one] using hu

/-- Normalization pins the affine reciprocal density to one at the tilted mean. -/
theorem kestenTiltedSquareMean_density_identity (p : Nat.Primes) (n : ℕ) :
    (1 + 4 * kestenEdgeSlope p * (1 - kestenTiltedSquareMean p n)) *
      kestenMomentRatio p n = kestenEdgeScale p := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith only [hp])
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith only [hp])
  rw [kestenTiltedSquareMean_eq]
  unfold kestenEdgeSlope kestenEdgeScale
  field_simp [hp0, hp1, (kestenMomentRatio_pos p n).ne']
  ring

private theorem unit_denominator_pos (p : Nat.Primes) (u : Icc (0 : ℝ) 1) :
    0 < 1 + 4 * kestenEdgeSlope p * (1 - (u : ℝ)) := by
  have h := mul_nonneg
    (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (kestenEdgeSlope_pos p).le)
    (sub_nonneg.mpr u.property.2)
  linarith only [h]

/-- Exact centered form of the rational beta likelihood ratio. -/
theorem kestenBetaLikelihood_centered (p : Nat.Primes) (n : ℕ) (u : Icc (0 : ℝ) 1) :
    kestenBetaWeight p u / kestenMomentRatio p n - 1 =
      (4 * kestenEdgeSlope p / (1 + 4 * kestenEdgeSlope p * (1 - (u : ℝ)))) *
        ((u : ℝ) - kestenTiltedSquareMean p n) := by
  rw [kestenBetaWeight_on_unit]
  have h := kestenTiltedSquareMean_density_identity p n
  field_simp [(kestenMomentRatio_pos p n).ne', (unit_denominator_pos p u).ne']
  nlinarith only [h]

/-- The rational beta likelihood is at most one exactly below its own tilted mean. -/
theorem kestenBetaLikelihood_le_one_iff (p : Nat.Primes) (n : ℕ) (u : Icc (0 : ℝ) 1) :
    kestenBetaWeight p u / kestenMomentRatio p n ≤ 1 ↔
      (u : ℝ) ≤ kestenTiltedSquareMean p n := by
  have hc : 0 < 4 * kestenEdgeSlope p /
      (1 + 4 * kestenEdgeSlope p * (1 - (u : ℝ))) :=
    div_pos (mul_pos (by norm_num) (kestenEdgeSlope_pos p)) (unit_denominator_pos p u)
  have he := kestenBetaLikelihood_centered p n u
  constructor
  · intro h
    by_contra hn
    have hs := mul_pos hc (sub_pos.mpr (lt_of_not_ge hn))
    linarith only [h, he, hs]
  · intro h
    have hs := mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr h)
    linarith only [he, hs]

/-- The unit likelihood level is attained precisely at the tilted mean. -/
theorem kestenBetaLikelihood_eq_one_iff (p : Nat.Primes) (n : ℕ) (u : Icc (0 : ℝ) 1) :
    kestenBetaWeight p u / kestenMomentRatio p n = 1 ↔
      (u : ℝ) = kestenTiltedSquareMean p n := by
  have hc : 0 < 4 * kestenEdgeSlope p /
      (1 + 4 * kestenEdgeSlope p * (1 - (u : ℝ))) :=
    div_pos (mul_pos (by norm_num) (kestenEdgeSlope_pos p)) (unit_denominator_pos p u)
  rw [← sub_eq_zero, kestenBetaLikelihood_centered, mul_eq_zero]
  simp only [hc.ne', false_or, sub_eq_zero]

/-- The unique unit likelihood level is attained at the actual tilted mean. -/
theorem kestenBetaLikelihood_at_mean (p : Nat.Primes) (n : ℕ) :
    kestenBetaWeight p (kestenTiltedSquareMean p n) / kestenMomentRatio p n = 1 := by
  have hm := kestenTiltedSquareMean_mem p n
  exact (kestenBetaLikelihood_eq_one_iff p n
    ⟨kestenTiltedSquareMean p n, hm.1.le, hm.2.le⟩).2 rfl

end
end GaloisForLFunctions.SelbergClass.Primon
