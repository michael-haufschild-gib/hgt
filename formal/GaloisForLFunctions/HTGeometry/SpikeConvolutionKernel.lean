import GaloisForLFunctions.HTGeometry.NearDiagonalHarmonicTail
import GaloisForLFunctions.HTGeometry.HarmonicPowerConvolution

/-!
# A harmonic kernel against a power spike

Convolving a harmonic kernel with the weight `r^{-c}` carried on a band produces, at distance `s`
from the band centre, at most a logarithmic multiple of `(1 + |s|)^{-c}`: the same power, with only
a logarithm lost.  Away from the band that is weighted arithmetic–geometric mean applied to
`1 + |s| + r ≥ (1 + |s|)^c r^{1-c}`; on the band it is the split into the three ranges `r ≤ s/2`,
`s/2 < r ≤ 2s` and `r > 2s`, the middle one being where the logarithm appears.

This is the estimate a spike-to-spike transfer needs: a harmonic convolution keeps the shape of a
power spike and multiplies its height by a logarithm.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- Weighted arithmetic–geometric mean in the form used here. -/
theorem rpow_mul_rpow_le_add {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ c * b ^ (1 - c) ≤ a + b := by
  have hw : c + (1 - c) = 1 := by ring
  have h := Real.geom_mean_le_arith_mean2_weighted hc0 (by linarith) ha hb hw
  have h2 : c * a + (1 - c) * b ≤ a + b := by nlinarith
  linarith

/-- **The far side of the spike.**  When the base point lies outside the band, the harmonic kernel
against a power spike is bounded by a harmonic sum times the same power. -/
theorem sum_harmonic_rpow_neg_le_of_nonpos {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (N : ℕ) {m : ℕ} :
    ∑ r ∈ Finset.Icc 1 N, 1 / ((1 + (m : ℝ) + (r : ℝ)) * (r : ℝ) ^ c)
      ≤ (1 / (1 + (m : ℝ)) ^ c) * ∑ r ∈ Finset.Icc 1 N, 1 / (r : ℝ) := by
  have hm0 : (0 : ℝ) < 1 + (m : ℝ) := by positivity
  have hstep : ∀ r ∈ Finset.Icc 1 N,
      1 / ((1 + (m : ℝ) + (r : ℝ)) * (r : ℝ) ^ c)
        ≤ (1 / (1 + (m : ℝ)) ^ c) * (1 / (r : ℝ)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.1
    have hgm : (1 + (m : ℝ)) ^ c * (r : ℝ) ^ (1 - c) ≤ (1 + (m : ℝ)) + (r : ℝ) :=
      rpow_mul_rpow_le_add hc0.le hc1.le hm0.le hr0.le
    have hden : (0 : ℝ) < (1 + (m : ℝ)) ^ c * (r : ℝ) ^ (1 - c) := by
      have h1 : (0 : ℝ) < (1 + (m : ℝ)) ^ c := Real.rpow_pos_of_pos hm0 _
      have h2 : (0 : ℝ) < (r : ℝ) ^ (1 - c) := Real.rpow_pos_of_pos hr0 _
      positivity
    have hprod : (r : ℝ) ^ (1 - c) * (r : ℝ) ^ c = (r : ℝ) := by
      rw [← Real.rpow_add hr0]
      norm_num
    have hkey : (1 + (m : ℝ)) ^ c * (r : ℝ) ≤ ((1 + (m : ℝ)) + (r : ℝ)) * (r : ℝ) ^ c := by
      calc (1 + (m : ℝ)) ^ c * (r : ℝ)
          = ((1 + (m : ℝ)) ^ c * (r : ℝ) ^ (1 - c)) * (r : ℝ) ^ c := by
            rw [mul_assoc, hprod]
        _ ≤ ((1 + (m : ℝ)) + (r : ℝ)) * (r : ℝ) ^ c :=
            mul_le_mul_of_nonneg_right hgm (Real.rpow_nonneg hr0.le _)
    have hposa : (0 : ℝ) < (1 + (m : ℝ)) ^ c * (r : ℝ) := by
      have := Real.rpow_pos_of_pos hm0 c
      positivity
    have h1 : 1 / ((1 + (m : ℝ) + (r : ℝ)) * (r : ℝ) ^ c)
        ≤ 1 / ((1 + (m : ℝ)) ^ c * (r : ℝ)) := by
      refine one_div_le_one_div_of_le hposa ?_
      have hrw : (1 + (m : ℝ) + (r : ℝ)) * (r : ℝ) ^ c
          = ((1 + (m : ℝ)) + (r : ℝ)) * (r : ℝ) ^ c := by ring
      rw [hrw]
      exact hkey
    have h2 : (1 / (1 + (m : ℝ)) ^ c) * (1 / (r : ℝ))
        = 1 / ((1 + (m : ℝ)) ^ c * (r : ℝ)) := one_div_mul_one_div _ _
    rw [h2]
    exact h1
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]

end GaloisForLFunctions.HTGeometry
