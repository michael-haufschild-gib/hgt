import GaloisForLFunctions.HTGeometry.GammaStirlingQuarticLog

/-!
# The second rung, telescoped

`‖g₂(z+1) − g₂(z)‖ ≤ 4/‖z‖⁴` and `g₂(z+N) → 0` give, by the same telescope as the first rung,

```text
ψ(z) = log z − 1/(2z) − 1/(12 z²) + O(|z|⁻³).
```

The only new estimate is `‖z+k‖⁴ ≥ ‖z‖²(‖z‖+k)²/2` on the right half-plane, which turns the
one-step gain into the same `∑_k (‖z‖+k)⁻²` sum the first rung used.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

theorem norm_add_natCast_fourth_ge {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    ‖z‖ ^ (2 : ℕ) * (‖z‖ + (k : ℝ)) ^ (2 : ℕ) / 2 ≤ ‖z + (k : ℂ)‖ ^ (4 : ℕ) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hsq : ‖z‖ ^ (2 : ℕ) + (k : ℝ) ^ (2 : ℕ) ≤ ‖z + (k : ℂ)‖ ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im]
    nlinarith [hz, hk]
  have hnn : (0 : ℝ) ≤ ‖z‖ ^ (2 : ℕ) + (k : ℝ) ^ (2 : ℕ) := by positivity
  have hfourth : (‖z‖ ^ (2 : ℕ) + (k : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) ≤ ‖z + (k : ℂ)‖ ^ (4 : ℕ) := by
    have h4 : ‖z + (k : ℂ)‖ ^ (4 : ℕ) = (‖z + (k : ℂ)‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    rw [h4]
    nlinarith [hsq, hnn, sq_nonneg (‖z + (k : ℂ)‖)]
  refine le_trans ?_ hfourth
  nlinarith [sq_nonneg (‖z‖ - (k : ℝ)), hz0, hk, hnn]

set_option maxHeartbeats 1000000 in
theorem tendsto_digammaStirlingDefectTwo_shift_zero {z : ℂ} (hz : 0 ≤ z.re) :
    Tendsto (fun N : ℕ => digammaStirlingDefectTwo (z + (N : ℂ))) atTop (nhds 0) := by
  have hbase := tendsto_digammaStirlingDefect_shift_zero hz
  have hnormlow : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ ‖z + (N : ℂ)‖ := by
    intro N hN
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.add_re, Complex.natCast_re, le_abs]
    left
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have htail : Tendsto (fun N : ℕ => (1 : ℂ) / (12 * (z + (N : ℂ)) ^ (2 : ℕ))) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlow := hnormlow N hN
    rw [norm_div, norm_one, norm_mul, norm_pow]
    have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h12]
    rw [div_le_div_iff₀ (by nlinarith) hNpos]
    nlinarith [hlow, hNpos, hN1]
  have hsum := hbase.add htail
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  rw [digammaStirlingDefect, digammaStirlingDefectTwo]

set_option maxHeartbeats 1000000 in
/-- **The second-rung Stirling bound.**  `ψ(z) = log z − 1/(2z) − 1/(12 z²) + O(|z|⁻³)`. -/
theorem norm_digammaStirlingDefectTwo_le {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖digammaStirlingDefectTwo z‖ ≤ 12 / ‖z‖ ^ (3 : ℕ) := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hzre : ∀ k : ℕ, 0 < (z + (k : ℂ)).re := by
    intro k
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hnorm2 : ∀ k : ℕ, 2 ≤ ‖z + (k : ℂ)‖ := fun k =>
    le_trans h2 (norm_le_norm_add_natCast hz k)
  have htel : ∀ N : ℕ, digammaStirlingDefectTwo (z + (N : ℂ)) - digammaStirlingDefectTwo z
      = ∑ k ∈ Finset.range N,
        (digammaStirlingDefectTwo (z + ((k : ℕ) + 1 : ℕ))
          - digammaStirlingDefectTwo (z + (k : ℂ))) := by
    intro N
    have h := Finset.sum_range_sub
      (f := fun k : ℕ => digammaStirlingDefectTwo (z + (k : ℂ))) N
    simpa using h.symm
  have hstepbound : ∀ k : ℕ,
      ‖digammaStirlingDefectTwo (z + ((k : ℕ) + 1 : ℕ))
        - digammaStirlingDefectTwo (z + (k : ℂ))‖
        ≤ 8 / (‖z‖ ^ (2 : ℕ) * (‖z‖ + (k : ℝ)) ^ (2 : ℕ)) := by
    intro k
    have hcast : ((z : ℂ) + (((k : ℕ) + 1 : ℕ) : ℂ)) = (z + (k : ℂ)) + 1 := by
      push_cast
      ring
    rw [hcast]
    have hstep := norm_digammaStirlingDefectTwo_step_le (hzre k) (hnorm2 k)
    refine le_trans hstep ?_
    have hfourth := norm_add_natCast_fourth_ge hz k
    have hden : (0 : ℝ) < ‖z‖ ^ (2 : ℕ) * (‖z‖ + (k : ℝ)) ^ (2 : ℕ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      positivity
    have hcpos : (0 : ℝ) < ‖z + (k : ℂ)‖ ^ (4 : ℕ) := by
      have := hnorm2 k
      positivity
    rw [div_le_div_iff₀ hcpos hden]
    nlinarith [hfourth, hden, hcpos]
  have hpartial : ∀ N : ℕ,
      ‖digammaStirlingDefectTwo (z + (N : ℂ)) - digammaStirlingDefectTwo z‖
        ≤ 12 / ‖z‖ ^ (3 : ℕ) := by
    intro N
    rw [htel N]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun k _ => hstepbound k) ?_
    have hrw : ∀ k : ℕ, (8 : ℝ) / (‖z‖ ^ (2 : ℕ) * (‖z‖ + (k : ℝ)) ^ (2 : ℕ))
        = (8 / ‖z‖ ^ (2 : ℕ)) * ((1 : ℝ) / (‖z‖ + (k : ℝ)) ^ (2 : ℕ)) := by
      intro k
      field_simp
    rw [Finset.sum_congr rfl (fun k _ => hrw k), ← Finset.mul_sum]
    have hsum := sum_inv_sq_shift_head_le hzpos N
    have h8 : (0 : ℝ) ≤ 8 / ‖z‖ ^ (2 : ℕ) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hsum h8) ?_
    have hid : (8 : ℝ) / ‖z‖ ^ (2 : ℕ) * (1 / ‖z‖ ^ (2 : ℕ) + 1 / ‖z‖)
        = 8 / ‖z‖ ^ (4 : ℕ) + 8 / ‖z‖ ^ (3 : ℕ) := by
      field_simp
    rw [hid]
    have hstep1 : (8 : ℝ) / ‖z‖ ^ (4 : ℕ) ≤ 4 / ‖z‖ ^ (3 : ℕ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h2, hzpos, pow_pos hzpos 3]
    have hstep2 : (4 : ℝ) / ‖z‖ ^ (3 : ℕ) + 8 / ‖z‖ ^ (3 : ℕ) = 12 / ‖z‖ ^ (3 : ℕ) := by ring
    linarith
  have hlim : Tendsto (fun N : ℕ =>
      ‖digammaStirlingDefectTwo (z + (N : ℂ)) - digammaStirlingDefectTwo z‖) atTop
      (nhds ‖digammaStirlingDefectTwo z‖) := by
    have hshift := tendsto_digammaStirlingDefectTwo_shift_zero hz.le
    have := (hshift.sub_const (digammaStirlingDefectTwo z)).norm
    simpa using this
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hpartial)

end

end GaloisForLFunctions.HTGeometry
