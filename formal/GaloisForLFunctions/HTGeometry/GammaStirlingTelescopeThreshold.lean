import GaloisForLFunctions.HTGeometry.GammaStirlingTelescope

/-!
# The telescope with an arbitrary threshold

`norm_le_of_step_bound` demands the one-step bound on the whole region `‖w‖ ≥ 2`.  A shifted ladder
`ψ(s+μ) - log s + …` only has it for `‖s‖ ≥ R(μ)`, since the rational factor `1/(1+μ/s)` has to stay
bounded.  The telescope is insensitive to this: it only ever evaluates the step at `z, z+1, z+2, …`,
and `‖z+k‖ ≥ ‖z‖` when `Re z > 0`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **The telescope above an arbitrary threshold `R ≥ 2`.** -/
theorem norm_le_of_step_bound_ge {L : ℂ → ℂ} {N : ℕ} {K R : ℝ} (hK : 0 ≤ K) (hR : 2 ≤ R)
    (hstep : ∀ w : ℂ, 0 < w.re → R ≤ ‖w‖ → ‖L (w + 1) - L w‖ ≤ K / ‖w‖ ^ (N + 2))
    {z : ℂ} (hz : 0 < z.re) (h2 : R ≤ ‖z‖)
    (hanchor : Tendsto (fun n : ℕ => L (z + (n : ℂ))) atTop (nhds 0)) :
    ‖L z‖ ≤ (3 * K) / ‖z‖ ^ (N + 1) := by
  have hz2 : (2 : ℝ) ≤ ‖z‖ := le_trans hR h2
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hzre : ∀ k : ℕ, 0 < (z + (k : ℂ)).re := by
    intro k
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hnormR : ∀ k : ℕ, R ≤ ‖z + (k : ℂ)‖ := fun k =>
    le_trans h2 (norm_le_norm_add_natCast hz k)
  have htel : ∀ M : ℕ, L (z + (M : ℂ)) - L z
      = ∑ k ∈ Finset.range M, (L (z + ((k : ℕ) + 1 : ℕ)) - L (z + (k : ℂ))) := by
    intro M
    have h := Finset.sum_range_sub (f := fun k : ℕ => L (z + (k : ℂ))) M
    simpa using h.symm
  have hstepbound : ∀ k : ℕ,
      ‖L (z + ((k : ℕ) + 1 : ℕ)) - L (z + (k : ℂ))‖
        ≤ (2 * K) / (‖z‖ ^ N * (‖z‖ + (k : ℝ)) ^ (2 : ℕ)) := by
    intro k
    have hcast : ((z : ℂ) + (((k : ℕ) + 1 : ℕ) : ℂ)) = (z + (k : ℂ)) + 1 := by
      push_cast
      ring
    rw [hcast]
    refine le_trans (hstep (z + (k : ℂ)) (hzre k) (hnormR k)) ?_
    have hpow := norm_add_natCast_pow_ge hz N k
    have hden : (0 : ℝ) < ‖z‖ ^ N * (‖z‖ + (k : ℝ)) ^ (2 : ℕ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      positivity
    have hcpos : (0 : ℝ) < ‖z + (k : ℂ)‖ ^ (N + 2) := by
      have h1 : (2 : ℝ) ≤ ‖z + (k : ℂ)‖ := le_trans hR (hnormR k)
      positivity
    rw [div_le_div_iff₀ hcpos hden]
    nlinarith [hpow, hden, hcpos, hK]
  have hpartial : ∀ M : ℕ, ‖L (z + (M : ℂ)) - L z‖ ≤ (3 * K) / ‖z‖ ^ (N + 1) := by
    intro M
    rw [htel M]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun k _ => hstepbound k) ?_
    have hrw : ∀ k : ℕ, (2 * K) / (‖z‖ ^ N * (‖z‖ + (k : ℝ)) ^ (2 : ℕ))
        = ((2 * K) / ‖z‖ ^ N) * ((1 : ℝ) / (‖z‖ + (k : ℝ)) ^ (2 : ℕ)) := by
      intro k
      field_simp
    rw [Finset.sum_congr rfl (fun k _ => hrw k), ← Finset.mul_sum]
    have hsum := sum_inv_sq_shift_head_le hzpos M
    have hc0 : (0 : ℝ) ≤ (2 * K) / ‖z‖ ^ N := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hsum hc0) ?_
    have hid : ((2 * K) / ‖z‖ ^ N) * (1 / ‖z‖ ^ (2 : ℕ) + 1 / ‖z‖)
        = (2 * K) / ‖z‖ ^ (N + 2) + (2 * K) / ‖z‖ ^ (N + 1) := by
      rw [pow_add, pow_add]
      field_simp
    rw [hid]
    have hstep1 : (2 * K) / ‖z‖ ^ (N + 2) ≤ K / ‖z‖ ^ (N + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hpow : ‖z‖ ^ (N + 2) = ‖z‖ ^ (N + 1) * ‖z‖ := by ring
      rw [hpow]
      nlinarith [mul_nonneg (mul_nonneg hK (pow_pos hzpos (N + 1)).le)
        (by linarith : (0 : ℝ) ≤ ‖z‖ - 2)]
    have hstep2 : K / ‖z‖ ^ (N + 1) + (2 * K) / ‖z‖ ^ (N + 1) = (3 * K) / ‖z‖ ^ (N + 1) := by
      ring
    linarith
  have hlim : Tendsto (fun M : ℕ => ‖L (z + (M : ℂ)) - L z‖) atTop (nhds ‖L z‖) := by
    have := (hanchor.sub_const (L z)).norm
    simpa using this
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hpartial)

end

end GaloisForLFunctions.HTGeometry
