import GaloisForLFunctions.HTGeometry.GammaStirlingSecondRung

/-!
# The order-independent telescope of the Stirling ladder

Both rungs built so far use the same argument: a one-step bound `‖L(z+1) − L(z)‖ ≤ K/‖z‖^{N+2}`
plus a vanishing anchor gives `‖L(z)‖ ≤ 3K/‖z‖^{N+1}`.  Nothing in it depends on `N` beyond the
elementary inequality

```text
‖z+k‖^{N+2} ≥ ‖z‖^N (‖z‖+k)² / 2      (Re z > 0),
```

which reduces every rung to the *same* sum `∑_k (‖z‖+k)⁻² ≤ ‖z‖⁻² + ‖z‖⁻¹`.

Isolating it here means each further rung of the ladder costs only its Taylor bound for
`log(1+u)` and the algebraic cancellation that fixes its coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

theorem norm_add_natCast_pow_ge {z : ℂ} (hz : 0 < z.re) (N k : ℕ) :
    ‖z‖ ^ N * (‖z‖ + (k : ℝ)) ^ (2 : ℕ) / 2 ≤ ‖z + (k : ℂ)‖ ^ (N + 2) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hmono : ‖z‖ ≤ ‖z + (k : ℂ)‖ := norm_le_norm_add_natCast hz k
  have hsq : ‖z‖ ^ (2 : ℕ) + (k : ℝ) ^ (2 : ℕ) ≤ ‖z + (k : ℂ)‖ ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im]
    nlinarith [hz, hk]
  have hpowN : ‖z‖ ^ N ≤ ‖z + (k : ℂ)‖ ^ N := pow_le_pow_left₀ hz0 hmono N
  have hsplit : ‖z + (k : ℂ)‖ ^ (N + 2) = ‖z + (k : ℂ)‖ ^ N * ‖z + (k : ℂ)‖ ^ (2 : ℕ) := by
    rw [pow_add]
  rw [hsplit]
  have hstep1 : ‖z‖ ^ N * (‖z‖ ^ (2 : ℕ) + (k : ℝ) ^ (2 : ℕ))
      ≤ ‖z + (k : ℂ)‖ ^ N * ‖z + (k : ℂ)‖ ^ (2 : ℕ) := by
    have hnn : (0 : ℝ) ≤ ‖z‖ ^ (2 : ℕ) + (k : ℝ) ^ (2 : ℕ) := by positivity
    have hpn : (0 : ℝ) ≤ ‖z + (k : ℂ)‖ ^ N := by positivity
    nlinarith [hpowN, hsq, hnn, hpn]
  refine le_trans ?_ hstep1
  have hhalf : (‖z‖ + (k : ℝ)) ^ (2 : ℕ) / 2 ≤ ‖z‖ ^ (2 : ℕ) + (k : ℝ) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (‖z‖ - (k : ℝ))]
  have hpn : (0 : ℝ) ≤ ‖z‖ ^ N := by positivity
  nlinarith [hhalf, hpn]

set_option maxHeartbeats 1000000 in
/-- **The order-independent telescope.**  A one-step bound at order `N+2` and a vanishing anchor
give a bound at order `N+1`. -/
theorem norm_le_of_step_bound {L : ℂ → ℂ} {N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hstep : ∀ w : ℂ, 0 < w.re → 2 ≤ ‖w‖ → ‖L (w + 1) - L w‖ ≤ K / ‖w‖ ^ (N + 2))
    {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖)
    (hanchor : Tendsto (fun n : ℕ => L (z + (n : ℂ))) atTop (nhds 0)) :
    ‖L z‖ ≤ (3 * K) / ‖z‖ ^ (N + 1) := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hzre : ∀ k : ℕ, 0 < (z + (k : ℂ)).re := by
    intro k
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hnorm2 : ∀ k : ℕ, 2 ≤ ‖z + (k : ℂ)‖ := fun k =>
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
    refine le_trans (hstep (z + (k : ℂ)) (hzre k) (hnorm2 k)) ?_
    have hpow := norm_add_natCast_pow_ge hz N k
    have hden : (0 : ℝ) < ‖z‖ ^ N * (‖z‖ + (k : ℝ)) ^ (2 : ℕ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      positivity
    have hcpos : (0 : ℝ) < ‖z + (k : ℂ)‖ ^ (N + 2) := by
      have := hnorm2 k
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
