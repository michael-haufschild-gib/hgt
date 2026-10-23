import GaloisForLFunctions.HTGeometry.GammaDigammaShiftAnchor

/-!
# `ψ(z) = log z − 1/(2z) + O(|z|⁻²)` on the right half-plane

The Stirling defect `g(z) = ψ(z) − log z + 1/(2z)` telescopes:
`g(z) = g(z+N) − ∑_{k<N} (g(z+k+1) − g(z+k))`.  The one-step gain is cubic
(`norm_digammaStirlingDefect_step_le`), the shifted defects vanish
(`norm_digamma_shift_sub_le` plus the integer anchor), and

```text
‖z+k‖³ ≥ ‖z‖ (‖z‖ + k)² / 2,      ∑_{k≥1} (‖z‖ + k)⁻² ≤ ‖z‖⁻¹,
```

so the telescoped tail is `O(‖z‖⁻²)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-! ## A real telescoping bound -/

theorem sum_inv_sq_shift_le {a : ℝ} (ha : 0 < a) (M : ℕ) :
    ∑ k ∈ Finset.range M, (1 : ℝ) / (a + k + 1) ^ (2 : ℕ) ≤ 1 / a := by
  have hkey : ∀ m : ℕ, ∑ k ∈ Finset.range m, ((1 : ℝ) / (a + k) - 1 / (a + k + 1))
      = 1 / a - 1 / (a + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have hcast : (a + ((m + 1 : ℕ) : ℝ)) = a + m + 1 := by push_cast; ring
        rw [hcast]
        ring
  have hterm : ∀ k ∈ Finset.range M,
      (1 : ℝ) / (a + k + 1) ^ (2 : ℕ) ≤ (1 : ℝ) / (a + k) - 1 / (a + k + 1) := by
    intro k _
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : (0 : ℝ) < a + k := by linarith
    have h2 : (0 : ℝ) < a + k + 1 := by linarith
    have hid : (1 : ℝ) / (a + k) - 1 / (a + k + 1) = 1 / ((a + k) * (a + k + 1)) := by
      field_simp
      ring
    rw [hid, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h1, h2]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [hkey]
  have hpos : (0 : ℝ) < a + (M : ℝ) := by
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have : (0 : ℝ) < 1 / (a + (M : ℝ)) := by positivity
  linarith

/-! ## The shifted norms -/

theorem norm_le_norm_add_natCast {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    ‖z‖ ≤ ‖z + (k : ℂ)‖ := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hsq : ‖z‖ ^ (2 : ℕ) ≤ ‖z + (k : ℂ)‖ ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im]
    nlinarith [hz, hk]
  nlinarith [norm_nonneg z, norm_nonneg (z + (k : ℂ)), hsq]

theorem norm_add_natCast_cube_ge {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    ‖z‖ * (‖z‖ + (k : ℝ)) ^ (2 : ℕ) / 2 ≤ ‖z + (k : ℂ)‖ ^ (3 : ℕ) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have h1 : ‖z‖ ≤ ‖z + (k : ℂ)‖ := norm_le_norm_add_natCast hz k
  have hsq : ‖z‖ ^ (2 : ℕ) + (k : ℝ) ^ (2 : ℕ) ≤ ‖z + (k : ℂ)‖ ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im]
    nlinarith [hz, hk]
  have hcube : ‖z + (k : ℂ)‖ ^ (3 : ℕ) = ‖z + (k : ℂ)‖ * ‖z + (k : ℂ)‖ ^ (2 : ℕ) := by ring
  rw [hcube]
  have hstep : ‖z‖ * (‖z‖ ^ (2 : ℕ) + (k : ℝ) ^ (2 : ℕ)) ≤ ‖z + (k : ℂ)‖ * ‖z + (k : ℂ)‖ ^ (2 : ℕ) := by
    have hnn : (0 : ℝ) ≤ ‖z‖ ^ (2 : ℕ) + (k : ℝ) ^ (2 : ℕ) := by positivity
    nlinarith [h1, hsq, hz0, hnn]
  nlinarith [hstep, hz0, sq_nonneg (‖z‖ - (k : ℝ))]

/-! ## The logarithm is additive across the right half-plane -/

theorem log_sub_log_of_re_pos {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) :
    Complex.log w - Complex.log v = Complex.log (w / v) := by
  have hpi := Real.pi_pos
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hv
    simp at hv
  have hargw : |Complex.arg w| < Real.pi / 2 := by
    rw [abs_lt]
    exact ⟨Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hw),
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hw)⟩
  have hargv : |Complex.arg v| < Real.pi / 2 := by
    rw [abs_lt]
    exact ⟨Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hv),
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hv)⟩
  obtain ⟨hwl, hwu⟩ := abs_lt.mp hargw
  obtain ⟨hvl, hvu⟩ := abs_lt.mp hargv
  have hargv' : Complex.arg v ≠ Real.pi := by
    intro h
    rw [h] at hvu
    linarith
  have hinvarg : Complex.arg v⁻¹ = -Complex.arg v := by
    have h := congrArg Complex.im (Complex.log_inv v hargv')
    simpa [Complex.log_im] using h
  have hmul : Complex.log (w * v⁻¹) = Complex.log w + Complex.log v⁻¹ := by
    refine Complex.log_mul hw0 (inv_ne_zero hv0) ?_
    rw [hinvarg]
    exact ⟨by linarith, by linarith⟩
  rw [div_eq_mul_inv, hmul, Complex.log_inv v hargv']
  ring

/-! ## The shifted Stirling defect vanishes -/

theorem tendsto_digammaStirlingDefect_shift_zero {z : ℂ} (hz : 0 ≤ z.re) :
    Tendsto (fun N : ℕ => digammaStirlingDefect (z + (N : ℂ))) atTop (nhds 0) := by
  have hzre : ∀ N : ℕ, 1 ≤ N → 0 < (z + (N : ℂ)).re := by
    intro N hN
    rw [Complex.add_re, Complex.natCast_re]
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hone : ∀ N : ℕ, 0 < ((N : ℂ) + 1).re := by
    intro N
    rw [Complex.add_re, Complex.one_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  -- the four pieces
  have hnormlow : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ ‖z + (N : ℂ)‖ := by
    intro N hN
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.add_re, Complex.natCast_re, le_abs]
    left
    linarith
  have hA : Tendsto (fun N : ℕ =>
      Complex.digamma (z + (N : ℂ)) - Complex.digamma (1 + (N : ℂ))) atTop (nhds 0) := by
    have hbound : ∀ᶠ N : ℕ in atTop,
        ‖Complex.digamma (z + (N : ℂ)) - Complex.digamma (1 + (N : ℂ))‖ ≤ ‖z - 1‖ / (N : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact norm_digamma_shift_sub_le hz hN
    exact squeeze_zero_norm' hbound (tendsto_const_div_atTop_nhds_zero_nat ‖z - 1‖)
  have hB : Tendsto (fun N : ℕ =>
      Complex.digamma ((N : ℂ) + 1) - Complex.log ((N : ℂ) + 1)) atTop (nhds 0) :=
    RHTower.digamma_natCast_add_one_sub_log_tendsto
  have hquot : Tendsto (fun N : ℕ => (z + (N : ℂ)) / ((N : ℂ) + 1)) atTop (nhds 1) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat ‖z - 1‖)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hne : ((N : ℂ) + 1) ≠ 0 := by
      intro h
      have hre : ((N : ℂ) + 1).re = 0 := by rw [h]; simp
      have := hone N
      linarith [hre]
    have hid : (z + (N : ℂ)) / ((N : ℂ) + 1) - 1 = (z - 1) / ((N : ℂ) + 1) := by
      field_simp
      ring
    have hlow : (N : ℝ) ≤ ‖(N : ℂ) + 1‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      rw [Complex.add_re, Complex.one_re, Complex.natCast_re, le_abs]
      left
      linarith
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [norm_norm, hid, norm_div]
    rw [div_le_div_iff₀ (by linarith) hNpos]
    exact mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
  have hC : Tendsto (fun N : ℕ =>
      Complex.log (z + (N : ℂ)) - Complex.log ((N : ℂ) + 1)) atTop (nhds 0) := by
    have hcont : ContinuousAt Complex.log 1 := by
      refine continuousAt_clog ?_
      simp [Complex.mem_slitPlane_iff]
    have hlim := hcont.tendsto.comp hquot
    rw [Complex.log_one] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (log_sub_log_of_re_pos (hzre N hN) (hone N)).symm
  have hD : Tendsto (fun N : ℕ => (1 : ℂ) / (2 * (z + (N : ℂ)))) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hlow := hnormlow N hN
    rw [norm_div, norm_one, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    rw [div_le_div_iff₀ (by linarith) hNpos]
    linarith [hlow]
  have hsum := ((hA.add hB).sub hC).add hD
  simp only [add_zero, sub_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [digammaStirlingDefect]
  have hcomm : (1 : ℂ) + (N : ℂ) = (N : ℂ) + 1 := by ring
  rw [hcomm]
  ring

/-! ## The Stirling bound -/

theorem sum_inv_sq_shift_head_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 : ℝ) / (a + k) ^ (2 : ℕ) ≤ 1 / a ^ (2 : ℕ) + 1 / a := by
  rcases N with _ | M
  · simp
    positivity
  · rw [Finset.sum_range_succ']
    have hcongr : ∑ k ∈ Finset.range M, (1 : ℝ) / (a + ((k + 1 : ℕ) : ℝ)) ^ (2 : ℕ)
        = ∑ k ∈ Finset.range M, (1 : ℝ) / (a + k + 1) ^ (2 : ℕ) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      push_cast
      ring
    rw [hcongr]
    have h := sum_inv_sq_shift_le ha M
    have hzero : (1 : ℝ) / (a + ((0 : ℕ) : ℝ)) ^ (2 : ℕ) = 1 / a ^ (2 : ℕ) := by
      norm_num
    rw [hzero]
    linarith

/-- **The Stirling bound for the digamma function.**  `ψ(z) = log z − 1/(2z) + O(|z|⁻²)` on the
right half-plane, with an explicit constant. -/
theorem norm_digammaStirlingDefect_le {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖digammaStirlingDefect z‖ ≤ 6 / ‖z‖ ^ (2 : ℕ) := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hzre : ∀ k : ℕ, 0 < (z + (k : ℂ)).re := by
    intro k
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hnorm2 : ∀ k : ℕ, 2 ≤ ‖z + (k : ℂ)‖ := fun k =>
    le_trans h2 (norm_le_norm_add_natCast hz k)
  -- the telescope
  have htel : ∀ N : ℕ, digammaStirlingDefect (z + (N : ℂ)) - digammaStirlingDefect z
      = ∑ k ∈ Finset.range N,
        (digammaStirlingDefect (z + ((k : ℕ) + 1 : ℕ)) - digammaStirlingDefect (z + (k : ℂ))) := by
    intro N
    have h := Finset.sum_range_sub (f := fun k : ℕ => digammaStirlingDefect (z + (k : ℂ))) N
    simpa using h.symm
  have hstepbound : ∀ k : ℕ,
      ‖digammaStirlingDefect (z + ((k : ℕ) + 1 : ℕ)) - digammaStirlingDefect (z + (k : ℂ))‖
        ≤ 4 / (‖z‖ * (‖z‖ + (k : ℝ)) ^ (2 : ℕ)) := by
    intro k
    have hcast : ((z : ℂ) + (((k : ℕ) + 1 : ℕ) : ℂ)) = (z + (k : ℂ)) + 1 := by
      push_cast
      ring
    rw [hcast]
    have hstep := norm_digammaStirlingDefect_step_le (hzre k) (hnorm2 k)
    refine le_trans hstep ?_
    have hcube := norm_add_natCast_cube_ge hz k
    have hden : (0 : ℝ) < ‖z‖ * (‖z‖ + (k : ℝ)) ^ (2 : ℕ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      positivity
    have hcpos : (0 : ℝ) < ‖z + (k : ℂ)‖ ^ (3 : ℕ) := by
      have := hnorm2 k
      positivity
    rw [div_le_div_iff₀ hcpos hden]
    linarith [hcube]
  have hpartial : ∀ N : ℕ,
      ‖digammaStirlingDefect (z + (N : ℂ)) - digammaStirlingDefect z‖ ≤ 6 / ‖z‖ ^ (2 : ℕ) := by
    intro N
    rw [htel N]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun k _ => hstepbound k) ?_
    have hrw : ∀ k : ℕ, (4 : ℝ) / (‖z‖ * (‖z‖ + (k : ℝ)) ^ (2 : ℕ))
        = (4 / ‖z‖) * ((1 : ℝ) / (‖z‖ + (k : ℝ)) ^ (2 : ℕ)) := by
      intro k
      field_simp
    rw [Finset.sum_congr rfl (fun k _ => hrw k), ← Finset.mul_sum]
    have hsum := sum_inv_sq_shift_head_le hzpos N
    have h4 : (0 : ℝ) ≤ 4 / ‖z‖ := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hsum h4) ?_
    have hid : (4 : ℝ) / ‖z‖ * (1 / ‖z‖ ^ (2 : ℕ) + 1 / ‖z‖) = 4 / ‖z‖ ^ (3 : ℕ) + 4 / ‖z‖ ^ (2 : ℕ) := by
      field_simp
    rw [hid]
    have hstep1 : (4 : ℝ) / ‖z‖ ^ (3 : ℕ) ≤ 2 / ‖z‖ ^ (2 : ℕ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖z‖)]
    have hstep2 : (2 : ℝ) / ‖z‖ ^ (2 : ℕ) + 4 / ‖z‖ ^ (2 : ℕ) = 6 / ‖z‖ ^ (2 : ℕ) := by ring
    linarith
  -- pass to the limit
  have hlim : Tendsto (fun N : ℕ =>
      ‖digammaStirlingDefect (z + (N : ℂ)) - digammaStirlingDefect z‖) atTop
      (nhds ‖digammaStirlingDefect z‖) := by
    have hshift := tendsto_digammaStirlingDefect_shift_zero hz.le
    have := (hshift.sub_const (digammaStirlingDefect z)).norm
    simpa using this
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hpartial)

end

end GaloisForLFunctions.HTGeometry
