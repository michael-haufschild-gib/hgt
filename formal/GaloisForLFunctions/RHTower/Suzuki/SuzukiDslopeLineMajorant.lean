import GaloisForLFunctions.RHTower.Suzuki.SuzukiDslopeBounded

noncomputable section

/-!
# A uniform line majorant for `F_γ`

The two bounds `‖dslope (A/E) γ z‖ ≤ C` and `≤ 1/‖z - γ‖` combine into a single Cauchy profile in
the real part,

```text
‖dslope (A/E) γ z‖² ≤ 2C² / (1 + (Re z - Re γ)²),
```

valid on the whole closed upper half-plane once `C ≥ 1`.  Near `γ` the uniform bound is the
binding one; far away the reciprocal-distance bound is, and `C ≥ 1` is exactly what makes the two
regimes meet.

The point of the profile is that it does not depend on the height of the line, so integrating it
bounds the mass of `F_γ` on every horizontal line by `2C²π` at once.  The naive bound
`1/‖z - γ‖` alone would give `π/y`, which blows up at the boundary and is useless.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

theorem exists_one_le_bound_dslope (hRH : RiemannHypothesis) {γ : ℂ} (hγ : XiC γ = 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.im → ‖dslope suzukiHalfInner γ z‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_dslope_suzukiHalfInner hRH hγ
  exact ⟨max C 1, le_max_right _ _, fun z hz => le_trans (hC z hz) (le_max_left _ _)⟩

/-- **The uniform line majorant.**  `‖F_γ‖²` is dominated by a fixed Cauchy profile in the real
part, uniformly over all horizontal lines in the closed upper half-plane. -/
theorem norm_sq_dslope_le_lineMajorant (hRH : RiemannHypothesis) {γ : ℂ} (hγ : XiC γ = 0)
    {C : ℝ} (hC1 : 1 ≤ C)
    (hCb : ∀ z : ℂ, 0 ≤ z.im → ‖dslope suzukiHalfInner γ z‖ ≤ C)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖dslope suzukiHalfInner γ z‖ ^ (2 : ℕ) ≤ 2 * C ^ (2 : ℕ) / (1 + (z.re - γ.re) ^ (2 : ℕ)) := by
  have hnn : 0 ≤ ‖dslope suzukiHalfInner γ z‖ := norm_nonneg _
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hden : (0 : ℝ) < 1 + (z.re - γ.re) ^ (2 : ℕ) := by positivity
  rcases le_or_gt |z.re - γ.re| 1 with h | h
  · have hb := hCb z hz
    have hsq : ‖dslope suzukiHalfInner γ z‖ ^ (2 : ℕ) ≤ C ^ (2 : ℕ) := by nlinarith [hnn, hb]
    have hd2 : (z.re - γ.re) ^ (2 : ℕ) ≤ 1 := by
      nlinarith [sq_abs (z.re - γ.re), h, abs_nonneg (z.re - γ.re)]
    rw [le_div_iff₀ hden]
    nlinarith [hsq, hd2, sq_nonneg ‖dslope suzukiHalfInner γ z‖, sq_nonneg C]
  · have hne : z ≠ γ := by
      intro hzz
      rw [hzz] at h
      simp at h
      linarith
    have hre : |z.re - γ.re| ≤ ‖z - γ‖ := by
      have := Complex.abs_re_le_norm (z - γ)
      simpa [Complex.sub_re] using this
    have hpos : (0 : ℝ) < ‖z - γ‖ := lt_of_lt_of_le (by linarith) hre
    have hb := norm_dslope_suzukiHalfInner_le_inv hRH hγ hz hne
    have hsq : ‖dslope suzukiHalfInner γ z‖ ^ (2 : ℕ) ≤ 1 / ‖z - γ‖ ^ (2 : ℕ) := by
      have h1 : ‖dslope suzukiHalfInner γ z‖ ^ (2 : ℕ) ≤ (1 / ‖z - γ‖) ^ (2 : ℕ) := by
        nlinarith [hnn, hb, hpos]
      rwa [div_pow, one_pow] at h1
    have hgz : (1 : ℝ) ≤ (z.re - γ.re) ^ (2 : ℕ) := by
      nlinarith [sq_abs (z.re - γ.re), h]
    have hzsq : (z.re - γ.re) ^ (2 : ℕ) ≤ ‖z - γ‖ ^ (2 : ℕ) := by
      nlinarith [sq_abs (z.re - γ.re), hre, abs_nonneg (z.re - γ.re)]
    have hstep : 1 / ‖z - γ‖ ^ (2 : ℕ) ≤ 2 * C ^ (2 : ℕ) / (1 + (z.re - γ.re) ^ (2 : ℕ)) := by
      rw [div_le_div_iff₀ (by positivity) hden]
      nlinarith [hgz, hzsq, hC1, sq_nonneg (C - 1)]
    linarith

end RHTower
