import GaloisForLFunctions.HTGeometry.ShortBumpMellinSmoothedSums

/-!
# A one-sided holomorphic ceiling removes the quadratic boundary defect

An upper ceiling uniform along vertical lines controls the lower boundary as well.
The proof chooses an arbitrarily small fixed interior anchor before approaching the
boundary. Harnack's inequality then removes the quadratic defect without a Laurent
expansion, a lower bound, or a prescribed rate of absolute growth.
-/

open Complex Metric Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

private theorem quadratic_boundary_lower {F : ℂ → ℂ} {M r : ℝ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.re ∧ z.re < r})
    (hM : 0 ≤ M) (hr : 0 < r)
    (hu : ∀ z : ℂ, 0 < z.re → z.re < r → z.re * (F z).re ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, -ε < s ^ 2 * (F s).re := by
  let d := min (r / 4) (ε / (32 * (M + 1)))
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdr : 2 * d < r := by
    have := min_le_left (r / 4) (ε / (32 * (M + 1)))
    change d ≤ r / 4 at this
    linarith
  have hde : 8 * M * d < ε / 2 := by
    have he := (le_div_iff₀ (show 0 < 32 * (M + 1) by positivity)).mp
      (min_le_right (r / 4) (ε / (32 * (M + 1))))
    change d * (32 * (M + 1)) ≤ ε at he
    nlinarith [mul_nonneg hM hd.le]
  let A := |(F (d : ℂ)).re|
  have hA : 0 ≤ A := abs_nonneg _
  have hs0 : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have herr : Tendsto (fun s : ℝ => s ^ 2 * A + 4 * d * s * A)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((hs0.pow 2).mul_const A).add ((hs0.const_mul (4 * d)).mul_const A)
  filter_upwards [self_mem_nhdsWithin, hs0.eventually_lt_const hd,
    herr.eventually_lt_const (half_pos hε)] with s hs hsd he
  have hs : 0 < s := hs
  let G : ℂ → ℂ := fun z => (2 * M / s : ℝ) - F z
  have hball : ∀ z ∈ ball (d : ℂ) (d - s / 2), s / 2 < z.re ∧ z.re < 2 * d := by
    intro z hz
    have hn := mem_ball_iff_norm.mp hz
    have ha := Complex.abs_re_le_norm (z - (d : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at ha
    constructor <;> linarith [neg_abs_le (z.re - d), le_abs_self (z.re - d)]
  have hGd : DifferentiableOn ℂ G (ball (d : ℂ) (d - s / 2)) :=
    (differentiableOn_const _).sub (hF.mono fun z hz => by
      obtain ⟨hz1, hz2⟩ := hball z hz
      exact ⟨by linarith, hz2.trans hdr⟩)
  have hG : ∀ z ∈ ball (d : ℂ) (d - s / 2), 0 ≤ (G z).re := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hball z hz
    have hz0 : 0 < z.re := by linarith
    have hub := hu z hz0 (hz2.trans hdr)
    have hle : (F z).re ≤ 2 * M / s := by
      apply (le_div_iff₀ hs).mpr
      by_cases hpos : 0 ≤ (F z).re
      · have := mul_le_mul_of_nonneg_right hz1.le hpos
        nlinarith
      · nlinarith
    simpa only [G, Complex.sub_re, Complex.ofReal_re, sub_nonneg] using hle
  have hdist : ‖(s : ℂ) - (d : ℂ)‖ = d - s := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    ring
  have hmem : (s : ℂ) ∈ ball (d : ℂ) (d - s / 2) := by
    rw [mem_ball_iff_norm, hdist]
    linarith
  have hh := norm_sub_le_of_re_nonneg_on_ball hGd hG hmem
  have hG0 := hG (d : ℂ) (mem_ball_self (by linarith : 0 < d - s / 2))
  have hfac : 2 * (d - s) / (d - s / 2 - (d - s)) ≤ 4 * d / s := by
    rw [show d - s / 2 - (d - s) = s / 2 by ring]
    field_simp
    linarith
  have hGc : (G (d : ℂ)).re ≤ 2 * M / s + A := by
    simp only [G, Complex.sub_re, Complex.ofReal_re]
    dsimp [A]
    linarith [neg_abs_le (F (d : ℂ)).re]
  have hdiff : ‖F (s : ℂ) - F (d : ℂ)‖ ≤ 4 * d / s * (2 * M / s + A) := by
    have hgsub : G (s : ℂ) - G (d : ℂ) = -(F (s : ℂ) - F (d : ℂ)) := by
      dsimp [G]
      ring
    rw [hgsub, norm_neg, hdist] at hh
    exact hh.trans (mul_le_mul hfac hGc hG0 (by positivity))
  have hneg : -(F (s : ℂ)).re ≤ A + 4 * d / s * (2 * M / s + A) := by
    have hn := Complex.re_le_norm (F (d : ℂ) - F (s : ℂ))
    rw [Complex.sub_re, norm_sub_rev] at hn
    have ha : -(F (d : ℂ)).re ≤ A := neg_le_abs _
    linarith
  have hk := mul_le_mul_of_nonneg_left hneg (sq_nonneg s)
  have hid : s ^ 2 * (A + 4 * d / s * (2 * M / s + A)) =
      8 * M * d + (s ^ 2 * A + 4 * d * s * A) := by
    field_simp
    ring
  rw [hid] at hk
  nlinarith only [hk, hde, he]

/-- A vertical-line-uniform first-order upper ceiling rules out both signs of a
quadratic boundary defect. No lower growth or meromorphic continuation is assumed. -/
theorem tendsto_sq_mul_re_zero_of_uniform_ceiling {F : ℂ → ℂ} {M r : ℝ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.re ∧ z.re < r})
    (hM : 0 ≤ M) (hr : 0 < r)
    (hu : ∀ z : ℂ, 0 < z.re → z.re < r → z.re * (F z).re ≤ M) :
    Tendsto (fun s : ℝ => s ^ 2 * (F s).re) (𝓝[>] 0) (𝓝 0) := by
  have hs0 : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  apply tendsto_order.mpr
  constructor
  · intro a ha
    simpa using quadratic_boundary_lower hF hM hr hu (show 0 < -a by linarith)
  · intro b hb
    have ht : Tendsto (fun s : ℝ => s * M) (𝓝[>] 0) (𝓝 0) := by
      simpa using hs0.mul_const M
    filter_upwards [self_mem_nhdsWithin, hs0.eventually_lt_const hr,
      ht.eventually_lt_const hb] with s hs hsr hsm
    have hs : 0 < s := hs
    have h := mul_le_mul_of_nonneg_left (hu (s : ℂ) hs hsr) hs.le
    simp only [Complex.ofReal_re] at h
    nlinarith only [h, hsm]

end GaloisForLFunctions.HTGeometry
