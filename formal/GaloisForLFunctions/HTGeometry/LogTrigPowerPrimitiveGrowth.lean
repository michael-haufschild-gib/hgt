import GaloisForLFunctions.HTGeometry.LogTrigPowerPrimitives
import GaloisForLFunctions.HTGeometry.LogPhaseNoLimit

/-!
# The second primitives oscillate without limit

For `b ≠ 0` and `c > -1` the second primitives of `x^(c-1) cos (b log x)` and
`x^(c-1) sin (b log x)` carry the growing factor `x^(c+1)` in front of a nonzero logarithmic
harmonic.  They are therefore unbounded in both signs and converge to no real number at `+∞`.

This is the precise reason why an antiderivative of an oscillatory power kernel cannot be
evaluated "at infinity" even when the kernel itself has a convergent improper integral against a
bounded weight.
-/

open Real Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The amplitude pair of the second primitive never vanishes when `b ≠ 0`. -/
theorem secondPrimitive_amplitude_ne_zero {c b : ℝ} (hb : b ≠ 0) :
    c ^ 2 + c - b ^ 2 ≠ 0 ∨ (2 * c + 1) * b ≠ 0 := by
  rcases eq_or_ne (2 * c + 1) 0 with h | h
  · left
    have hc : c = -(1 / 2) := by linarith
    rw [hc]
    intro heq
    nlinarith [sq_nonneg b]
  · exact Or.inr (mul_ne_zero h hb)

theorem secondPrimitive_denom_pos {c b : ℝ} (hb : b ≠ 0) :
    0 < (c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2) := by
  have h1 : 0 < c ^ 2 + b ^ 2 := by positivity
  have h2 : 0 < (c + 1) ^ 2 + b ^ 2 := by positivity
  exact mul_pos h1 h2

theorem cosLogSecondPrimitive_eq_rpow_mul_harmonic (c b x : ℝ) :
    cosLogSecondPrimitive c b x
      = x ^ (c + 1) *
        (((c ^ 2 + c - b ^ 2) / ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2)))
            * Real.cos (b * Real.log x)
          + ((2 * c + 1) * b / ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2)))
            * Real.sin (b * Real.log x)) := by
  rw [cosLogSecondPrimitive]
  ring

theorem sinLogSecondPrimitive_eq_rpow_mul_harmonic (c b x : ℝ) :
    sinLogSecondPrimitive c b x
      = x ^ (c + 1) *
        ((-((2 * c + 1) * b) / ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2)))
            * Real.cos (b * Real.log x)
          + ((c ^ 2 + c - b ^ 2) / ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2)))
            * Real.sin (b * Real.log x)) := by
  rw [sinLogSecondPrimitive]
  ring

/-- **The cosine second primitive has no limit at `+∞`.** -/
theorem not_tendsto_cosLogSecondPrimitive_atTop {c b L : ℝ} (hb : b ≠ 0) (hc : -1 < c) :
    ¬ Tendsto (cosLogSecondPrimitive c b) atTop (𝓝 L) := by
  have hD := secondPrimitive_denom_pos (c := c) hb
  have hAB : (c ^ 2 + c - b ^ 2) / ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2)) ≠ 0 ∨
      (2 * c + 1) * b / ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2)) ≠ 0 := by
    rcases secondPrimitive_amplitude_ne_zero (c := c) hb with h | h
    · exact Or.inl (div_ne_zero h hD.ne')
    · exact Or.inr (div_ne_zero h hD.ne')
  have hd : 0 < c + 1 := by linarith
  have := not_tendsto_rpow_mul_logHarmonic_atTop (L := L) hb hAB hd
  intro hcon
  exact this (by
    refine hcon.congr fun x => ?_
    exact cosLogSecondPrimitive_eq_rpow_mul_harmonic c b x)

/-- **The sine second primitive has no limit at `+∞`.** -/
theorem not_tendsto_sinLogSecondPrimitive_atTop {c b L : ℝ} (hb : b ≠ 0) (hc : -1 < c) :
    ¬ Tendsto (sinLogSecondPrimitive c b) atTop (𝓝 L) := by
  have hD := secondPrimitive_denom_pos (c := c) hb
  have hAB : -((2 * c + 1) * b) / ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2)) ≠ 0 ∨
      (c ^ 2 + c - b ^ 2) / ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2)) ≠ 0 := by
    rcases secondPrimitive_amplitude_ne_zero (c := c) hb with h | h
    · exact Or.inr (div_ne_zero h hD.ne')
    · exact Or.inl (div_ne_zero (neg_ne_zero.mpr h) hD.ne')
  have hd : 0 < c + 1 := by linarith
  have := not_tendsto_rpow_mul_logHarmonic_atTop (L := L) hb hAB hd
  intro hcon
  exact this (by
    refine hcon.congr fun x => ?_
    exact sinLogSecondPrimitive_eq_rpow_mul_harmonic c b x)

/-! ## Decay of the boundary term, and failure of jump-free partial integration -/

theorem abs_cosLogPrimitive_le {c b x : ℝ} (hx : 0 < x) (h : c ^ 2 + b ^ 2 ≠ 0) :
    |cosLogPrimitive c b x| ≤ x ^ c * ((|c| + |b|) / (c ^ 2 + b ^ 2)) := by
  have hD : 0 < c ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx c
  have hnum : |c * Real.cos (b * Real.log x) + b * Real.sin (b * Real.log x)| ≤ |c| + |b| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [Real.abs_cos_le_one (b * Real.log x), Real.abs_sin_le_one (b * Real.log x),
      abs_nonneg c, abs_nonneg b]
  calc |cosLogPrimitive c b x|
      = x ^ c * |c * Real.cos (b * Real.log x) + b * Real.sin (b * Real.log x)|
          / (c ^ 2 + b ^ 2) := by
        rw [cosLogPrimitive, abs_div, abs_of_pos hD, abs_mul, abs_of_pos hxc]
    _ ≤ x ^ c * (|c| + |b|) / (c ^ 2 + b ^ 2) := by gcongr
    _ = x ^ c * ((|c| + |b|) / (c ^ 2 + b ^ 2)) := by ring

theorem abs_sinLogPrimitive_le {c b x : ℝ} (hx : 0 < x) (h : c ^ 2 + b ^ 2 ≠ 0) :
    |sinLogPrimitive c b x| ≤ x ^ c * ((|c| + |b|) / (c ^ 2 + b ^ 2)) := by
  have hD : 0 < c ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx c
  have hnum : |c * Real.sin (b * Real.log x) - b * Real.cos (b * Real.log x)| ≤ |c| + |b| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [Real.abs_cos_le_one (b * Real.log x), Real.abs_sin_le_one (b * Real.log x),
      abs_nonneg c, abs_nonneg b]
  calc |sinLogPrimitive c b x|
      = x ^ c * |c * Real.sin (b * Real.log x) - b * Real.cos (b * Real.log x)|
          / (c ^ 2 + b ^ 2) := by
        rw [sinLogPrimitive, abs_div, abs_of_pos hD, abs_mul, abs_of_pos hxc]
    _ ≤ x ^ c * (|c| + |b|) / (c ^ 2 + b ^ 2) := by gcongr
    _ = x ^ c * ((|c| + |b|) / (c ^ 2 + b ^ 2)) := by ring

theorem tendsto_rpow_mul_const_atTop_nhds_zero {c K : ℝ} (hc : c < 0) :
    Tendsto (fun x : ℝ => x ^ c * K) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => x ^ c) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := -c) (by linarith)
    simpa using this
  simpa using h.mul_const K

/-- **The boundary term of the partial integration decays.** -/
theorem tendsto_fract_mul_cosLogPrimitive_atTop {c b : ℝ} (hc : c < 0) (h : c ^ 2 + b ^ 2 ≠ 0) :
    Tendsto (fun x : ℝ => Int.fract x * cosLogPrimitive c b x) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_rpow_mul_const_atTop_nhds_zero
    (c := c) (K := (|c| + |b|) / (c ^ 2 + b ^ 2)) hc)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Int.fract_nonneg x)]
  have h1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
  have h2 : |cosLogPrimitive c b x| ≤ x ^ c * ((|c| + |b|) / (c ^ 2 + b ^ 2)) :=
    abs_cosLogPrimitive_le hx h
  have h3 : (0 : ℝ) ≤ x ^ c * ((|c| + |b|) / (c ^ 2 + b ^ 2)) :=
    le_trans (abs_nonneg _) h2
  nlinarith [abs_nonneg (cosLogPrimitive c b x), Int.fract_nonneg x]

/-- **The boundary term of the partial integration decays, sine version.** -/
theorem tendsto_fract_mul_sinLogPrimitive_atTop {c b : ℝ} (hc : c < 0) (h : c ^ 2 + b ^ 2 ≠ 0) :
    Tendsto (fun x : ℝ => Int.fract x * sinLogPrimitive c b x) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_rpow_mul_const_atTop_nhds_zero
    (c := c) (K := (|c| + |b|) / (c ^ 2 + b ^ 2)) hc)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Int.fract_nonneg x)]
  have h1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
  have h2 : |sinLogPrimitive c b x| ≤ x ^ c * ((|c| + |b|) / (c ^ 2 + b ^ 2)) :=
    abs_sinLogPrimitive_le hx h
  have h3 : (0 : ℝ) ≤ x ^ c * ((|c| + |b|) / (c ^ 2 + b ^ 2)) :=
    le_trans (abs_nonneg _) h2
  nlinarith [abs_nonneg (sinLogPrimitive c b x), Int.fract_nonneg x]

/-- **Jump-free partial integration against the fractional part has no limit.**  The expression
obtained by treating `{x}` as a differentiable function with derivative `1` on all of `[1, N]`,
namely `{N} P(N) - (W(N) - W(1))`, converges to no real number, while the integral it is meant to
evaluate does converge. -/
theorem not_tendsto_jumpFreeCos_atTop {c b L : ℝ} (hb : b ≠ 0) (hc0 : c < 0) (hc1 : -1 < c) :
    ¬ Tendsto (fun N : ℝ => Int.fract N * cosLogPrimitive c b N
        - (cosLogSecondPrimitive c b N - cosLogSecondPrimitive c b 1)) atTop (𝓝 L) := by
  intro hcon
  have hD : c ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hb0 := tendsto_fract_mul_cosLogPrimitive_atTop (c := c) (b := b) hc0 hD
  have hdiff : Tendsto (fun N : ℝ => cosLogSecondPrimitive c b N) atTop
      (𝓝 (0 - L + cosLogSecondPrimitive c b 1)) := by
    have h := (hb0.sub hcon).add_const (cosLogSecondPrimitive c b 1)
    refine h.congr fun N => ?_
    ring
  exact not_tendsto_cosLogSecondPrimitive_atTop hb hc1 hdiff

/-- Sine version of the failure of jump-free partial integration. -/
theorem not_tendsto_jumpFreeSin_atTop {c b L : ℝ} (hb : b ≠ 0) (hc0 : c < 0) (hc1 : -1 < c) :
    ¬ Tendsto (fun N : ℝ => Int.fract N * sinLogPrimitive c b N
        - (sinLogSecondPrimitive c b N - sinLogSecondPrimitive c b 1)) atTop (𝓝 L) := by
  intro hcon
  have hD : c ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hb0 := tendsto_fract_mul_sinLogPrimitive_atTop (c := c) (b := b) hc0 hD
  have hdiff : Tendsto (fun N : ℝ => sinLogSecondPrimitive c b N) atTop
      (𝓝 (0 - L + sinLogSecondPrimitive c b 1)) := by
    have h := (hb0.sub hcon).add_const (sinLogSecondPrimitive c b 1)
    refine h.congr fun N => ?_
    ring
  exact not_tendsto_sinLogSecondPrimitive_atTop hb hc1 hdiff

end GaloisForLFunctions.HTGeometry
