import GaloisForLFunctions.HTGeometry.PowerTailMomentDivergence

/-!
# A large complex average has a large coordinate

If a complex number has modulus at least `c`, one of its two real coordinates has modulus at least
`c/√2`, since otherwise the squared modulus would be below `c²`.  A concentration bound for each
real coordinate therefore controls the modulus after a union bound over the two coordinates.

This is the reduction that turns a chord condition on a torsion average into two real-coordinate
deviation events.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- **The coordinate split.**  A modulus bound forces one coordinate bound. -/
theorem abs_re_or_abs_im_ge {z : ℂ} {c : ℝ} (h : c ≤ ‖z‖) :
    c / Real.sqrt 2 ≤ |z.re| ∨ c / Real.sqrt 2 ≤ |z.im| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := by
    rw [Real.sqrt_pos]
    norm_num
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcpos : 0 < c := by
    by_contra hc
    push Not at hc
    have : c / Real.sqrt 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc (le_of_lt hsqrt)
    exact absurd (le_trans this (abs_nonneg z.re)) (not_le.mpr hre)
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hre2 : z.re ^ 2 < c ^ 2 / 2 := by
    have habs : |z.re| ^ 2 < (c / Real.sqrt 2) ^ 2 := by
      have h0 : (0 : ℝ) ≤ |z.re| := abs_nonneg _
      nlinarith [hre, h0]
    rw [sq_abs] at habs
    calc z.re ^ 2 < (c / Real.sqrt 2) ^ 2 := habs
      _ = c ^ 2 / 2 := by
          rw [div_pow, hsq2]
  have him2 : z.im ^ 2 < c ^ 2 / 2 := by
    have habs : |z.im| ^ 2 < (c / Real.sqrt 2) ^ 2 := by
      have h0 : (0 : ℝ) ≤ |z.im| := abs_nonneg _
      nlinarith [him, h0]
    rw [sq_abs] at habs
    calc z.im ^ 2 < (c / Real.sqrt 2) ^ 2 := habs
      _ = c ^ 2 / 2 := by
          rw [div_pow, hsq2]
  have hlt : ‖z‖ ^ 2 < c ^ 2 := by
    rw [hnorm]
    linarith
  nlinarith [h, hlt, norm_nonneg z, hcpos]

/-- **The union bound for the split.**  If each coordinate event has small measure, so does the
modulus event. -/
theorem measure_modulus_le_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ)
    (c : ℝ) :
    μ {ω | c ≤ ‖Z ω‖}
      ≤ μ {ω | c / Real.sqrt 2 ≤ |(Z ω).re|} + μ {ω | c / Real.sqrt 2 ≤ |(Z ω).im|} := by
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  rcases abs_re_or_abs_im_ge hω with h | h
  · exact Or.inl h
  · exact Or.inr h

end GaloisForLFunctions.HTGeometry
