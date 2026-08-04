import GaloisForLFunctions.RHTower.Sieve.HorizontalPoleBound

/-!
# The residue of the pole term

Combining the four edges: the vertical ones contribute `2π` and the horizontal ones vanish, so the
boundary functional of `(s-1)⁻¹` — the same functional that is zero for a holomorphic integrand —
tends to `2πi`.

This is the residue theorem for the one function the Chebyshev route needs it for, and it is proved
by direct computation rather than from a general residue calculus, which mathlib does not have for
rectangles.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The arctangent limit, extracted from the vertical pole integral. -/
theorem tendsto_two_arctan {α : ℝ} (hα : 0 < α) :
    Tendsto (fun T : ℝ => 2 * Real.arctan (T / α)) atTop (𝓝 Real.pi) := by
  refine (tendsto_integral_re_pole_line hα).congr fun T => ?_
  exact integral_re_pole_line (ne_of_gt hα)

/-- **The vertical edges tend to the residue.** -/
theorem tendsto_vertical_pole_pair {c d : ℝ} (hc : c < 1) (hd : 1 < d) :
    Tendsto (fun T : ℝ =>
        (∫ y : ℝ in (-T)..T, ((d : ℂ) + (y : ℝ) * Complex.I - 1)⁻¹)
          - (∫ y : ℝ in (-T)..T, ((c : ℂ) + (y : ℝ) * Complex.I - 1)⁻¹))
      atTop (𝓝 ((2 * Real.pi : ℝ) : ℂ)) := by
  have hreal : Tendsto (fun T : ℝ =>
      2 * Real.arctan (T / (d - 1)) + 2 * Real.arctan (T / (1 - c)))
      atTop (𝓝 (Real.pi + Real.pi)) :=
    (tendsto_two_arctan (by linarith)).add (tendsto_two_arctan (by linarith))
  rw [show Real.pi + Real.pi = 2 * Real.pi by ring] at hreal
  have hcast := (Complex.continuous_ofReal.tendsto (2 * Real.pi)).comp hreal
  refine hcast.congr fun T => ?_
  exact (integral_vertical_pole_pair hc hd).symm

/-- The horizontal edge at height `-T` is small. -/
theorem norm_integral_horizontal_pole_neg_le {c d T : ℝ} (hcd : c ≤ d) (hT : 0 < T) :
    ‖∫ x : ℝ in c..d, ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I - 1)⁻¹‖ ≤ (d - c) / T := by
  have h := norm_integral_horizontal_pole_le (c := c) (d := d) (T := -T) hcd (by linarith)
  rwa [abs_neg, abs_of_pos hT] at h

/-- **Both horizontal edges vanish.** -/
theorem tendsto_horizontal_pole_pair {c d : ℝ} (hcd : c ≤ d) :
    Tendsto (fun T : ℝ =>
        (∫ x : ℝ in c..d, ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I - 1)⁻¹)
          - (∫ x : ℝ in c..d, ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I - 1)⁻¹))
      atTop (𝓝 0) := by
  have hmaj : Tendsto (fun T : ℝ => (d - c) / T + (d - c) / T) atTop (𝓝 (0 + 0)) := by
    have h : Tendsto (fun T : ℝ => (d - c) / T) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := d - c) (f := atTop (α := ℝ))).div_atTop
        (tendsto_id (α := ℝ))
    exact h.add h
  rw [add_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  refine le_trans (norm_sub_le _ _) ?_
  have h1 := norm_integral_horizontal_pole_le (c := c) (d := d) (T := T) hcd (ne_of_gt hT)
  have h2 := norm_integral_horizontal_pole_neg_le hcd hT
  rw [abs_of_pos hT] at h1
  linarith

/-- **The residue of the pole term.**  The boundary functional tends to `2πi`. -/
theorem tendsto_pole_boundary {c d : ℝ} (hc : c < 1) (hd : 1 < d) :
    Tendsto (fun T : ℝ =>
        Complex.I • (∫ y : ℝ in (-T)..T, ((d : ℂ) + (y : ℝ) * Complex.I - 1)⁻¹)
          - Complex.I • (∫ y : ℝ in (-T)..T, ((c : ℂ) + (y : ℝ) * Complex.I - 1)⁻¹)
          - ((∫ x : ℝ in c..d, ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I - 1)⁻¹)
              - (∫ x : ℝ in c..d, ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I - 1)⁻¹)))
      atTop (𝓝 (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) := by
  have hvert := (tendsto_vertical_pole_pair hc hd).const_smul Complex.I
  have hhor := tendsto_horizontal_pole_pair (le_of_lt (lt_trans hc hd))
  have hsub := hvert.sub hhor
  rw [sub_zero] at hsub
  have hval : Complex.I • ((2 * Real.pi : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    rw [smul_eq_mul]
    ring
  rw [hval] at hsub
  refine hsub.congr fun T => ?_
  rw [smul_sub]

end RHTower.Sieve
