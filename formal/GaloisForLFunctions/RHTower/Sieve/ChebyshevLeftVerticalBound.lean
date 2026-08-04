import GaloisForLFunctions.RHTower.Sieve.ChebyshevFullBound

/-!
# The pole-free left edge

After the pole term is extracted, the left edge of the divided difference is
`∫ W(c+iy)/(c-1+iy) dy`.  Its integrand is the cutoff's transform against a factor bounded by
`1/(1-c)`, since the real part of `c-1+iy` is `c-1` and the norm dominates it.  The vertical mass of
the transform is already controlled, so the edge is bounded with no further analysis of `ζ`.

The bound is uniform in the truncation height: the mass estimate is, the pole factor is, and nothing
else appears.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- The pole factor is bounded on a line left of the abscissa `1`. -/
theorem norm_inv_sub_one_line_le {c y : ℝ} (hc : c < 1) :
    ‖((c : ℂ) + (y : ℝ) * Complex.I - 1)⁻¹‖ ≤ (1 - c)⁻¹ := by
  have hre : ((c : ℂ) + (y : ℝ) * Complex.I - 1).re = c - 1 := by simp
  have hge : (1 - c : ℝ) ≤ ‖(c : ℂ) + (y : ℝ) * Complex.I - 1‖ := by
    have h := Complex.abs_re_le_norm ((c : ℂ) + (y : ℝ) * Complex.I - 1)
    rw [hre, abs_of_nonpos (by linarith)] at h
    linarith
  have hpos : (0 : ℝ) < 1 - c := by linarith
  rw [norm_inv]
  exact inv_anti₀ hpos hge

/-- **The pole-free left edge.** -/
theorem norm_integral_left_vertical_pole_free_le {N H c T C : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hc0 : 0 < c) (hc : c < 1) (hT : 1 ≤ T)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖∫ y : ℝ in (-T)..T, mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((c : ℂ) + (y : ℝ) * Complex.I)
        * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹‖
      ≤ (1 - c)⁻¹ * (2 * ((N + H) ^ c / c) + 2 * C) := by
  have hcongr : (∫ y : ℝ in (-T)..T, mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * Complex.I)
      * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
      = ∫ y : ℝ in (-T)..T, (fun s : ℂ => (s - 1)⁻¹) ((c : ℂ) + (y : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I) :=
    intervalIntegral.integral_congr (fun y _ => by dsimp only; ring)
  rw [hcongr]
  refine norm_integral_vertical_edge_le hN hH hc0 hT
    (by positivity) hbd (F := fun s : ℂ => (s - 1)⁻¹) ?_ ?_
  · have hlin : Continuous fun y : ℝ => ((c : ℂ) + (y : ℝ) * Complex.I) - 1 := by fun_prop
    exact (hlin.inv₀ fun y => sub_one_ne_zero_line_of_ne hc.ne).continuousOn
  · exact fun y _ => norm_inv_sub_one_line_le hc

end RHTower.Sieve
