import GaloisForLFunctions.RHTower.Sieve.CutoffMass

/-!
# The cutoff's mass in norm

The main term is `W(1)`, the total mass of the cutoff, and the horizontal edges carry it divided by
the truncation height.  Both need it in norm:

    ‖W(1)‖ ≤ N + H.

The transform at `1` is the integral of a nonnegative real function, so its norm is the integral
itself, and the mass bound applies.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

/-- **The cutoff's mass, in norm.** -/
theorem norm_mellin_smoothWeight_one_le {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1‖ ≤ N + H := by
  have hreal : mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
      = ((∫ x in Ioi (0 : ℝ), smoothWeight N H x : ℝ) : ℂ) := by
    rw [mellin_smoothWeight_one]
    exact integral_ofReal (𝕜 := ℂ)
  rw [hreal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_trans hN (le_integral_smoothWeight hN hH))]
  exact integral_smoothWeight_le hN hH

end RHTower.Sieve
