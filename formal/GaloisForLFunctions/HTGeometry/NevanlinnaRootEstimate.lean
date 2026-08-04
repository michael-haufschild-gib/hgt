import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic

/-!
# The characteristic of an algebraic root

If an entire function satisfies a polynomial relation whose coefficients are controlled on a circle,
its own growth on that circle is controlled: Cauchy's bound on the roots of a polynomial converts a
bound on the coefficient ratios into a bound on the root, and the characteristic of an entire
function is a circle average of `log⁺` of its modulus.

This is the shape of the algebraic-function root estimate that a composition-growth induction uses:
the first state to satisfy an algebraic relation over the previous ones cannot grow faster than they
do.
-/

open MeasureTheory Real Complex Metric

namespace GaloisForLFunctions.Nevanlinna

/-- **The characteristic of a root is bounded by the Cauchy bound of its equation.**  If `g z` is a
root of a nonzero polynomial `p z` for every `z` on the circle of radius `r`, and the Cauchy bounds
of those polynomials are at most `B`, then `T(r, g) <= log⁺ B`. -/
theorem characteristic_le_posLog_of_isRoot {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {r B : ℝ} {p : ℂ → Polynomial ℂ}
    (hne : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, p z ≠ 0)
    (hroot : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, (p z).IsRoot (g z))
    (hB : ∀ z ∈ Metric.sphere (0 : ℂ) |r|,
      ((Polynomial.cauchyBound (p z) : NNReal) : ℝ) ≤ B) :
    ValueDistribution.characteristic g ⊤ r ≤ Real.posLog B := by
  refine characteristic_top_le_posLog_of_bound hg ?_
  intro z hz
  have h := (hroot z hz).norm_lt_cauchyBound (hne z hz)
  have h' : ‖g z‖ < ((Polynomial.cauchyBound (p z) : NNReal) : ℝ) := by exact_mod_cast h
  exact le_trans h'.le (hB z hz)

/-! ## Bounding the Cauchy bound -/

/-- **A coefficient bound gives a Cauchy bound.**  If every coefficient of `p` has norm at most `C`
and its leading coefficient has norm at least `L > 0`, then the Cauchy bound of `p` is at most
`C / L + 1`. -/
theorem cauchyBound_le_of_coeff_bound {p : Polynomial ℂ} {C L : NNReal} (hL : 0 < L)
    (hlead : L ≤ ‖p.leadingCoeff‖₊) (hC : ∀ i, ‖p.coeff i‖₊ ≤ C) :
    Polynomial.cauchyBound p ≤ C / L + 1 := by
  simp only [Polynomial.cauchyBound]
  gcongr
  all_goals first
    | exact hL
    | exact Finset.sup_le fun i _ => hC i

/-- The same bound stated over the reals. -/
theorem cauchyBound_coe_le_of_coeff_bound {p : Polynomial ℂ} {C L : NNReal} (hL : 0 < L)
    (hlead : L ≤ ‖p.leadingCoeff‖₊) (hC : ∀ i, ‖p.coeff i‖₊ ≤ C) :
    ((Polynomial.cauchyBound p : NNReal) : ℝ) ≤ (C : ℝ) / (L : ℝ) + 1 := by
  have h := cauchyBound_le_of_coeff_bound hL hlead hC
  have hcoe : (((C / L + 1 : NNReal)) : ℝ) = (C : ℝ) / (L : ℝ) + 1 := by
    push_cast
    ring
  calc ((Polynomial.cauchyBound p : NNReal) : ℝ) ≤ ((C / L + 1 : NNReal) : ℝ) := by
        exact_mod_cast h
    _ = (C : ℝ) / (L : ℝ) + 1 := hcoe

end GaloisForLFunctions.Nevanlinna
