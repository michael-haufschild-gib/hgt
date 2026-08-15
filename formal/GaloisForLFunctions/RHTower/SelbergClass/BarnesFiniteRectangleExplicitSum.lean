import GaloisForLFunctions.RHTower.SelbergClass.BarnesFiniteRectangleIntegral

/-!
# Explicit finite Barnes rectangle sum

This is the finite residue expansion for the concrete Barnes integrand.  It
does not take a height limit, a left-edge limit, or evaluate the resulting
infinite Barnes integral.
-/

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-- The fixed Barnes rectangle equals the finite sum of its explicit
negative-integer Gamma residues. -/
theorem rectangleIntegral_barnesJ_eq_range_sum
    {ξ η : ℂ} {m : ℕ} {c T : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hT : 0 < T) (hη : η ≠ 0) :
    RectangleIntegral' (barnesJ ξ η) (barnesLeftCorner m T) (barnesRightCorner c T) =
      ∑ n ∈ Finset.range (m + 1),
        ((-1 : ℂ) ^ n / (n.factorial : ℂ)) * Gamma (ξ + n) * η ^ n := by
  rw [rectangleIntegral_barnesJ_eq_finset_sum hc hcξ hT hη, barnesPoleFinset]
  rw [Finset.sum_image]
  · simp_rw [residue_barnesJ_neg_nat (by linarith) hη]
  · intro a ha b hb hab
    have hcast : (a : ℂ) = b := by
      have := congrArg Neg.neg hab
      simpa using this
    exact_mod_cast hcast

end

end RHTower
