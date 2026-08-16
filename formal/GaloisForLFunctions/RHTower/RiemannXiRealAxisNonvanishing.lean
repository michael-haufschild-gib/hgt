import GaloisForLFunctions.RHTower.RiemannXiRealRayNonvanishing
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# The completed Xi function has no real zeros

The corpus owns the positive ray; the functional equation `ξ(1−s) = ξ(s)` carries it to the rest of
the line, because `σ ≤ 0` gives `1 − σ ≥ 1 > 0`.  This is the regularity the torque card's `(19)`
needs of the two Xi arguments of `(16)`.
-/

noncomputable section

namespace RHTower

/-- The two spellings of the completed Xi function agree. -/
theorem xi_eq_riemannXi (s : ℂ) : xi s = riemannXi s := by
  rw [xi, riemannXi]
  ring

/-- **`ξ` has no zero on the real axis.** -/
theorem xi_ne_zero_of_ofReal (σ : ℝ) : xi ((σ : ℂ)) ≠ 0 := by
  rcases lt_or_ge 0 σ with h | h
  · rw [xi_eq_riemannXi]
    exact GaloisForLFunctions.RHTower.riemannXi_ne_zero_of_ofReal_pos h
  · have hpos : (0 : ℝ) < 1 - σ := by linarith
    have hfe : xi ((((1 - σ : ℝ)) : ℂ)) = xi ((σ : ℂ)) := by
      have hcast : ((((1 - σ : ℝ)) : ℂ)) = 1 - ((σ : ℂ)) := by push_cast; ring
      rw [hcast, xi_one_sub]
    rw [← hfe, xi_eq_riemannXi]
    exact GaloisForLFunctions.RHTower.riemannXi_ne_zero_of_ofReal_pos hpos

end RHTower
