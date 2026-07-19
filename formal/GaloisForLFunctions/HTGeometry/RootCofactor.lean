import GaloisForLFunctions.HTGeometry.SortedNodes

/-!
# The cofactor at a simple root

Each root `ξ` of `Q_{n+1}` is simple (link 61), so `Q_{n+1} = (X - ξ) G` with `G(ξ) ≠ 0`.  The
nonvanishing is exactly what simplicity buys: were `G(ξ) = 0`, the factor `(X - ξ)` would divide
`Q_{n+1}` twice.

`G(ξ)` plays the role the derivative `Q'_{n+1}(ξ)` plays in the classical treatment, without any
derivative being taken.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The cofactor at a root does not vanish there.** -/
theorem exists_cofactor (h : PositiveMomentForm s) (n : ℕ) {xi : ℝ}
    (hxi : (monicOrtho s (n + 1)).eval xi = 0) :
    ∃ G : Polynomial ℝ, monicOrtho s (n + 1) = (X - C xi) * G ∧ G.eval xi ≠ 0 := by
  obtain ⟨G, hG⟩ := dvd_iff_isRoot.mpr hxi
  refine ⟨G, hG, ?_⟩
  intro h0
  obtain ⟨H, hH⟩ := dvd_iff_isRoot.mpr h0
  refine monicOrtho_not_sq_dvd h n xi ⟨H, ?_⟩
  rw [hG, hH]
  ring

/-- The cofactor is nonzero as a polynomial. -/
theorem cofactor_ne_zero (s : ℕ → ℝ) (n : ℕ) {xi : ℝ} {G : Polynomial ℝ}
    (hG : monicOrtho s (n + 1) = (X - C xi) * G) : G ≠ 0 := by
  intro h0
  rw [h0, mul_zero] at hG
  exact monicOrtho_ne_zero s (n + 1) hG

end HTGeometry
