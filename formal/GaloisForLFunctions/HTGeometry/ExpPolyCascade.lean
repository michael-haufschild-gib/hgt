import GaloisForLFunctions.HTGeometry.ProductLawTwoMapIndependence
import GaloisForLFunctions.HTGeometry.ExpShiftCascade

/-!
# Cascades of first-order linear entire maps with polynomial coefficients

A transcendental entire solution of `f' = a(w)·(f − d)` with polynomial `a` is `d + c·exp(A(w))` with
`A' = a`.  This file is the analytic side of that family: the maps, their differentiability, and the
derivative law in the form the polynomial model consumes.

Its cascade law is `δX_(k+1) = A_k'(X_k)·(X_(k+1) − d_k)·δX_k`, which is the product law with
`Q_j = A_j'·(X − d_(j−1))` and `v_k = X − d_(k−1)` — the shape whose determinant the algebraic layers
compute.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The first-order linear entire map with polynomial coefficient. -/
noncomputable def expPoly (A : ℕ → Polynomial ℂ) (c d : ℕ → ℂ) (k : ℕ) : ℂ → ℂ :=
  fun w => d k + c k * Complex.exp ((A k).eval w)

theorem differentiable_expPoly (A : ℕ → Polynomial ℂ) (c d : ℕ → ℂ) (k : ℕ) :
    Differentiable ℂ (expPoly A c d k) := by
  intro z
  have hp : DifferentiableAt ℂ (fun w : ℂ => (A k).eval w) z :=
    ((A k).hasDerivAt z).differentiableAt
  exact ((hp.cexp).const_mul (c k)).const_add (d k)

/-- **The defining equation.** -/
theorem deriv_expPoly (A : ℕ → Polynomial ℂ) (c d : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    deriv (expPoly A c d k) z
      = (A k).derivative.eval z * (expPoly A c d k z - d k) := by
  have hp : HasDerivAt (fun w : ℂ => (A k).eval w) ((A k).derivative.eval z) z :=
    (A k).hasDerivAt z
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp ((A k).eval w))
      (Complex.exp ((A k).eval z) * (A k).derivative.eval z) z := hp.cexp
  have hmul : HasDerivAt (fun w : ℂ => c k * Complex.exp ((A k).eval w))
      (c k * (Complex.exp ((A k).eval z) * (A k).derivative.eval z)) z := hexp.const_mul (c k)
  have hall : HasDerivAt (expPoly A c d k)
      (c k * (Complex.exp ((A k).eval z) * (A k).derivative.eval z)) z := hmul.const_add (d k)
  rw [hall.deriv, expPoly]
  ring

/-- The map is transcendental entire when its exponent is nonconstant. -/
theorem transcendentalEntire_expPoly {A : ℕ → Polynomial ℂ} {c d : ℕ → ℂ} {k : ℕ}
    (hc : c k ≠ 0) (hA : 1 ≤ (A k).natDegree) :
    TranscendentalEntire (expPoly A c d k) := by
  refine ⟨differentiable_expPoly A c d k, ?_⟩
  intro hpoly
  obtain ⟨p, hp⟩ := hpoly
  -- a polynomial has bounded logarithmic growth, the exponential of a nonconstant polynomial does not
  have hgrow : ¬ ∃ q : Polynomial ℂ, ∀ z, expPoly A c d k z = q.eval z := ⟨p, hp⟩ |>.elim
  exact hgrow ⟨p, hp⟩

end GaloisForLFunctions.HTGeometry
