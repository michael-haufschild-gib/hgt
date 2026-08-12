import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceGaussDecomposition

/-!
# Finite-block confluent Christoffel--Darboux laws

The ordinary confluent Christoffel--Darboux identity only needs one finite positive Hankel block.
This localization identifies the exact Gauss weight/root-derivative coupling used by moving
admission laws. No infinite moment extension or support representation enters.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Finite-block confluent Christoffel--Darboux identity. -/
theorem cdKernel_diag_mul_eq_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 < N)
    {xi : ℝ} {G : Polynomial ℝ}
    (hG : monicOrtho s (n + 1) = (X - C xi) * G) :
    (cdKernel s n xi).eval xi * momentInner s (monicOrtho s n) (monicOrtho s n) =
      G.eval xi * (monicOrtho s n).eval xi := by
  have hn0 : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
    (monicOrtho_inner_self_pos_below h (by omega)).ne'
  have hxi : (monicOrtho s (n + 1)).eval xi = 0 := by rw [hG]; simp
  have hpoly : (X - C xi) * (cdKernel s n xi * C
        (momentInner s (monicOrtho s n) (monicOrtho s n))) =
      (X - C xi) * (G * C ((monicOrtho s n).eval xi)) := by
    refine Polynomial.funext fun x => ?_
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    have hcd := christoffelDarboux_below h n hnN x xi
    rw [hxi, mul_zero, sub_zero] at hcd
    have h1 : (cdKernel s n xi).eval x = ∑ k ∈ Finset.range (n + 1),
        (monicOrtho s k).eval x * (monicOrtho s k).eval xi /
          momentInner s (monicOrtho s k) (monicOrtho s k) := by
      rw [cdKernel_symm, cdKernel_eval]
    have hQ : (monicOrtho s (n + 1)).eval x = (x - xi) * G.eval x := by
      rw [hG]; simp
    rw [h1, ← mul_assoc, hcd, hQ]
    field_simp
  have hcancel := mul_left_cancel₀ (X_sub_C_ne_zero xi) hpoly
  have hev := congrArg (Polynomial.eval xi) hcancel
  simpa using hev

/-- Christoffel weight times root derivative and preceding value is preceding norm. -/
theorem christoffel_mul_derivative_mul_prev_eq_normSq_below {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {x : ℝ}
    (hroot : (monicOrtho s (m + 1)).eval x = 0) :
    christoffel s m x * (monicOrtho s (m + 1)).derivative.eval x *
        (monicOrtho s m).eval x = monicOrthoNormSq s m := by
  obtain ⟨G, hG⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hderiv : (monicOrtho s (m + 1)).derivative.eval x = G.eval x := by
    rw [hG, Polynomial.derivative_mul]
    simp
  have hcd := cdKernel_diag_mul_eq_below h m hmN hG
  have hweight := christoffel_mul_cdKernel_below h m (by omega) x
  rw [hderiv, monicOrthoNormSq]
  calc
    christoffel s m x * G.eval x * (monicOrtho s m).eval x =
        christoffel s m x *
          ((cdKernel s m x).eval x *
            momentInner s (monicOrtho s m) (monicOrtho s m)) := by
      rw [hcd]
      ring
    _ = momentInner s (monicOrtho s m) (monicOrtho s m) := by
      rw [← mul_assoc, hweight, one_mul]

/-- Jacobi edge times Gauss weight and root derivative is current norm. -/
theorem monicOrthoBeta_mul_christoffel_mul_derivative_mul_prev_eq_normSq_below
    {N m : ℕ} (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N) {x : ℝ}
    (hroot : (monicOrtho s (m + 1)).eval x = 0) :
    monicOrthoBeta s (m + 1) * christoffel s m x *
        (monicOrtho s (m + 1)).derivative.eval x * (monicOrtho s m).eval x =
      monicOrthoNormSq s (m + 1) := by
  have hprev := christoffel_mul_derivative_mul_prev_eq_normSq_below h (by omega) hroot
  have hbeta := monicOrthoNormSq_mul_nextBeta h (by omega : m + 1 < N)
  calc
    _ = monicOrthoBeta s (m + 1) *
        (christoffel s m x * (monicOrtho s (m + 1)).derivative.eval x *
          (monicOrtho s m).eval x) := by ring
    _ = monicOrthoBeta s (m + 1) * monicOrthoNormSq s m := by rw [hprev]
    _ = monicOrthoNormSq s m * monicOrthoBeta s (m + 1) := by ring
    _ = monicOrthoNormSq s (m + 1) := hbeta

end HTGeometry
