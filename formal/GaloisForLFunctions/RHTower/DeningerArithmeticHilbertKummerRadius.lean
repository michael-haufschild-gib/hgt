import Mathlib

/-!
# Hilbert--Kummer radius on Deninger's suspension

A Hilbert-bounded logarithmic modulus character is represented by a
continuous real linear functional.  Its operator norm scales linearly
under positive Frobenius.  Multiplication by inverse suspension height
cancels that scaling, while positive-time flow dilates the descended
radius.

This is the algebraic/normed core of the source radial collar.  No zeta
zero or Riemann-hypothesis premise occurs.
-/

namespace RHTower

noncomputable section

variable {H : Type*}
variable [SeminormedAddCommGroup H] [NormedSpace ℝ H]

/-- Operator-norm radius of a Hilbert-bounded Kummer modulus character. -/
def deningerHilbertKummerRadius (ell : H →L[ℝ] ℝ) : ℝ :=
  ‖ell‖

/-- Positive Frobenius scaling acts linearly on the Kummer radius. -/
theorem deningerHilbertKummerRadius_smul
    (q : ℝ) (hq : 0 ≤ q) (ell : H →L[ℝ] ℝ) :
    deningerHilbertKummerRadius (q • ell) =
      q * deningerHilbertKummerRadius ell := by
  simp [deningerHilbertKummerRadius, norm_smul, abs_of_nonneg hq]

/-- Radius multiplied by Deninger's positive suspension height. -/
def deningerHilbertKummerSuspensionRadius
    (u : ℝ) (ell : H →L[ℝ] ℝ) : ℝ :=
  u * deningerHilbertKummerRadius ell

/--
Inverse height scaling cancels positive Frobenius scaling, so the
Hilbert--Kummer radius descends to the suspension quotient.
-/
theorem deningerHilbertKummerSuspensionRadius_deck_invariant
    (u q : ℝ) (hq : 0 < q) (ell : H →L[ℝ] ℝ) :
    deningerHilbertKummerSuspensionRadius (u / q) (q • ell) =
      deningerHilbertKummerSuspensionRadius u ell := by
  rw [deningerHilbertKummerSuspensionRadius,
    deningerHilbertKummerRadius_smul q hq.le,
    deningerHilbertKummerSuspensionRadius]
  field_simp [hq.ne']

/-- Positive-time flow dilates the descended radius. -/
theorem deningerHilbertKummerSuspensionRadius_flow
    (u v : ℝ) (ell : H →L[ℝ] ℝ) :
    deningerHilbertKummerSuspensionRadius (u * v) ell =
      v * deningerHilbertKummerSuspensionRadius u ell := by
  simp only [deningerHilbertKummerSuspensionRadius]
  ring

/-- Scalar flow pullback is ordinary dilation on every radial function. -/
theorem deningerHilbertKummerFlowPullback_eq_dilation
    (f : ℝ → ℂ) (u v : ℝ) (ell : H →L[ℝ] ℝ) :
    f (deningerHilbertKummerSuspensionRadius (u * v) ell) =
      f (v * deningerHilbertKummerSuspensionRadius u ell) := by
  rw [deningerHilbertKummerSuspensionRadius_flow]

end

end RHTower
