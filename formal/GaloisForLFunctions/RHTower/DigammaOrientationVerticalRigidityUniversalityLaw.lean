import GaloisForLFunctions.HTGeometry.ExplicitDigammaOrientationLimit
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum

/-!
# Digamma-orientation vertical-rigidity universality

The infinite Boolean orientation theorem singles out the all-positive Gauss completion by its
upper-half-plane Herglotz sign.  The vertical-minimum theorem independently makes ordinary
digamma nondecreasing in absolute height.  Their exact source identity transports that height law
back to every Boolean completion satisfying the Herglotz condition.
-/

namespace GaloisForLFunctions.RHTower

open Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The global upper-half-plane sign condition for a Boolean signed Gauss completion. -/
def SignedDigammaBooleanHerglotz (ε : ℕ → Bool) : Prop :=
  ∀ w : ℂ, 0 < w.im → 0 ≤ (signedDigammaBooleanCompletion ε w).im

/-- Radial height monotonicity on every vertical line to the right of the first half-integer
digamma pole. -/
def SignedDigammaBooleanVerticalHeightMonotone (ε : ℕ → Bool) : Prop :=
  ∀ (a y z : ℝ), -(1 / 2 : ℝ) < a → |y| ≤ |z| →
    (signedDigammaBooleanCompletion ε
        ((a : ℂ) + (y : ℂ) * Complex.I)).re ≤
      (signedDigammaBooleanCompletion ε
        ((a : ℂ) + (z : ℂ) * Complex.I)).re

/-- A Herglotz Boolean completion is the explicit shifted-digamma source everywhere off its pole
lattice. -/
theorem signedDigammaBooleanCompletion_eq_source_of_herglotz
    {ε : ℕ → Bool} (hH : SignedDigammaBooleanHerglotz ε)
    {w : ℂ} (hw : ∀ n : ℕ, w + (1 / 2 : ℂ) ≠ -(n : ℂ)) :
    signedDigammaBooleanCompletion ε w = explicitDigammaHerglotzSource w := by
  have hε : ε = fun _ => false :=
    (signedDigammaBooleanCompletion_nonneg_iff_allPositive ε).mp hH
  subst ε
  exact signedDigammaBooleanCompletion_allPositive_eq_explicitDigammaHerglotzSource hw

/-- **Classification-to-height transport.**  The global Herglotz sign alone forces radial
real-part monotonicity on every vertical line right of the first pole. -/
theorem signedDigammaBooleanCompletion_verticalHeightMonotone_of_herglotz
    {ε : ℕ → Bool} (hH : SignedDigammaBooleanHerglotz ε) :
    SignedDigammaBooleanVerticalHeightMonotone ε := by
  have hε : ε = fun _ => false :=
    (signedDigammaBooleanCompletion_nonneg_iff_allPositive ε).mp hH
  subst ε
  intro a y z ha hyz
  have ha' : 0 < a + 1 / 2 := by linarith
  have hoff (t : ℝ) :
      ∀ n : ℕ,
        ((a : ℂ) + (t : ℂ) * Complex.I) + (1 / 2 : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.natCast_re,
      Complex.neg_re] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [signedDigammaBooleanCompletion_allPositive_eq_explicitDigammaHerglotzSource (hoff y),
    signedDigammaBooleanCompletion_allPositive_eq_explicitDigammaHerglotzSource (hoff z)]
  have hmono :=
    re_digamma_mono_of_abs_le (a := a + 1 / 2) ha' hyz
  have hargY :
      ((a : ℂ) + (y : ℂ) * Complex.I) + (1 / 2 : ℂ) =
        (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    push_cast
    ring
  have hargZ :
      ((a : ℂ) + (z : ℂ) * Complex.I) + (1 / 2 : ℂ) =
        (((a + 1 / 2 : ℝ) : ℂ) + (z : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [explicitDigammaHerglotzSource, explicitDigammaHerglotzSource, hargY, hargZ]
  simpa only [Complex.add_re, Complex.ofReal_re] using
    (add_le_add_right hmono Real.eulerMascheroniConstant)

/-- **Digamma-orientation vertical-rigidity universality law.**  The unique Herglotz orientation,
its exact closed form, and its vertical-height rigidity are one simultaneous certificate. -/
theorem digammaOrientation_verticalRigidityUniversality (ε : ℕ → Bool) :
    SignedDigammaBooleanHerglotz ε ↔
      ε = (fun _ => false) ∧
        (∀ w : ℂ, (∀ n : ℕ, w + (1 / 2 : ℂ) ≠ -(n : ℂ)) →
          signedDigammaBooleanCompletion ε w = explicitDigammaHerglotzSource w) ∧
        SignedDigammaBooleanVerticalHeightMonotone ε := by
  constructor
  · intro hH
    have hε : ε = fun _ => false :=
      (signedDigammaBooleanCompletion_nonneg_iff_allPositive ε).mp hH
    exact ⟨hε, fun _ hw =>
      signedDigammaBooleanCompletion_eq_source_of_herglotz hH hw,
      signedDigammaBooleanCompletion_verticalHeightMonotone_of_herglotz hH⟩
  · rintro ⟨hε, -, -⟩
    exact (signedDigammaBooleanCompletion_nonneg_iff_allPositive ε).mpr hε

end

end GaloisForLFunctions.RHTower
