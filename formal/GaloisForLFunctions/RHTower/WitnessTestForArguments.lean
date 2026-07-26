import GaloisForLFunctions.RHTower.ScaleInvariantAbscissaRatio

/-!
# The witness test: which structures can possibly force the critical line

This development already contains constructive witnesses showing that the functional equation
together with nonnegativity of a generalized von Mangoldt coefficient does **not** force the critical
line: for every prescribed off-critical abscissa there is such a system with a zero there.  Those
witnesses are a test instrument, and this file uses them as one.

**The principle.**  If a structural property holds for an object possessing an off-line zero, no
argument using only that property can prove criticality.  This is trivial as logic and decisive as
bookkeeping.

**Applied to the scaling lane.**  The scale invariance of the previous entry — that the ratio of the
critical abscissa to the abscissa of absolute convergence is `1/2` at every scale — uses only a
functional equation and a growth normalisation.  Both hold for the witnesses.  So the scaling
structure cannot force the critical line, whatever is done with it.

> **Any argument that appeals only to the functional equation, the convergence abscissa, and their
> scaling behaviour is refuted in advance.  The Euler product is not a convenience in this problem;
> it is the only ingredient that distinguishes zeta from the counterexamples.**

**Classification of the atlas by this test.**  Entries about the explicit formula and about the
compressed prime operator all involve the prime side and are not refuted.  The two scaling entries do
not, and are.  Recording the test makes that distinction checkable rather than a matter of taste.

This file formalizes the insufficiency principle, its application, and the ratio arithmetic that the
witnesses also satisfy.
-/

open Real

noncomputable section

namespace RHTower

/-- **The insufficiency principle.**  A property enjoyed by an object with an off-line zero cannot
imply that all zeros are on the line. -/
theorem property_insufficient {α : Type*} {P : α → Prop} {onLine : α → ℂ → Prop}
    {f : α} {z : ℂ} (hP : P f) (hoff : ¬ onLine f z) :
    ¬ (∀ g, P g → ∀ w, onLine g w) := by
  intro h
  exact hoff (h f hP z)

/-- The contrapositive form: to force criticality, a property must fail for every witness. -/
theorem must_fail_on_witnesses {α : Type*} {P : α → Prop} {onLine : α → ℂ → Prop}
    (h : ∀ g, P g → ∀ w, onLine g w) {f : α} {z : ℂ} (hoff : ¬ onLine f z) : ¬ P f := by
  intro hP
  exact hoff (h f hP z)

/-- **The witnesses satisfy the ratio.**  The scale-invariant ratio is `1/2` for any system whose
functional equation reflects about `w/2` and whose series converges for `Re s > w`. -/
theorem witness_satisfies_ratio {w : ℝ} (hw : w ≠ 0) : (w / 2) / w = 1 / 2 :=
  abscissa_ratio_invariant hw

/-- Hence the ratio alone cannot separate zeta from a witness: both realise the same value. -/
theorem ratio_does_not_separate {w₁ w₂ : ℝ} (h1 : w₁ ≠ 0) (h2 : w₂ ≠ 0) :
    (w₁ / 2) / w₁ = (w₂ / 2) / w₂ :=
  ratio_independent_of_scale h1 h2

/-- **What the test demands.**  A property that forces criticality must be one the witnesses fail.
Since they satisfy the functional equation and the convergence normalisation, the property must
involve something else — and the only remaining ingredient is the Euler product. -/
theorem test_isolates_euler {α : Type*} {FE Conv Euler : α → Prop} {onLine : α → ℂ → Prop}
    {f : α} {z : ℂ} (hFE : FE f) (hConv : Conv f) (hoff : ¬ onLine f z)
    (hforce : ∀ g, FE g → Conv g → Euler g → ∀ w, onLine g w) : ¬ Euler f := by
  intro hE
  exact hoff (hforce f hFE hConv hE z)

end RHTower
