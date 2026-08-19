import Mathlib

/-!
# Completely monotone functions have completely monotone samples

A completely monotone function on the open half line, presented by its derivative tower, has
alternating forward differences of every order at every step.  Sampling it on an arithmetic
progression therefore yields a completely monotone sequence in the Hausdorff sense.

The induction replaces the tower `F` by the shifted-difference tower `x ↦ F k x - F k (x+h)`,
whose signs are exactly the antitonicity of the alternating derivatives.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- A completely monotone function on `(0,∞)`, presented together with its derivative tower. -/
structure CompletelyMonotoneTower (F : ℕ → ℝ → ℝ) : Prop where
  hasDeriv : ∀ k x, 0 < x → HasDerivAt (F k) (F (k + 1) x) x
  sign : ∀ k x, 0 < x → 0 ≤ (-1 : ℝ) ^ k * F k x

/-- Every alternating derivative of a completely monotone tower is antitone on the half line. -/
theorem antitoneOn_alternating {F : ℕ → ℝ → ℝ} (hF : CompletelyMonotoneTower F) (k : ℕ) :
    AntitoneOn (fun x => (-1 : ℝ) ^ k * F k x) (Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
  · intro x hx
    have hc : ContinuousAt (fun y : ℝ => (-1 : ℝ) ^ k * F k y) x :=
      continuousAt_const.mul ((hF.hasDeriv k x hx).continuousAt)
    exact hc.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (((hF.hasDeriv k x hx).const_mul ((-1 : ℝ) ^ k)).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [((hF.hasDeriv k x hx).const_mul ((-1 : ℝ) ^ k)).deriv]
    have hs := hF.sign (k + 1) x hx
    rw [pow_succ] at hs
    nlinarith [hs]

/-- The shifted-difference tower of a completely monotone tower. -/
def shiftedDifferenceTower (F : ℕ → ℝ → ℝ) (h : ℝ) : ℕ → ℝ → ℝ :=
  fun k x => F k x - F k (x + h)

theorem completelyMonotoneTower_shiftedDifference {F : ℕ → ℝ → ℝ}
    (hF : CompletelyMonotoneTower F) {h : ℝ} (hh : 0 < h) :
    CompletelyMonotoneTower (shiftedDifferenceTower F h) where
  hasDeriv := by
    intro k x hx
    have h1 := hF.hasDeriv k x hx
    have hshift : HasDerivAt (fun y : ℝ => F k (y + h)) (F (k + 1) (x + h)) x := by
      have hinner : HasDerivAt (fun y : ℝ => y + h) 1 x := (hasDerivAt_id x).add_const h
      have hcomp := (hF.hasDeriv k (x + h) (by linarith)).comp x hinner
      simpa only [Function.comp_def, mul_one] using! hcomp
    exact h1.sub hshift
  sign := by
    intro k x hx
    have hanti := antitoneOn_alternating hF k (mem_Ioi.mpr hx)
      (mem_Ioi.mpr (by linarith : (0:ℝ) < x + h)) (by linarith)
    rw [shiftedDifferenceTower]
    nlinarith [hanti]

theorem fwdDiff_iterate_neg (h : ℝ) (g : ℝ → ℝ) (k : ℕ) :
    (fwdDiff h)^[k] (fun x => -g x) = fun x => -((fwdDiff h)^[k] g x) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have hstep : fwdDiff h (fun x => -g x) = fun x => -(fwdDiff h g x) := by
        funext x
        rw [fwdDiff, fwdDiff]
        ring
      rw [hstep, ih]

/-- **Alternating forward differences.**  Every forward difference of a completely monotone tower
alternates in sign on the half line. -/
theorem fwdDiff_iterate_alternating {h : ℝ} (hh : 0 < h) :
    ∀ (k : ℕ) {F : ℕ → ℝ → ℝ}, CompletelyMonotoneTower F →
      ∀ {x : ℝ}, 0 < x → 0 ≤ (-1 : ℝ) ^ k * (fwdDiff h)^[k] (F 0) x := by
  intro k
  induction k with
  | zero =>
      intro F hF x hx
      simpa using hF.sign 0 x hx
  | succ k ih =>
      intro F hF x hx
      have hfun : fwdDiff h (F 0) = fun y => -(shiftedDifferenceTower F h 0 y) := by
        funext y
        rw [fwdDiff, shiftedDifferenceTower]
        ring
      rw [Function.iterate_succ_apply, hfun, fwdDiff_iterate_neg]
      have hrec := ih (completelyMonotoneTower_shiftedDifference hF hh) hx
      have hpow : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by
        rw [pow_succ]; ring
      rw [hpow]
      nlinarith [hrec]

/-- **Sampling.**  A completely monotone function restricts to a completely monotone sequence on
every arithmetic progression inside the half line. -/
theorem fwdDiff_one_sample_alternating {F : ℕ → ℝ → ℝ} (hF : CompletelyMonotoneTower F)
    {x₀ h : ℝ} (hx₀ : 0 < x₀) (hh : 0 < h) (m k : ℕ) :
    0 ≤ (-1 : ℝ) ^ k * ((fwdDiff 1)^[k] (fun n : ℕ => F 0 (x₀ + n * h)) m) := by
  have hsample : ∀ (j : ℕ) (g : ℝ → ℝ) (n : ℕ),
      (fwdDiff 1)^[j] (fun n : ℕ => g (x₀ + n * h)) n =
        (fwdDiff h)^[j] g (x₀ + n * h) := by
    intro j
    induction j with
    | zero => intro g n; rfl
    | succ j ih =>
        intro g n
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        have hstep : (fun n : ℕ => fwdDiff h g (x₀ + n * h)) =
            fwdDiff 1 (fun n : ℕ => g (x₀ + n * h)) := by
          funext n
          rw [fwdDiff, fwdDiff]
          congr 2
          push_cast
          ring
        rw [← hstep, ih]
  rw [hsample k (F 0) m]
  exact fwdDiff_iterate_alternating hh k hF (by positivity)

end GaloisForLFunctions.HTGeometry
