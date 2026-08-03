import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import GaloisForLFunctions.HTGeometry.ClockProbeSolutionSpace

/-!
# The one-dimensional case, including the oscillatory one

For a one-dimensional clock geometry the wave operator is the second derivative and the
potential-dressed equation is `u'' + V u = 0`. Both constant-potential regimes are settled here by
explicit solutions.

The oscillatory regime is the interesting one. There the natural probes are cosines, and every one
of them has zeros, so no probe of that family is globally nonvanishing. Determination nevertheless
holds, because a cosine centred at an event is nonvanishing *at that event*: the pointwise condition
is satisfied by a family whose members differ from event to event.

This is what the passage from a globally nonvanishing probe to the pointwise no-common-zero
condition buys, and it shows that weakening was not cosmetic.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The one-dimensional wave operator: the second derivative. -/
noncomputable def secondDeriv (u : ℝ → ℝ) : ℝ → ℝ := deriv (deriv u)

/-! ## Oscillatory regime -/

/-- Cosine probe centred at an event. -/
noncomputable def cosProbe (k a : ℝ) : ℝ → ℝ := fun x => Real.cos (k * (x - a))

theorem hasDerivAt_cosArg (k a x : ℝ) :
    HasDerivAt (fun t : ℝ => k * (t - a)) k x := by
  simpa using ((hasDerivAt_id x).sub_const a).const_mul k

theorem deriv_cosProbe (k a : ℝ) :
    deriv (cosProbe k a) = fun x => -Real.sin (k * (x - a)) * k := by
  funext x
  exact ((hasDerivAt_cosArg k a x).cos).deriv

theorem secondDeriv_cosProbe (k a x : ℝ) :
    secondDeriv (cosProbe k a) x = -(k ^ 2) * cosProbe k a x := by
  have h : HasDerivAt (fun t : ℝ => -Real.sin (k * (t - a)) * k)
      (-(Real.cos (k * (x - a)) * k) * k) x := by
    exact (((hasDerivAt_cosArg k a x).sin).neg).mul_const k
  rw [secondDeriv, deriv_cosProbe, h.deriv, cosProbe]
  ring

/-- **The cosine probe solves the oscillatory equation.** -/
theorem solvesPotentialWave_cosProbe (k a : ℝ) :
    SolvesPotentialWave secondDeriv (fun _ => k ^ 2) (cosProbe k a) := by
  intro x
  rw [secondDeriv_cosProbe]
  ring

theorem cosProbe_self (k a : ℝ) : cosProbe k a a = 1 := by
  simp [cosProbe]

/-- **The oscillatory potential is determined**, by cosines centred at each event. -/
theorem noCommonZero_oscillatory (k : ℝ) :
    NoCommonZero secondDeriv (fun _ => k ^ 2) := by
  refine noCommonZero_of_exists_normalized fun a => ?_
  exact ⟨cosProbe k a, solvesPotentialWave_cosProbe k a, cosProbe_self k a⟩

/-- Every cosine probe has a zero, so none of them is globally nonvanishing. -/
theorem cosProbe_eq_zero (k a : ℝ) (hk : k ≠ 0) :
    cosProbe k (a) (a + Real.pi / (2 * k)) = 0 := by
  have h : k * (a + Real.pi / (2 * k) - a) = Real.pi / 2 := by
    field_simp
    ring
  rw [cosProbe, h, Real.cos_pi_div_two]

/-! ## Non-oscillatory regime -/

/-- Hyperbolic cosine probe centred at an event. -/
noncomputable def coshProbe (s a : ℝ) : ℝ → ℝ := fun x => Real.cosh (s * (x - a))

theorem deriv_coshProbe (s a : ℝ) :
    deriv (coshProbe s a) = fun x => Real.sinh (s * (x - a)) * s := by
  funext x
  exact ((hasDerivAt_cosArg s a x).cosh).deriv

theorem secondDeriv_coshProbe (s a x : ℝ) :
    secondDeriv (coshProbe s a) x = s ^ 2 * coshProbe s a x := by
  have h : HasDerivAt (fun t : ℝ => Real.sinh (s * (t - a)))
      (Real.cosh (s * (x - a)) * s) x := (hasDerivAt_cosArg s a x).sinh
  rw [secondDeriv, deriv_coshProbe, (h.mul_const s).deriv, coshProbe]
  ring

/-- **The hyperbolic cosine probe solves the non-oscillatory equation.** -/
theorem solvesPotentialWave_coshProbe (s a : ℝ) :
    SolvesPotentialWave secondDeriv (fun _ => -(s ^ 2)) (coshProbe s a) := by
  intro x
  rw [secondDeriv_coshProbe]
  ring

/-- The hyperbolic cosine probe never vanishes. -/
theorem coshProbe_ne_zero (s a x : ℝ) : coshProbe s a x ≠ 0 :=
  ne_of_gt (Real.cosh_pos _)

/-- **The non-oscillatory potential is determined by a single globally nonvanishing probe.** -/
theorem noCommonZero_nonOscillatory (s : ℝ) :
    NoCommonZero secondDeriv (fun _ => -(s ^ 2)) :=
  noCommonZero_of_nonvanishing_probe (coshProbe_ne_zero s 0)
    (solvesPotentialWave_coshProbe s 0)

/-! ## Both regimes determine their potential -/

/-- **Any potential with the same solutions as the oscillatory one is that potential.** -/
theorem potential_eq_of_oscillatory (k : ℝ) {other : ℝ → ℝ}
    (hother : ∀ u ∈ solutionSet secondDeriv (fun _ => k ^ 2),
      SolvesPotentialWave secondDeriv other u) :
    other = fun _ => k ^ 2 :=
  potential_eq_of_noCommonZero (noCommonZero_oscillatory k) hother

/-- **The same for the non-oscillatory regime.** -/
theorem potential_eq_of_nonOscillatory (s : ℝ) {other : ℝ → ℝ}
    (hother : ∀ u ∈ solutionSet secondDeriv (fun _ => -(s ^ 2)),
      SolvesPotentialWave secondDeriv other u) :
    other = fun _ => -(s ^ 2) :=
  potential_eq_of_noCommonZero (noCommonZero_nonOscillatory s) hother

end GaloisForLFunctions.HTGeometry
