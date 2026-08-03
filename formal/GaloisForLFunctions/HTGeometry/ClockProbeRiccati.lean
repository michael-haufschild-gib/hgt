import GaloisForLFunctions.HTGeometry.ClockPotentialLocalDetermination

/-!
# A variable-potential class determined by exponential probes

The one-dimensional constant-potential regimes were settled by explicit cosines and hyperbolic
cosines. Variable potentials need no existence theory either, provided one reads the equation in the
other direction.

Substituting `u = e^{w}` into `u'' + Vu = 0` gives `V = -(w'' + (w')²)`. So for **every** smooth `w`
the potential `-(w'' + (w')²)` carries the globally nonvanishing probe `e^{w}`, and is therefore
determined. This is a genuinely variable class: `w = x²` gives `V = -(2 + 4x²)`.

The class is exactly the Riccati range, which is the one-dimensional form of the characterization
already proved: a potential admits a nowhere-vanishing probe precisely when it is `-(□u)/u`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

/-- Exponential probe of a smooth exponent. -/
noncomputable def expProbe (w : ℝ → ℝ) : ℝ → ℝ := fun x => Real.exp (w x)

theorem expProbe_ne_zero (w : ℝ → ℝ) (x : ℝ) : expProbe w x ≠ 0 :=
  Real.exp_ne_zero _

theorem differentiable_deriv_of_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    Differentiable ℝ (deriv w) :=
  ((contDiff_infty_iff_deriv.mp hw).2).differentiable (by simp)

theorem hasDerivAt_expProbe {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (x : ℝ) :
    HasDerivAt (expProbe w) (Real.exp (w x) * deriv w x) x := by
  have hd : HasDerivAt w (deriv w x) x :=
    (hw.differentiable (by simp) x).hasDerivAt
  show HasDerivAt (fun t => Real.exp (w t)) (Real.exp (w x) * deriv w x) x
  simpa [mul_comm] using hd.exp

theorem deriv_expProbe {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    deriv (expProbe w) = fun x => Real.exp (w x) * deriv w x := by
  funext x
  exact (hasDerivAt_expProbe hw x).deriv

/-- **The exponential probe turns the equation into the Riccati relation.** -/
theorem secondDeriv_expProbe {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (x : ℝ) :
    secondDeriv (expProbe w) x =
      (deriv (deriv w) x + (deriv w x) ^ 2) * expProbe w x := by
  have hderiv : HasDerivAt (deriv w) (deriv (deriv w) x) x :=
    (differentiable_deriv_of_contDiff hw x).hasDerivAt
  have hprod : HasDerivAt (fun t => Real.exp (w t) * deriv w t)
      (Real.exp (w x) * deriv w x * deriv w x + Real.exp (w x) * deriv (deriv w) x) x :=
    (hasDerivAt_expProbe hw x).mul hderiv
  rw [secondDeriv, deriv_expProbe hw, hprod.deriv, expProbe]
  ring

/-- The potential carried by an exponential probe. -/
noncomputable def riccatiPotential (w : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -(deriv (deriv w) x + (deriv w x) ^ 2)

/-- **Every smooth exponent yields a solved variable potential.** -/
theorem solvesPotentialWave_expProbe {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    SolvesPotentialWave secondDeriv (riccatiPotential w) (expProbe w) := by
  intro x
  rw [secondDeriv_expProbe hw, riccatiPotential]
  ring

/-- **Every Riccati potential is determined**, by a globally nonvanishing probe. -/
theorem noCommonZero_riccatiPotential {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    NoCommonZero secondDeriv (riccatiPotential w) :=
  noCommonZero_of_nonvanishing_probe (expProbe_ne_zero w) (solvesPotentialWave_expProbe hw)

/-- **Any potential with the same solutions as a Riccati potential is that potential.** -/
theorem potential_eq_riccatiPotential {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) {other : ℝ → ℝ}
    (hother : ∀ u ∈ solutionSet secondDeriv (riccatiPotential w),
      SolvesPotentialWave secondDeriv other u) :
    other = riccatiPotential w :=
  potential_eq_of_noCommonZero (noCommonZero_riccatiPotential hw) hother

/-! ### The class contains genuinely variable potentials -/

theorem contDiff_sq : ContDiff ℝ ∞ fun x : ℝ => x ^ 2 := by
  exact contDiff_id.pow 2

theorem deriv_sq_fun : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
  funext x
  simp

theorem riccatiPotential_sq : riccatiPotential (fun x : ℝ => x ^ 2) =
    fun x => -(2 + (2 * x) ^ 2) := by
  funext x
  rw [riccatiPotential, deriv_sq_fun]
  congr 1
  congr 1
  simp

/-- **A nonconstant determined potential.** -/
theorem noCommonZero_quadraticRiccati :
    NoCommonZero secondDeriv (fun x : ℝ => -(2 + (2 * x) ^ 2)) := by
  rw [← riccatiPotential_sq]
  exact noCommonZero_riccatiPotential contDiff_sq

end GaloisForLFunctions.HTGeometry
