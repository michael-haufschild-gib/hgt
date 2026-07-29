import Mathlib

/-!
# A decreasing log-concave kernel is log-concave in the logarithmic variable

The Jensen dispersion consumed by the hyperbolicity criterion is `Var_π(log s)` for the tilted
measure `π ∝ u^{2n} Φ(u) du`, `s = u²`.  Passing to `L = log u` turns the tilt into a *linear* term:
the density of `L` is proportional to `exp((2n+1)L + log Φ(exp L))`, and the `n`-dependence
contributes nothing to the second derivative.  Hence the concavity of the log-density is a property
of `Φ` alone, and it is

```text
−(log Φ(e^L))''  =  u·|(log Φ)'(u)|  +  u²·(−(log Φ)''(u)) ,      u = e^L ,
```

which is nonnegative as soon as `Φ` is **decreasing** and **log-concave** — two properties the
classical theta kernel has.  Both terms matter: the first alone already grows like the tilt
parameter, and the second carries the double-exponential decay.

This is the step that converts source regularity into an *upper* bound on a variance.  Positivity of
`Φ` gives Hankel positivity and therefore lower bounds on moment ratios; log-concavity, through the
one-dimensional Brascamp–Lieb inequality applied to the log-density below, gives the opposite
direction, which is what every hyperbolicity criterion actually consumes.
-/

open Real

namespace GaloisForLFunctions

namespace LogTilt

variable {logPhi p q : ℝ → ℝ}

/-- The log-density of `L = log u` under the tilt `u^{2n}Φ(u) du`, up to an additive constant. -/
noncomputable def logTiltDensity (logPhi : ℝ → ℝ) (n : ℕ) (L : ℝ) : ℝ :=
  (2 * (n : ℝ) + 1) * L + logPhi (Real.exp L)

/-- First derivative of the log-density in the logarithmic variable. -/
theorem hasDerivAt_logTiltDensity
    (hp : ∀ u : ℝ, 0 < u → HasDerivAt logPhi (p u) u) (n : ℕ) (L : ℝ) :
    HasDerivAt (logTiltDensity logPhi n)
      ((2 * (n : ℝ) + 1) + Real.exp L * p (Real.exp L)) L := by
  have hexp : HasDerivAt Real.exp (Real.exp L) L := Real.hasDerivAt_exp L
  have hcomp : HasDerivAt (fun L => logPhi (Real.exp L)) (p (Real.exp L) * Real.exp L) L :=
    (hp _ (Real.exp_pos L)).comp L hexp
  have hlin : HasDerivAt (fun L : ℝ => (2 * (n : ℝ) + 1) * L) (2 * (n : ℝ) + 1) L := by
    simpa using (hasDerivAt_id L).const_mul (2 * (n : ℝ) + 1)
  have := hlin.add hcomp
  refine this.congr_deriv ?_
  ring

/-- The derivative of the log-density, as a function of `L`. -/
noncomputable def logTiltSlope (p : ℝ → ℝ) (n : ℕ) (L : ℝ) : ℝ :=
  (2 * (n : ℝ) + 1) + Real.exp L * p (Real.exp L)

/-- **Second derivative in the logarithmic variable.**  The tilt parameter `n` drops out: the
curvature is `u·(log Φ)'(u) + u²·(log Φ)''(u)` at `u = exp L`. -/
theorem hasDerivAt_logTiltSlope
    (hq : ∀ u : ℝ, 0 < u → HasDerivAt p (q u) u) (n : ℕ) (L : ℝ) :
    HasDerivAt (logTiltSlope p n)
      (Real.exp L * p (Real.exp L) + (Real.exp L) ^ 2 * q (Real.exp L)) L := by
  have hexp : HasDerivAt Real.exp (Real.exp L) L := Real.hasDerivAt_exp L
  have hpc : HasDerivAt (fun L => p (Real.exp L)) (q (Real.exp L) * Real.exp L) L :=
    (hq _ (Real.exp_pos L)).comp L hexp
  have hmul : HasDerivAt (fun L => Real.exp L * p (Real.exp L))
      (Real.exp L * p (Real.exp L) + Real.exp L * (q (Real.exp L) * Real.exp L)) L := by
    rw [show (fun L => Real.exp L * p (Real.exp L)) =
      Real.exp * fun L => p (Real.exp L) by rfl]
    exact hexp.mul hpc
  have := hmul.const_add (2 * (n : ℝ) + 1)
  refine this.congr_deriv ?_
  ring

/-- **A decreasing log-concave kernel is log-concave in the logarithmic variable.**  If
`(log Φ)' ≤ 0` and `(log Φ)'' ≤ 0` on the positive axis, then the log-density of `L = log u` under
every tilt `u^{2n}Φ(u) du` has nonpositive second derivative — and the bound is uniform in `n`,
because the tilt is linear in `L`. -/
theorem logTilt_curvature_nonpos
    (hpneg : ∀ u : ℝ, 0 < u → p u ≤ 0) (hqneg : ∀ u : ℝ, 0 < u → q u ≤ 0) (L : ℝ) :
    Real.exp L * p (Real.exp L) + (Real.exp L) ^ 2 * q (Real.exp L) ≤ 0 := by
  have hu : (0 : ℝ) < Real.exp L := Real.exp_pos L
  have h1 : Real.exp L * p (Real.exp L) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.le (hpneg _ hu)
  have h2 : (Real.exp L) ^ 2 * q (Real.exp L) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (hqneg _ hu)
  linarith

/-- The curvature in closed form: `−(log Φ(e^L))'' = u|(log Φ)'(u)| + u²(−(log Φ)''(u))`.  Both terms
are nonnegative under the hypotheses, and they are the two independent sources of concentration:
monotonicity of the kernel and its log-concavity. -/
theorem logTilt_curvature_eq
    (hpneg : ∀ u : ℝ, 0 < u → p u ≤ 0) (hqneg : ∀ u : ℝ, 0 < u → q u ≤ 0) (L : ℝ) :
    -(Real.exp L * p (Real.exp L) + (Real.exp L) ^ 2 * q (Real.exp L))
      = Real.exp L * |p (Real.exp L)| + (Real.exp L) ^ 2 * |q (Real.exp L)| := by
  have hu : (0 : ℝ) < Real.exp L := Real.exp_pos L
  rw [abs_of_nonpos (hpneg _ hu), abs_of_nonpos (hqneg _ hu)]
  ring

/-- **Strict concavity from either source.**  If the kernel is strictly decreasing at a point, or
strictly log-concave there, the log-density is strictly concave there — so no uniform hypothesis on
both is needed. -/
theorem logTilt_curvature_neg
    (hpneg : ∀ u : ℝ, 0 < u → p u ≤ 0) (hqneg : ∀ u : ℝ, 0 < u → q u ≤ 0) (L : ℝ)
    (hstrict : p (Real.exp L) < 0 ∨ q (Real.exp L) < 0) :
    Real.exp L * p (Real.exp L) + (Real.exp L) ^ 2 * q (Real.exp L) < 0 := by
  have hu : (0 : ℝ) < Real.exp L := Real.exp_pos L
  have hu2 : (0 : ℝ) < (Real.exp L) ^ 2 := by positivity
  rcases hstrict with h | h
  · have h1 : Real.exp L * p (Real.exp L) < 0 := mul_neg_of_pos_of_neg hu h
    have h2 : (Real.exp L) ^ 2 * q (Real.exp L) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hu2.le (hqneg _ hu)
    linarith
  · have h1 : Real.exp L * p (Real.exp L) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.le (hpneg _ hu)
    have h2 : (Real.exp L) ^ 2 * q (Real.exp L) < 0 := mul_neg_of_pos_of_neg hu2 h
    linarith

end LogTilt

end GaloisForLFunctions
