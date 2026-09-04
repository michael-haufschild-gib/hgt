import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Analyticity of `Γ` off its poles

`Complex.Gamma` is analytic at every point that is not a pole.  Mathlib proves smoothness
(`contDiffAt_Gamma`) and entirety of the reciprocal (`differentiable_one_div_Gamma`) but does not
expose analyticity itself, so the corpus re-derived it repeatedly in half a dozen files, each time
in the specialised form it happened to need.

This file carries the single general law -- analyticity away from `-ℕ` -- and the one specialisation
every contour argument actually uses, analyticity on the open right half-plane.  Both are pure
mathlib consequences, so the module sits at the bottom of `HTGeometry` and imports nothing else
from the project.
-/

open Complex

namespace HTGeometry

/-- **The totalized complex Gamma function is Borel measurable.**  Mathlib's reciprocal Gamma is
entire; measurable inversion recovers `Gamma`, including its totalized values at the poles. -/
theorem measurable_Gamma : Measurable Complex.Gamma := by
  have hinv : Continuous (fun s : ℂ => (Complex.Gamma s)⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous
  have hmeas : Measurable (fun s : ℂ => ((Complex.Gamma s)⁻¹)⁻¹) :=
    hinv.measurable.inv
  simpa only [inv_inv] using hmeas

/-- **The totalized real Gamma function is Borel measurable.**  This is the restriction of the
complex statement to the real axis, followed by the continuous real-part map. -/
theorem measurable_realGamma : Measurable Real.Gamma := by
  have h := Complex.measurable_re.comp (measurable_Gamma.comp Complex.measurable_ofReal)
  change Measurable (fun s : ℝ => (Complex.Gamma (s : ℂ)).re) at h
  simpa only [Complex.Gamma_ofReal, Complex.ofReal_re] using h

/-- **`Γ` is analytic off its poles.**  At any `x ∉ -ℕ`, `Complex.Gamma` is the pointwise inverse of
the entire reciprocal `1/Γ`, which is nonzero exactly off the poles; inversion preserves analyticity
at a nonvanishing point. -/
theorem analyticAt_Gamma_off_poles {x : ℂ} (hx : ∀ n : ℕ, x ≠ -(n : ℂ)) :
    AnalyticAt ℂ Complex.Gamma x := by
  have hinv : AnalyticAt ℂ (fun s => (Complex.Gamma s)⁻¹) x :=
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ) x
      (Set.mem_univ x)
  have hΓ : AnalyticAt ℂ (fun s => ((Complex.Gamma s)⁻¹)⁻¹) x :=
    hinv.inv (inv_ne_zero (Complex.Gamma_ne_zero hx))
  have heq : (fun s => ((Complex.Gamma s)⁻¹)⁻¹) = Complex.Gamma := by funext s; rw [inv_inv]
  rwa [heq] at hΓ

/-- A point of positive real part is not a pole of `Γ`: every pole has nonpositive real part. -/
theorem ne_neg_natCast_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ n : ℕ, s ≠ -(n : ℂ) := by
  intro n h
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- **`Γ` is analytic on the open right half-plane** -- the specialisation of
`analyticAt_Gamma_off_poles` used by every Mellin and contour argument in the corpus. -/
theorem analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Complex.Gamma s :=
  analyticAt_Gamma_off_poles (ne_neg_natCast_of_re_pos hs)

end HTGeometry
