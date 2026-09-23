import GaloisForLFunctions.HTGeometry.GammaFactorialComposition

/-!
# The Riccati boundary of the Gamma factorial microscope

The factorial microscope sends Gamma to the reciprocal germ `M(x) = -1/x`, whose first jet lies
on the Riccati hypersurface `M' = M²`.  This module records the corresponding first-jet collapse for
the exact Gamma zoom.  The vanishing limit is the boundary kernel that must be crossed at the next
harmonic residue in any proof of joint first-jet independence of Gamma iterates.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

/-- The first-jet Riccati defect of the factorially rescaled Gamma germ. -/
def gammaFactorialFirstJetDefect (n : ℕ) (x : ℂ) : ℂ :=
  iteratedDeriv 1 (factorialBlowUpZoom Complex.Gamma n) x -
    factorialBlowUpZoom Complex.Gamma n x ^ (2 : ℕ)

/-- The reciprocal boundary germ lies exactly on the Riccati hypersurface `y' = y²`. -/
theorem iteratedDeriv_one_outerReciprocalLimit_id (x : ℂ) (hx : x ≠ 0) :
    iteratedDeriv 1 (outerReciprocalLimit id) x =
      outerReciprocalLimit id x ^ (2 : ℕ) := by
  rw [iteratedDeriv_one]
  have h : HasDerivAt (fun x : ℂ => (-x)⁻¹) (x⁻¹ ^ (2 : ℕ)) x := by
    simpa [inv_pow] using! (hasDerivAt_inv hx).neg
  rw [show outerReciprocalLimit id = fun x : ℂ => (-x)⁻¹ by
    funext y
    simp [outerReciprocalLimit]]
  rw [h.deriv]
  simp

/-- Along the Gamma factorial microscope, the exact first jet collapses onto the reciprocal
Riccati hypersurface.  This is a genuine jet limit, obtained from locally uniform holomorphic
convergence rather than from pointwise differentiation of a limit. -/
theorem tendsto_gammaFactorialFirstJetDefect_zero
    {x : ℂ} (hx : x ∈ gammaFactorialMicroscopeDomain) :
    Tendsto (fun n => gammaFactorialFirstJetDefect n x) atTop (𝓝 0) := by
  have h0 := iteratedDeriv_outerGamma_factorialBlowUp_tendsto
    id (fun _ _ => analyticAt_id) hx 0
  have h1 := iteratedDeriv_outerGamma_factorialBlowUp_tendsto
    id (fun _ _ => analyticAt_id) hx 1
  have h := h1.sub (h0.pow 2)
  have hx0 : x ≠ 0 := gammaFactorialMicroscopeDomain_ne_zero hx
  simp only [iteratedDeriv_zero] at h
  rw [iteratedDeriv_one_outerReciprocalLimit_id x hx0, sub_self] at h
  simpa [gammaFactorialFirstJetDefect, iteratedDeriv_zero] using h

end

end GaloisForLFunctions
