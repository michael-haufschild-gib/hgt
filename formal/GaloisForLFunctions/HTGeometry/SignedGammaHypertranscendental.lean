import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance
import GaloisForLFunctions.HTGeometry.GammaHypertranscendental
import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental

/-!
# Hypertranscendence of shifted Gamma and digamma

The base case of the hypertranscendental direction of the signed-archimedean orbit-charge dichotomy: a
single unit-scale Gamma factor `Γ(s + μ)` — and its logarithmic derivative `ψ(s + μ)` — is
hypertranscendental, by translation invariance of hypertranscendence (`hypertranscendental_comp_add_const_iff`)
applied to Hölder's theorem `hypertranscendental_gamma` (resp. `hypertranscendental_digamma`).

This is the `d = 1`, charge `= 1` case: the shift-orbit charge cannot vanish for a single positive-order
factor, and the factor is hypertranscendental.  (Genuine rescaling `Γ(λs)`, `λ ≠ 1`, is *not* reachable
this way: the scaling invariance `hypertranscendental_comp_const_mul_iff` requires global smoothness, which
`Γ` lacks at its poles — but the commensurable-scale normal form of the card reduces every orbit to unit
scale with integer shifts, exactly the case handled here.)
-/

open GaloisForLFunctions

namespace HTGeometry

/-- **A shifted Gamma factor is hypertranscendental.**  `Γ(s + μ)` satisfies no algebraic differential
equation, by translation invariance of hypertranscendence applied to Hölder's theorem. -/
theorem hypertranscendental_gamma_add_const (μ : ℂ) :
    Hypertranscendental (fun s => Complex.Gamma (s + μ)) := by
  rw [hypertranscendental_comp_add_const_iff μ]
  exact hypertranscendental_gamma

/-- **A shifted digamma factor is hypertranscendental.**  `ψ(s + μ) = (Γ'/Γ)(s + μ)` satisfies no
algebraic differential equation — the log-derivative form of the base case, from
`hypertranscendental_digamma`. -/
theorem hypertranscendental_digamma_add_const (μ : ℂ) :
    Hypertranscendental (fun s => Complex.digamma (s + μ)) := by
  rw [hypertranscendental_comp_add_const_iff μ]
  exact hypertranscendental_digamma

end HTGeometry
