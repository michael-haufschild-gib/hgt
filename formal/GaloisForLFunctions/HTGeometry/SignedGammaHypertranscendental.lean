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

/-- **A nonzero scalar multiple of a shifted Gamma factor is hypertranscendental.**  `c·Γ(s+μ)`
(`c ≠ 0`) — the single-factor carrier with leading coefficient — remains hypertranscendental, by scaling
invariance (`hypertranscendental_const_mul_iff`). -/
theorem hypertranscendental_smul_gamma_add_const (c μ : ℂ) (hc : c ≠ 0) :
    Hypertranscendental (fun s => c * Complex.Gamma (s + μ)) := by
  rw [hypertranscendental_const_mul_iff hc]
  exact hypertranscendental_gamma_add_const μ

/-- **A nonzero single-term digamma carrier is hypertranscendental.**  `m·ψ(s+μ)` (`m ≠ 0`) — the
`d = 1`, single-orbit logarithmic-derivative carrier `G'/G` of a single Gamma factor `Γ(s+μ)^m`, whose
orbit charge `m` is nonzero — is hypertranscendental.  This is the `d = 1` case of the hypertranscendental
direction read off the digamma carrier; the multi-term sum `∑_j m_j·ψ(s+n_j)` (a nonzero-charge
combination) is the genuine Adamczewski–Dreyfus–Hardouin content. -/
theorem hypertranscendental_smul_digamma_add_const (c μ : ℂ) (hc : c ≠ 0) :
    Hypertranscendental (fun s => c * Complex.digamma (s + μ)) := by
  rw [hypertranscendental_const_mul_iff hc]
  exact hypertranscendental_digamma_add_const μ

end HTGeometry
