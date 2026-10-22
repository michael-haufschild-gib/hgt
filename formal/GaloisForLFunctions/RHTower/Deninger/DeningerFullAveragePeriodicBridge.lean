/-
The Deninger averaging layer is the `p = 2πi` case of the general periodic averaging layer.

`RHTower/DeningerFullAverage` builds the constant-plus-exact decomposition of a closed periodic
`C^(1 : ℕ)` form on `(Fin r → ℂ)` with period `2πi`, through its own averaged-data recursion.
`HTGeometry/PeriodicFullAverage` builds the same decomposition for an arbitrary `RCLike` scalar
field and an arbitrary nonzero period, and additionally proves that the constant form of the
decomposition is **unique**.

Instantiating the general layer at `𝕜 = ℂ`, `p = 2πi` reproduces the Deninger statement verbatim,
so the Deninger recursion is not an independent result; and the uniqueness half, which the Deninger
layer never proved, transfers with it.  This file records the instantiation and the consequences
the Deninger side was missing:

* `deningerPeriodic_const_add_exact_unique` — the constant form of the decomposition is unique;
* `deningerPeriodic_closed_eq_const_add_exact_of_periodic` — the existence half, with the Deninger
  averaging recursion replaced by the general instantiation.

No averaging argument is repeated: each proof supplies the general theorem's period hypothesis with
`deningerPeriod_ne_zero`.
-/
import GaloisForLFunctions.RHTower.Deninger.DeningerFullAverage
import GaloisForLFunctions.HTGeometry.PeriodicFullAverage

namespace RHTower

open Complex ContinuousAlternatingMap GaloisForLFunctions.HTGeometry

section DeningerPeriodBridge

variable {r n : ℕ}

/-- The Deninger period `2πi` is nonzero, the only hypothesis the general periodic layer needs. -/
theorem deningerPeriod_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
  exact_mod_cast Real.pi_ne_zero

/-- **The constant form of the Deninger decomposition is unique.**  The Deninger case of
`periodic_const_add_exact_unique`; the Deninger averaging layer proved existence only. -/
theorem deningerPeriodic_const_add_exact_unique
    {α α' : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    {η : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ}
    (hdiff : Differentiable ℂ η) (hcont' : Continuous (fderiv ℂ η))
    (hper : ∀ (l : Fin r) (w : Fin r → ℂ),
      η (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = η w)
    (heq : ∀ w : Fin r → ℂ, α = α' + extDeriv η w) : α = α' :=
  periodic_const_add_exact_unique deningerPeriod_ne_zero hdiff hcont' hper heq

/-- **The Deninger decomposition, obtained from the general periodic layer.**  This is
`deningerPeriodic_closed_eq_const_add_exact` with its own averaging recursion replaced by the
instantiation `𝕜 = ℂ`, `p = 2πi` of `periodic_closed_eq_const_add_exact`. -/
theorem deningerPeriodic_closed_eq_const_add_exact_of_periodic
    {β : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ} (hdiff : Differentiable ℂ β)
    (hcont' : Continuous (fderiv ℂ β))
    (hper : ∀ (l : Fin r) (w : Fin r → ℂ),
      β (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = β w)
    (hclosed : ∀ w : Fin r → ℂ, extDeriv β w = 0) :
    ∃ (α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ)
      (η : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ),
      Differentiable ℂ η ∧ Continuous (fderiv ℂ η) ∧
      (∀ (l : Fin r) (w : Fin r → ℂ), η (w + (2 * Real.pi * Complex.I) •
        (Pi.single l (1 : ℂ) : Fin r → ℂ)) = η w) ∧
      ∀ w : Fin r → ℂ, β w = α + extDeriv η w :=
  periodic_closed_eq_const_add_exact deningerPeriod_ne_zero hdiff hcont' hper hclosed

/-!
Packaging existence and uniqueness as one `∃!` would need the difference of two `C^(1 : ℕ)` primitives,
whose `fderiv` continuity is the continuity of a sum in
`(Fin r → ℂ) →L[ℂ] (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ`.  That space carries the strong operator topology,
for which `ContinuousAdd` is not available here, so the pairwise uniqueness statement above is the
usable form — and it is the form the general periodic layer's consumers use, always at `α' = 0`.
-/

end DeningerPeriodBridge

end RHTower
