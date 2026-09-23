import GaloisForLFunctions.HTGeometry.AbePoincareLocalNormal
import GaloisForLFunctions.HTGeometry.QuasiAbelianAbePositivityReduction

/-!
# Appell--Humbert factors satisfy Abe's lattice growth condition

`gaussianMajorant_of_hasLatticeExponentialGrowth` reduces the polynomial-Gaussian Poincaré majorant
to one primitive condition on the factor: on every compact set the reciprocal factor grows at most
exponentially in the `ℓ¹` size of the lattice index.  For the Appell--Humbert factor of a positive
semidefinite Hermitian form that condition holds with growth rate **zero** — the reciprocal factor is
not merely subexponential in the lattice index, it is bounded, because the exponent
`−π·Re H(x,γ) − (π/2)·H(γ,γ)` is at most `π·C²` uniformly once `Re H(x,x) ≤ C²`.

So the analytic hypothesis of the corpus's majorant chain is discharged outright for this class.

* `hasLatticeExponentialGrowth_appellHumbert`.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ} {H : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} {χ : (Fin d → ℂ) → ℂ}

/-- **The Appell--Humbert factor of a positive semidefinite Hermitian form satisfies Abe's lattice
growth condition**, with growth rate zero. -/
theorem hasLatticeExponentialGrowth_appellHumbert (hH : IsHermitianForm H)
    (hpos : ∀ y : Fin d → ℂ, 0 ≤ (H y y).re) (hχ : ∀ γ, ‖χ γ‖ = 1)
    (hsemi : IsSemicharacterOn H χ (standardIntegerLattice d)) :
    (appellHumbertAutomorphicFactor hH hχ hsemi).HasLatticeExponentialGrowth := by
  intro K hK
  obtain ⟨CD, hCD⟩ := hK.exists_bound_of_continuousOn
    (f := fun y : Fin d → ℂ => (H y y).re) ((continuous_hermitian_self_re hH).continuousOn)
  set C₀ : ℝ := Real.sqrt (max CD 0) with hC₀def
  have hC₀ : 0 ≤ C₀ := Real.sqrt_nonneg _
  have hC₀sq : CD ≤ C₀ ^ (2 : ℕ) := by
    rw [hC₀def, Real.sq_sqrt (le_max_right CD 0)]
    exact le_max_left CD 0
  refine ⟨Real.exp (Real.pi * C₀ ^ (2 : ℕ)), 0, (Real.exp_nonneg _), le_refl 0, fun k x hx => ?_⟩
  have hxsup : (H x x).re ≤ C₀ ^ (2 : ℕ) := by
    refine le_trans (le_trans (le_abs_self _) ?_) hC₀sq
    simpa using hCD x hx
  have hbase := norm_inv_appellHumbertAutomorphicFactor_le hH hpos hχ hsemi hC₀ hxsup
    (standardIntegerLatticeEquiv d k)
  refine le_trans hbase ?_
  rw [zero_mul, Real.exp_zero, mul_one]
  refine mul_le_of_le_one_right (Real.exp_nonneg _) ?_
  refine Real.exp_le_one_iff.mpr ?_
  have hγ := hpos (standardIntegerLatticeEquiv d k).1
  nlinarith [Real.pi_pos]

end

end GaloisForLFunctions.HTGeometry
