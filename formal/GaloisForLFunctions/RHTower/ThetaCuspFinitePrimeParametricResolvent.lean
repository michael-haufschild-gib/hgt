import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeResolvent

/-!
# Positive-parameter finite-prime theta resolvents

The pointed theta-cusp source uses the finite Euler product
`∏_{p ≤ N} (I - p^{-σ} U_p⁻¹)⁻¹` on the positive half-plane.  This file begins
the missing parameter layer with its literal local factors.  Positivity of `σ`
makes every factor a strict norm contraction away from the unit circle, so its
inverse is a closed bounded operator without a source-side hypothesis.
-/

noncomputable section

namespace RHTower

/-- The physical local Euler factor at arbitrary positive real parameter `σ`. -/
def finitePrimeEvenLocalFactorTermAt (sigma : ℝ) (N : ℕ)
    (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    evenSubspace →L[ℂ] evenSubspace :=
  1 - (Real.exp (-sigma * Real.log (p : ℝ)) : ℂ) •
    ((evenDilationUnitary (p : ℝ) (by
      exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
        evenSubspace →L[ℂ] evenSubspace)

/-- Every positive-parameter local Euler factor is invertible. -/
theorem finitePrimeEvenLocalFactorTermAt_isUnit
    {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ)
    (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    IsUnit (finitePrimeEvenLocalFactorTermAt sigma N p) := by
  rw [finitePrimeEvenLocalFactorTermAt]
  refine isUnit_one_sub_of_norm_lt_one (x :=
    (Real.exp (-sigma * Real.log (p : ℝ)) : ℂ) •
      ((evenDilationUnitary (p : ℝ) (by
        exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
          evenSubspace →L[ℂ] evenSubspace)) ?_
  have hp : 1 < (p : ℝ) := by
    exact_mod_cast (Nat.mem_primesLE.mp p.property).2.one_lt
  have hcoeff : ‖(Real.exp (-sigma * Real.log (p : ℝ)) : ℂ)‖ < 1 := by
    norm_cast
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    nlinarith [Real.log_pos hp]
  calc
    ‖(Real.exp (-sigma * Real.log (p : ℝ)) : ℂ) •
        ((evenDilationUnitary (p : ℝ) (by
          exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
            evenSubspace →L[ℂ] evenSubspace)‖ ≤
      ‖(Real.exp (-sigma * Real.log (p : ℝ)) : ℂ)‖ *
        ‖((evenDilationUnitary (p : ℝ) (by
          exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
            evenSubspace →L[ℂ] evenSubspace)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖(Real.exp (-sigma * Real.log (p : ℝ)) : ℂ)‖ * 1 := by
      gcongr
      exact (evenDilationUnitary (p : ℝ) (by
        exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm.toLinearIsometry.norm_toContinuousLinearMap_le
    _ < 1 := by simpa using hcoeff

end RHTower
