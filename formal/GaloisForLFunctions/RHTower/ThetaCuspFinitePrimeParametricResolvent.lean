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

/-- Ordered finite product of the local Euler factors at parameter `σ`. -/
def finitePrimeEvenLocalFactorAt (sigma : ℝ) (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  ((Nat.primesLE N).attach.toList.map
    (finitePrimeEvenLocalFactorTermAt sigma N)).prod

/-- The complete finite-prime Euler factor is invertible for every `σ > 0`. -/
theorem finitePrimeEvenLocalFactorAt_isUnit
    {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    IsUnit (finitePrimeEvenLocalFactorAt sigma N) := by
  unfold finitePrimeEvenLocalFactorAt
  apply List.prod_isUnit
  intro T hT
  rw [List.mem_map] at hT
  obtain ⟨p, hp, rfl⟩ := hT
  exact finitePrimeEvenLocalFactorTermAt_isUnit hsigma N p

/-- Bounded finite-prime resolvent on the full positive real parameter range. -/
noncomputable def finitePrimeEvenResolventAt
    (sigma : ℝ) (hsigma : 0 < sigma) (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  ↑((finitePrimeEvenLocalFactorAt_isUnit hsigma N).unit⁻¹)

theorem finitePrimeEvenLocalFactorAt_mul_resolvent
    {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    finitePrimeEvenLocalFactorAt sigma N *
      finitePrimeEvenResolventAt sigma hsigma N = 1 := by
  let u := (finitePrimeEvenLocalFactorAt_isUnit hsigma N).unit
  change (u : evenSubspace →L[ℂ] evenSubspace) *
      (↑(u⁻¹) : evenSubspace →L[ℂ] evenSubspace) = 1
  exact Units.mul_inv u

theorem finitePrimeEvenResolventAt_mul_localFactor
    {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    finitePrimeEvenResolventAt sigma hsigma N *
      finitePrimeEvenLocalFactorAt sigma N = 1 := by
  let u := (finitePrimeEvenLocalFactorAt_isUnit hsigma N).unit
  change (↑(u⁻¹) : evenSubspace →L[ℂ] evenSubspace) *
      (u : evenSubspace →L[ℂ] evenSubspace) = 1
  exact Units.inv_mul u

/-- The parameter family specializes definitionally to the existing critical Euler factors. -/
theorem finitePrimeEvenLocalFactorTermAt_half (N : ℕ)
    (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    finitePrimeEvenLocalFactorTermAt (1 / 2) N p =
      finitePrimeEvenLocalFactorTerm N p := by
  unfold finitePrimeEvenLocalFactorTermAt finitePrimeEvenLocalFactorTerm
  congr 2
  have hp : 0 < (p : ℝ) := by
    exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos
  norm_cast
  rw [show -(1 / 2 : ℝ) * Real.log (p : ℝ) =
      -(Real.log (p : ℝ) / 2) by ring,
    ← Real.log_sqrt hp.le, Real.exp_neg,
    Real.exp_log (Real.sqrt_pos.2 hp)]

/-- At `σ = 1/2`, the parameter family is the established critical finite-prime factor. -/
theorem finitePrimeEvenLocalFactorAt_half (N : ℕ) :
    finitePrimeEvenLocalFactorAt (1 / 2) N = finitePrimeEvenLocalFactor N := by
  unfold finitePrimeEvenLocalFactorAt finitePrimeEvenLocalFactor
  congr 1
  apply List.map_congr_left
  intro p hp
  exact finitePrimeEvenLocalFactorTermAt_half N p

/-- The parameter resolvent at `σ = 1/2` is the existing critical resolvent. -/
theorem finitePrimeEvenResolventAt_half (N : ℕ) :
    finitePrimeEvenResolventAt (1 / 2) (by norm_num) N =
      finitePrimeEvenResolvent N := by
  have hleft := finitePrimeEvenLocalFactorAt_mul_resolvent (sigma := (1 / 2 : ℝ))
    (by norm_num) N
  rw [finitePrimeEvenLocalFactorAt_half] at hleft
  calc
    finitePrimeEvenResolventAt (1 / 2) (by norm_num) N =
        1 * finitePrimeEvenResolventAt (1 / 2) (by norm_num) N := by rw [one_mul]
    _ = (finitePrimeEvenResolvent N * finitePrimeEvenLocalFactor N) *
        finitePrimeEvenResolventAt (1 / 2) (by norm_num) N := by
      rw [finitePrimeEvenResolvent_mul_localFactor]
    _ = finitePrimeEvenResolvent N *
        (finitePrimeEvenLocalFactor N *
          finitePrimeEvenResolventAt (1 / 2) (by norm_num) N) := by
      rw [mul_assoc]
    _ = finitePrimeEvenResolvent N * 1 := by rw [hleft]
    _ = finitePrimeEvenResolvent N := by rw [mul_one]

end RHTower
