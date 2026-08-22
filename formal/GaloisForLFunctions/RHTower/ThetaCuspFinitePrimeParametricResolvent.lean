import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeResolvent
import Mathlib.Analysis.Normed.MulAction

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

/-- The physical operator norm is compatible with complex scalar multiplication. -/
private instance : IsBoundedSMul ℂ (evenSubspace →L[ℂ] evenSubspace) :=
  IsBoundedSMul.of_norm_smul_le fun (c : ℂ) (T : evenSubspace →L[ℂ] evenSubspace) =>
    ContinuousLinearMap.opNorm_smul_le c T

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

/-- The complex Euler factor at a finite prime. -/
def finitePrimeEvenLocalFactorTermAtC (s : ℂ) (N : ℕ)
    (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    evenSubspace →L[ℂ] evenSubspace :=
  1 - Complex.exp (-s * (Real.log (p : ℝ) : ℝ)) •
    ((evenDilationUnitary (p : ℝ) (by
      exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
        evenSubspace →L[ℂ] evenSubspace)

/-- Every complex local Euler factor is invertible on the open right half-plane. -/
theorem finitePrimeEvenLocalFactorTermAtC_isUnit
    {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    IsUnit (finitePrimeEvenLocalFactorTermAtC s N p) := by
  rw [finitePrimeEvenLocalFactorTermAtC]
  refine isUnit_one_sub_of_norm_lt_one (x :=
    Complex.exp (-s * (Real.log (p : ℝ) : ℝ)) •
      ((evenDilationUnitary (p : ℝ) (by
        exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
          evenSubspace →L[ℂ] evenSubspace)) ?_
  have hp : 1 < (p : ℝ) := by
    exact_mod_cast (Nat.mem_primesLE.mp p.property).2.one_lt
  have hcoeff : ‖Complex.exp (-s * (Real.log (p : ℝ) : ℝ))‖ < 1 := by
    rw [Complex.norm_exp]
    have hre : (-s * (Real.log (p : ℝ) : ℝ)).re = -s.re * Real.log (p : ℝ) := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    rw [hre]
    apply Real.exp_lt_one_iff.mpr
    nlinarith [Real.log_pos hp]
  calc
    ‖Complex.exp (-s * (Real.log (p : ℝ) : ℝ)) •
        ((evenDilationUnitary (p : ℝ) (by
          exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
            evenSubspace →L[ℂ] evenSubspace)‖ ≤
      ‖Complex.exp (-s * (Real.log (p : ℝ) : ℝ))‖ *
        ‖((evenDilationUnitary (p : ℝ) (by
          exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
            evenSubspace →L[ℂ] evenSubspace)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖Complex.exp (-s * (Real.log (p : ℝ) : ℝ))‖ * 1 := by
      gcongr
      exact (evenDilationUnitary (p : ℝ) (by
        exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm.toLinearIsometry.norm_toContinuousLinearMap_le
    _ < 1 := by simpa using hcoeff

/-- Exact complex derivative of one finite-prime Euler factor. -/
theorem hasDerivAt_finitePrimeEvenLocalFactorTermAtC
    (s : ℂ) (N : ℕ) (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    HasDerivAt (fun z : ℂ => finitePrimeEvenLocalFactorTermAtC z N p)
      (((Real.log (p : ℝ) : ℂ) * Complex.exp (-s * (Real.log (p : ℝ) : ℝ))) •
        ((evenDilationUnitary (p : ℝ) (by
          exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
            evenSubspace →L[ℂ] evenSubspace)) s := by
  have hinner : HasDerivAt (fun z : ℂ => -z * (Real.log (p : ℝ) : ℝ))
      (-(Real.log (p : ℝ) : ℂ)) s := by
    simpa [id] using ((hasDerivAt_id s).neg.mul_const (Real.log (p : ℝ) : ℂ))
  have hcoeff := (Complex.hasDerivAt_exp (-s * (Real.log (p : ℝ) : ℝ))).comp s hinner
  unfold finitePrimeEvenLocalFactorTermAtC
  apply ((hasDerivAt_const s (1 : evenSubspace →L[ℂ] evenSubspace)).sub
    (hcoeff.smul_const
      ((evenDilationUnitary (p : ℝ) (by
        exact_mod_cast (Nat.mem_primesLE.mp p.property).2.pos)).symm :
          evenSubspace →L[ℂ] evenSubspace))).congr_deriv
  module

/-- Ordered finite product of the complex local Euler factors. -/
def finitePrimeEvenLocalFactorAtC (s : ℂ) (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  ((Nat.primesLE N).attach.toList.map
    (finitePrimeEvenLocalFactorTermAtC s N)).prod

/-- The complete complex finite-prime factor is invertible on the open right half-plane. -/
theorem finitePrimeEvenLocalFactorAtC_isUnit
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    IsUnit (finitePrimeEvenLocalFactorAtC s N) := by
  unfold finitePrimeEvenLocalFactorAtC
  apply List.prod_isUnit
  intro T hT
  rw [List.mem_map] at hT
  obtain ⟨p, hp, rfl⟩ := hT
  exact finitePrimeEvenLocalFactorTermAtC_isUnit hs N p

/-- Bounded complex finite-prime resolvent on the open right half-plane. -/
noncomputable def finitePrimeEvenResolventAtC
    (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  ↑((finitePrimeEvenLocalFactorAtC_isUnit hs N).unit⁻¹)

/-- The complex Euler factor times its resolvent is the identity. -/
theorem finitePrimeEvenLocalFactorAtC_mul_resolvent
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    finitePrimeEvenLocalFactorAtC s N *
      finitePrimeEvenResolventAtC s hs N = 1 := by
  let u := (finitePrimeEvenLocalFactorAtC_isUnit hs N).unit
  change (u : evenSubspace →L[ℂ] evenSubspace) *
      (↑(u⁻¹) : evenSubspace →L[ℂ] evenSubspace) = 1
  exact Units.mul_inv u

/-- The complex resolvent times its Euler factor is the identity. -/
theorem finitePrimeEvenResolventAtC_mul_localFactor
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    finitePrimeEvenResolventAtC s hs N *
      finitePrimeEvenLocalFactorAtC s N = 1 := by
  let u := (finitePrimeEvenLocalFactorAtC_isUnit hs N).unit
  change (↑(u⁻¹) : evenSubspace →L[ℂ] evenSubspace) *
      (u : evenSubspace →L[ℂ] evenSubspace) = 1
  exact Units.inv_mul u

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

/-- Restriction of a complex local Euler factor to the real parameter line. -/
theorem finitePrimeEvenLocalFactorTermAtC_ofReal (sigma : ℝ) (N : ℕ)
    (p : {p : ℕ // p ∈ Nat.primesLE N}) :
    finitePrimeEvenLocalFactorTermAtC (sigma : ℂ) N p =
      finitePrimeEvenLocalFactorTermAt sigma N p := by
  unfold finitePrimeEvenLocalFactorTermAtC finitePrimeEvenLocalFactorTermAt
  congr 2
  calc
    Complex.exp (-↑sigma * ↑(Real.log (p : ℝ))) =
        Complex.exp ((-sigma * Real.log (p : ℝ) : ℝ) : ℂ) := by
      congr 1
      push_cast
      ring
    _ = ↑(Real.exp (-sigma * Real.log (p : ℝ))) := (Complex.ofReal_exp _).symm

/-- Restriction of the complex finite-prime Euler factor to the real parameter line. -/
theorem finitePrimeEvenLocalFactorAtC_ofReal (sigma : ℝ) (N : ℕ) :
    finitePrimeEvenLocalFactorAtC (sigma : ℂ) N = finitePrimeEvenLocalFactorAt sigma N := by
  unfold finitePrimeEvenLocalFactorAtC finitePrimeEvenLocalFactorAt
  congr 1
  apply List.map_congr_left
  intro p hp
  exact finitePrimeEvenLocalFactorTermAtC_ofReal sigma N p

/-- On a positive real parameter, the complex and real resolvents agree exactly. -/
theorem finitePrimeEvenResolventAtC_ofReal
    {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    finitePrimeEvenResolventAtC (sigma : ℂ) (by simpa using hsigma) N =
      finitePrimeEvenResolventAt sigma hsigma N := by
  have hleft := finitePrimeEvenLocalFactorAtC_mul_resolvent
    (s := (sigma : ℂ)) (by simpa using hsigma) N
  rw [finitePrimeEvenLocalFactorAtC_ofReal] at hleft
  calc
    finitePrimeEvenResolventAtC (sigma : ℂ) (by simpa using hsigma) N =
        1 * finitePrimeEvenResolventAtC (sigma : ℂ) (by simpa using hsigma) N := by rw [one_mul]
    _ = (finitePrimeEvenResolventAt sigma hsigma N * finitePrimeEvenLocalFactorAt sigma N) *
        finitePrimeEvenResolventAtC (sigma : ℂ) (by simpa using hsigma) N := by
      rw [finitePrimeEvenResolventAt_mul_localFactor]
    _ = finitePrimeEvenResolventAt sigma hsigma N *
        (finitePrimeEvenLocalFactorAt sigma N *
          finitePrimeEvenResolventAtC (sigma : ℂ) (by simpa using hsigma) N) := by
      rw [mul_assoc]
    _ = finitePrimeEvenResolventAt sigma hsigma N * 1 := by rw [hleft]
    _ = finitePrimeEvenResolventAt sigma hsigma N := by rw [mul_one]

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
