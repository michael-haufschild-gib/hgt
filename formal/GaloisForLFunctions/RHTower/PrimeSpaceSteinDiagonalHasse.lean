/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.RHTower.PrimeSpaceInertiaSteinLaw

/-!
# Diagonal Hasse reconstruction for prime-space Stein kernels

The diagonal of the prime-space Stein response kernel is a complete local coordinate system for
the global response.  Positive carrier mass makes the diagonal transform a linear equivalence,
with an explicit inverse.  Hence equality or vanishing of a global response is detected at every
one-prime diagonal entry; off-diagonal kernel values contain no additional response data.
-/

namespace RHTower

noncomputable section

/-- Linear response-to-Stein-kernel transform. -/
def primeSpaceSteinResponseKernelLinearMap :
    (Nat.Primes → ℝ) →ₗ[ℝ] (Nat.Primes → Nat.Primes → ℝ) where
  toFun := primeSpaceSteinResponseKernel
  map_add' x y := by
    funext p r
    exact primeSpaceSteinResponseKernel_add x y p r
  map_smul' c x := by
    funext p r
    simp [primeSpaceSteinResponseKernel]
    ring

/-- The linear response-to-kernel transform is faithful. -/
theorem primeSpaceSteinResponseKernelLinearMap_injective :
    Function.Injective primeSpaceSteinResponseKernelLinearMap :=
  primeSpaceSteinResponseKernel_injective

/-- Explicit local reconstruction: divide a diagonal kernel value by twice its positive carrier
mass. -/
theorem primeSpaceSteinResponse_recover_diagonal
    (response : Nat.Primes → ℝ) (p : Nat.Primes) :
    response p = primeSpaceSteinResponseKernel response p p /
      (2 * xiMobiusPrimeSchurDifferenceKernel p p) := by
  have hp := xiMobiusPrimeSchurDifferenceKernel_self_pos p
  simp only [primeSpaceSteinResponseKernel]
  field_simp [ne_of_gt hp]
  ring

/-- Diagonal Stein-kernel entries are linearly equivalent to arbitrary global prime responses. -/
noncomputable def primeSpaceSteinResponseDiagonalLinearEquiv :
    (Nat.Primes → ℝ) ≃ₗ[ℝ] (Nat.Primes → ℝ) where
  toFun response p := primeSpaceSteinResponseKernel response p p
  invFun diagonal p := diagonal p / (2 * xiMobiusPrimeSchurDifferenceKernel p p)
  left_inv response := by
    funext p
    exact (primeSpaceSteinResponse_recover_diagonal response p).symm
  right_inv diagonal := by
    funext p
    have hp := xiMobiusPrimeSchurDifferenceKernel_self_pos p
    simp only [primeSpaceSteinResponseKernel]
    field_simp [ne_of_gt hp]
    ring
  map_add' x y := by
    funext p
    exact primeSpaceSteinResponseKernel_add x y p p
  map_smul' c x := by
    funext p
    simp [primeSpaceSteinResponseKernel]
    ring

/-- Forward evaluation of the diagonal Hasse equivalence. -/
@[simp] theorem primeSpaceSteinResponseDiagonalLinearEquiv_apply
    (response : Nat.Primes → ℝ) (p : Nat.Primes) :
    primeSpaceSteinResponseDiagonalLinearEquiv response p =
      primeSpaceSteinResponseKernel response p p := rfl

/-- Inverse evaluation of the diagonal Hasse equivalence. -/
@[simp] theorem primeSpaceSteinResponseDiagonalLinearEquiv_symm_apply
    (diagonal : Nat.Primes → ℝ) (p : Nat.Primes) :
    primeSpaceSteinResponseDiagonalLinearEquiv.symm diagonal p =
      diagonal p / (2 * xiMobiusPrimeSchurDifferenceKernel p p) := rfl

/-- Global responses are linearly equivalent to the full Stein kernels they realize. -/
noncomputable def primeSpaceSteinResponseKernelHasseEquivRange :
    (Nat.Primes → ℝ) ≃ₗ[ℝ]
      LinearMap.range primeSpaceSteinResponseKernelLinearMap :=
  LinearEquiv.ofInjective primeSpaceSteinResponseKernelLinearMap
    primeSpaceSteinResponseKernelLinearMap_injective

/-- The realized-kernel equivalence evaluates by the Stein response kernel. -/
@[simp] theorem primeSpaceSteinResponseKernelHasseEquivRange_apply
    (response : Nat.Primes → ℝ) :
    (primeSpaceSteinResponseKernelHasseEquivRange response).1 =
      primeSpaceSteinResponseKernel response := rfl

/-- Two global prime responses agree exactly when every one-prime diagonal kernel coordinate
agrees. -/
theorem primeSpaceSteinResponse_congr_diagonal_hasse_iff
    (response₁ response₂ : Nat.Primes → ℝ) :
    response₁ = response₂ ↔
      ∀ p, primeSpaceSteinResponseKernel response₁ p p =
        primeSpaceSteinResponseKernel response₂ p p := by
  constructor
  · intro h
    subst response₂
    exact fun _ => rfl
  · intro h
    funext p
    have hp := h p
    simp only [primeSpaceSteinResponseKernel] at hp
    nlinarith [xiMobiusPrimeSchurDifferenceKernel_self_pos p]

/-- Equality of full prime-space kernels is equivalent to equality only on their diagonals. -/
theorem primeSpaceSteinResponseKernel_congr_diagonal_hasse_iff
    (response₁ response₂ : Nat.Primes → ℝ) :
    primeSpaceSteinResponseKernel response₁ = primeSpaceSteinResponseKernel response₂ ↔
      ∀ p, primeSpaceSteinResponseKernel response₁ p p =
        primeSpaceSteinResponseKernel response₂ p p := by
  constructor
  · intro h p
    exact congrArg (fun K => K p p) h
  · intro h
    rw [(primeSpaceSteinResponse_congr_diagonal_hasse_iff response₁ response₂).2 h]

/-- A global prime response vanishes exactly when every one-prime diagonal kernel entry
vanishes. -/
theorem primeSpaceSteinResponse_eq_zero_diagonal_hasse_iff
    (response : Nat.Primes → ℝ) :
    response = 0 ↔ ∀ p, primeSpaceSteinResponseKernel response p p = 0 := by
  rw [primeSpaceSteinResponse_congr_diagonal_hasse_iff response 0]
  simp [primeSpaceSteinResponseKernel]

end

end RHTower
