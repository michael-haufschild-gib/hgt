import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Navier--Stokes disjoint covariance assembly

Generic algebraic core of Proposition 7.5: when distinct wave packets have zero cross covariance,
the covariance of their amplitude-weighted sum is the sum of individual covariances weighted by
amplitude squares.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesDisjointCovariance

open Finset
open scoped BigOperators

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Diagonal quadratic map associated to a bilinear covariance map. -/
def quadraticCovariance (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (x : V) : W :=
  B x x

/-- Polarization expansion for a sum of two packets. -/
theorem quadraticCovariance_add (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (x y : V) :
    quadraticCovariance B (x + y) =
      quadraticCovariance B x + quadraticCovariance B y + B x y + B y x := by
  simp [quadraticCovariance]
  module

/-- Vanishing cross covariances make covariance additive. -/
theorem quadraticCovariance_add_of_cross_eq_zero
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) {x y : V}
    (hxy : B x y = 0) (hyx : B y x = 0) :
    quadraticCovariance B (x + y) = quadraticCovariance B x + quadraticCovariance B y := by
  rw [quadraticCovariance_add, hxy, hyx]
  simp

/-- Two disjoint packets contribute their squared amplitudes and no mixed term. -/
theorem quadraticCovariance_two_amplitudes
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) {x y : V}
    (hxy : B x y = 0) (hyx : B y x = 0) (a b : ℝ) :
    quadraticCovariance B (a • x + b • y) =
      a ^ 2 • quadraticCovariance B x + b ^ 2 • quadraticCovariance B y := by
  simp [quadraticCovariance, hxy, hyx, smul_smul, pow_two]

/--
Finite disjoint-packet covariance formula.  This is the exact algebra behind
`C(∑ aᵢbᵢ) = ∑ aᵢ² C(bᵢ)` in Proposition 7.5.
-/
theorem quadraticCovariance_sum_of_pairwise_cross_eq_zero
    {ι : Type*} (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (S : Finset ι)
    (a : ι → ℝ) (x : ι → V)
    (hcross : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → B (x i) (x j) = 0) :
    quadraticCovariance B (∑ i ∈ S, a i • x i) =
      ∑ i ∈ S, a i ^ 2 • quadraticCovariance B (x i) := by
  classical
  unfold quadraticCovariance
  rw [map_sum]
  simp_rw [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp [pow_two, smul_smul]
  · intro j hj hji
    rw [hcross i hi j hj (Ne.symm hji)]
    simp
  · exact fun h => (h hi).elim

end GaloisForLFunctions.HTGeometry.NavierStokesDisjointCovariance
