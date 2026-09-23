import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
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

/-- Symmetric polarization of a bilinear covariance map. -/
def polarCovariance (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (x y : V) : W :=
  B x y + B y x

/-- Polarization expansion for a sum of two packets. -/
theorem quadraticCovariance_add (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (x y : V) :
    quadraticCovariance B (x + y) =
      quadraticCovariance B x + quadraticCovariance B y + B x y + B y x := by
  simp [quadraticCovariance]
  module

/-- Exact covariance increment under addition of one packet. -/
theorem quadraticCovariance_increment (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (x y : V) :
    quadraticCovariance B (x + y) - quadraticCovariance B x =
      polarCovariance B x y + quadraticCovariance B y := by
  rw [quadraticCovariance_add]
  simp [polarCovariance]
  module

theorem polarCovariance_add_left (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (x y z : V) :
    polarCovariance B (x + y) z =
      polarCovariance B x z + polarCovariance B y z := by
  simp [polarCovariance]
  module

theorem polarCovariance_add_right (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (x y z : V) :
    polarCovariance B x (y + z) =
      polarCovariance B x y + polarCovariance B x z := by
  simp [polarCovariance]
  module

/-- **Corollary 7.8, exact algebraic expansion.** If an old field is its primary part plus
an error and a new field is its leading part plus a curl remainder, the covariance increment
splits into the prescribed leading stress and exactly three retained remainders. -/
theorem quadraticCovariance_increment_split
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (U V₁ primary error leading remainder : V) (target : W)
    (hU : U = primary + error) (hV : V₁ = leading + remainder)
    (hleading : polarCovariance B primary leading = target) :
    quadraticCovariance B (U + V₁) - quadraticCovariance B U =
      target + polarCovariance B error leading +
        polarCovariance B U remainder + quadraticCovariance B V₁ := by
  calc
    quadraticCovariance B (U + V₁) - quadraticCovariance B U =
        polarCovariance B U V₁ + quadraticCovariance B V₁ :=
      quadraticCovariance_increment B U V₁
    _ = polarCovariance B U (leading + remainder) + quadraticCovariance B V₁ := by
      rw [hV]
    _ = polarCovariance B U leading + polarCovariance B U remainder +
        quadraticCovariance B V₁ := by
      rw [polarCovariance_add_right]
    _ = polarCovariance B (primary + error) leading + polarCovariance B U remainder +
        quadraticCovariance B V₁ := by
      rw [hU]
    _ = target + polarCovariance B error leading +
        polarCovariance B U remainder + quadraticCovariance B V₁ := by
      rw [polarCovariance_add_left, hleading]

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
      a ^ (2 : ℕ) • quadraticCovariance B x + b ^ (2 : ℕ) • quadraticCovariance B y := by
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
      ∑ i ∈ S, a i ^ (2 : ℕ) • quadraticCovariance B (x i) := by
  classical
  unfold quadraticCovariance
  rw [map_sum]
  simp_rw [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp [pow_two, smul_smul]
  · intro j hj hji
    simp [hcross j hj i hi hji]
  · exact fun h => (h hi).elim

/-- Pointwise-disjoint packets have no nonlinear cross interaction.  Applied at each spatial
point, this is the finite/local algebra used when Corollary 10.6 periodizes disjoint translates. -/
theorem quadraticCovariance_sum_of_pairwise_disjoint
    {ι X : Type*} (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (S : Finset ι)
    (a : ι → ℝ) (x : ι → X → V)
    (hdisjoint : ∀ p, ∀ i ∈ S, ∀ j ∈ S, i ≠ j → x i p = 0 ∨ x j p = 0) :
    ∀ p, quadraticCovariance B (∑ i ∈ S, a i • x i p) =
      ∑ i ∈ S, a i ^ (2 : ℕ) • quadraticCovariance B (x i p) := by
  intro p
  apply quadraticCovariance_sum_of_pairwise_cross_eq_zero B S a (fun i ↦ x i p)
  intro i hi j hj hij
  rcases hdisjoint p i hi j hj hij with hzero | hzero
  · simp [hzero]
  · simp [hzero]

end GaloisForLFunctions.HTGeometry.NavierStokesDisjointCovariance
