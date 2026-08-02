import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Derived polarization law

An alternating cup form and an odd conjugate-linear polarization turn a
weight derivation into a Hermitian conservation law.  Its entire defect is
the cup pairing against the commutator of the generator with the
polarization.  For a nondegenerate cup form, conservation is therefore
equivalent to commutation.

This is the algebraic carrier needed before any completion or invariant
scalarization: a mixed degree-two class is polarized first and only then
read as a positive metric.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Sesquilinear metric obtained by following a bilinear cup form with a
conjugate-linear polarization in its second variable. -/
def cupHodgeMetric
    (cup : LinearMap.BilinForm ℂ V)
    (J : V →ₛₗ[starRingEnd ℂ] V)
    (x y : V) : ℂ :=
  cup x (J y)

/-- Commutator of a linear generator with a conjugate-linear polarization. -/
def cupHodgeCommutator
    (theta : V →ₗ[ℂ] V)
    (J : V →ₛₗ[starRingEnd ℂ] V)
    (y : V) : V :=
  theta (J y) - J (theta y)

/--
**Derived polarization defect identity.**  If `theta` is a weight-`w`
derivation of the cup form, the failure of its cup--Hodge metric to satisfy
the same weight law is exactly the negative cup pairing against `[theta,J]`.
-/
theorem cupHodgeMetric_purityDefect
    (cup : LinearMap.BilinForm ℂ V)
    (theta : V →ₗ[ℂ] V)
    (J : V →ₛₗ[starRingEnd ℂ] V)
    (w : ℂ)
    (hderivation : ∀ x z,
      cup (theta x) z + cup x (theta z) = w * cup x z)
    (x y : V) :
    cupHodgeMetric cup J (theta x) y +
          cupHodgeMetric cup J x (theta y) -
        w * cupHodgeMetric cup J x y =
      -cup x (cupHodgeCommutator theta J y) := by
  have h := hderivation x (J y)
  simp only [cupHodgeMetric, cupHodgeCommutator, map_sub, neg_sub]
  linear_combination h

/--
**Nondegenerate conservation law.**  For a nondegenerate cup form, exact
weight conservation of the polarized metric is equivalent to commutation of
the generator with the polarization.
-/
theorem cupHodgeMetric_weightLaw_iff_commutes
    (cup : LinearMap.BilinForm ℂ V)
    (theta : V →ₗ[ℂ] V)
    (J : V →ₛₗ[starRingEnd ℂ] V)
    (w : ℂ)
    (hderivation : ∀ x z,
      cup (theta x) z + cup x (theta z) = w * cup x z)
    (hnondegenerate : cup.Nondegenerate) :
    (∀ x y,
      cupHodgeMetric cup J (theta x) y +
          cupHodgeMetric cup J x (theta y) =
        w * cupHodgeMetric cup J x y) ↔
      ∀ y, theta (J y) = J (theta y) := by
  constructor
  · intro hmetric y
    apply sub_eq_zero.mp
    apply hnondegenerate.2
    intro x
    have hdefect :=
      cupHodgeMetric_purityDefect cup theta J w hderivation x y
    rw [hmetric x y] at hdefect
    simp only [sub_self] at hdefect
    exact neg_eq_zero.mp hdefect.symm
  · intro hcomm x y
    have hdefect :=
      cupHodgeMetric_purityDefect cup theta J w hderivation x y
    rw [cupHodgeCommutator, hcomm y, sub_self, map_zero, neg_zero] at hdefect
    exact sub_eq_zero.mp hdefect

end

end GaloisForLFunctions.HTGeometry
