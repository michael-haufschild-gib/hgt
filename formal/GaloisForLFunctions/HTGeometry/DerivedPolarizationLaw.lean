import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Finite
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
variable {A B C : Type*}
variable [AddCommGroup A] [Module ℂ A]
variable [AddCommGroup B] [Module ℂ B]
variable [AddCommGroup C] [Module ℂ C]

/--
Alternating scalar cup forced by a mixed bilinear source product and a
degree-two trace.  The two degree-one source legs are not scalarized
separately: multiplication precedes the trace.
-/
def tracedMixedSourceCup
    (cross : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (trace : C →ₗ[ℂ] ℂ) :
    LinearMap.BilinForm ℂ (A × B) where
  toFun x :=
    { toFun := fun y =>
        trace (cross x.1 y.2 - cross y.1 x.2)
      map_add' := by
        intro y z
        change
          trace
              (cross x.1 (y.2 + z.2) -
                cross (y.1 + z.1) x.2) =
            trace (cross x.1 y.2 - cross y.1 x.2) +
              trace (cross x.1 z.2 - cross z.1 x.2)
        simp only [map_add, LinearMap.add_apply, map_sub]
        abel
      map_smul' := by
        intro c y
        change
          trace
              (cross x.1 (c • y.2) -
                cross (c • y.1) x.2) =
            c • trace (cross x.1 y.2 - cross y.1 x.2)
        simp only [map_smul, LinearMap.smul_apply]
        rw [← smul_sub, map_smul] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change
      trace
          (cross (x.1 + y.1) z.2 -
            cross z.1 (x.2 + y.2)) =
        trace (cross x.1 z.2 - cross z.1 x.2) +
          trace (cross y.1 z.2 - cross z.1 y.2)
    simp only [map_add, LinearMap.add_apply, map_sub]
    abel
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    change
      trace
          (cross (c • x.1) y.2 -
            cross y.1 (c • x.2)) =
        c • trace (cross x.1 y.2 - cross y.1 x.2)
    simp only [map_smul, LinearMap.smul_apply]
    rw [← smul_sub, map_smul]

@[simp]
theorem tracedMixedSourceCup_apply
    (cross : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (trace : C →ₗ[ℂ] ℂ)
    (x y : A × B) :
    tracedMixedSourceCup cross trace x y =
      trace (cross x.1 y.2 - cross y.1 x.2) :=
  rfl

/--
If the traced cross-effect separates each source leg, its alternating
polarization is automatically a nondegenerate cup form.
-/
theorem tracedMixedSourceCup_nondegenerate
    (cross : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (trace : C →ₗ[ℂ] ℂ)
    (hleft : ∀ a, (∀ b, trace (cross a b) = 0) → a = 0)
    (hright : ∀ b, (∀ a, trace (cross a b) = 0) → b = 0) :
    (tracedMixedSourceCup cross trace).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply hleft
      intro b
      have h := hx (0, b)
      simpa using h
    · apply hright
      intro a
      have h := hx (a, 0)
      have hzero : -trace (cross a x.2) = 0 := by
        simpa using h
      exact neg_eq_zero.mp hzero
  · intro y hy
    apply Prod.ext
    · apply hleft
      intro b
      have h := hy (0, b)
      have hzero : -trace (cross y.1 b) = 0 := by
        simpa using h
      exact neg_eq_zero.mp hzero
    · apply hright
      intro a
      have h := hy (a, 0)
      simpa using h

/--
**Two-sided trace classification.**  The scalar cup obtained from a mixed
source product is nondegenerate if and only if its degree-two trace separates
both degree-one source legs.  Thus no later polarization can repair a trace
that erases either leg.
-/
theorem tracedMixedSourceCup_nondegenerate_iff
    (cross : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (trace : C →ₗ[ℂ] ℂ) :
    (tracedMixedSourceCup cross trace).Nondegenerate ↔
      (∀ a, (∀ b, trace (cross a b) = 0) → a = 0) ∧
      (∀ b, (∀ a, trace (cross a b) = 0) → b = 0) := by
  constructor
  · intro hnondegenerate
    constructor
    · intro a ha
      have hpair :
          ∀ y : A × B,
            tracedMixedSourceCup cross trace (a, 0) y = 0 := by
        intro y
        simpa using ha y.2
      have hzero := hnondegenerate.1 (a, 0) hpair
      exact congrArg Prod.fst hzero
    · intro b hb
      have hpair :
          ∀ x : A × B,
            tracedMixedSourceCup cross trace x (0, b) = 0 := by
        intro x
        simpa using hb x.1
      have hzero := hnondegenerate.2 (0, b) hpair
      exact congrArg Prod.snd hzero
  · rintro ⟨hleft, hright⟩
    exact tracedMixedSourceCup_nondegenerate
      cross trace hleft hright

/--
**Scalar-trace rank fracture.**  If the left source leg is one-dimensional
and the right leg contains two independent directions, no single scalar
degree-two trace can make the induced cup nondegenerate.  A faithful
polarization must retain a family-valued trace or additional grading.
-/
theorem no_scalar_tracedMixedSourceCup_of_oneDimensional_left
    (cross : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (trace : C →ₗ[ℂ] ℂ)
    (a0 : A)
    (hspan : ∀ a : A, ∃ c : ℂ, a = c • a0)
    (packet : Fin 2 → B)
    (hpacket : LinearIndependent ℂ packet) :
    ¬(tracedMixedSourceCup cross trace).Nondegenerate := by
  intro hnondegenerate
  have hseparates :=
    (tracedMixedSourceCup_nondegenerate_iff cross trace).mp
      hnondegenerate
  let phi : B →ₗ[ℂ] ℂ := trace.comp (cross a0)
  have hphi_zero : ∀ b : B, phi b = 0 → b = 0 := by
    intro b hb
    apply hseparates.2 b
    intro a
    obtain ⟨c, rfl⟩ := hspan a
    simp only [map_smul, LinearMap.smul_apply]
    change c • phi b = 0
    rw [hb, smul_zero]
  have hphi : Function.Injective phi := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hphi_zero (x - y)
    rw [map_sub, sub_eq_zero.mpr hxy]
  have hlinear : LinearIndependent ℂ (fun i => phi (packet i)) :=
    hpacket.map' phi (LinearMap.ker_eq_bot.mpr hphi)
  have hcard := hlinear.fintype_card_le_finrank
  norm_num [Module.finrank_self] at hcard

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

/--
**Mixed-source derived polarization law.**  A bilinear source product whose
degree-two trace separates both source legs forces a nondegenerate alternating
cup.  Consequently, for every cup derivation, exact conservation of the
polarized metric is equivalent to commutation with the polarization.
-/
theorem tracedMixedSourceCup_weightLaw_iff_commutes
    (cross : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (trace : C →ₗ[ℂ] ℂ)
    (theta : (A × B) →ₗ[ℂ] (A × B))
    (J : (A × B) →ₛₗ[starRingEnd ℂ] (A × B))
    (w : ℂ)
    (hleft : ∀ a, (∀ b, trace (cross a b) = 0) → a = 0)
    (hright : ∀ b, (∀ a, trace (cross a b) = 0) → b = 0)
    (hderivation : ∀ x z,
      tracedMixedSourceCup cross trace (theta x) z +
          tracedMixedSourceCup cross trace x (theta z) =
        w * tracedMixedSourceCup cross trace x z) :
    (∀ x y,
      cupHodgeMetric (tracedMixedSourceCup cross trace) J (theta x) y +
          cupHodgeMetric (tracedMixedSourceCup cross trace) J
            x (theta y) =
        w * cupHodgeMetric (tracedMixedSourceCup cross trace) J x y) ↔
      ∀ y, theta (J y) = J (theta y) :=
  cupHodgeMetric_weightLaw_iff_commutes
    (tracedMixedSourceCup cross trace) theta J w hderivation
    (tracedMixedSourceCup_nondegenerate cross trace hleft hright)

end

end GaloisForLFunctions.HTGeometry
