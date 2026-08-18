import GaloisForLFunctions.HTGeometry.AffineLineEtaleLocallyNilpotent
import GaloisForLFunctions.HTGeometry.EtaleModuleDerivation
import GaloisForLFunctions.HTGeometry.AlgebraDiscriminantBaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Local nilpotence of the lift over an arbitrary characteristic-zero domain

`AffineLineEtaleLocallyNilpotent` proves that the lift of `d/dX` to a finite étale algebra over
`E[X]` is locally nilpotent when `E` is algebraically closed.  The same holds over `R[X]` for any
characteristic-zero domain `R`:

```text
locallyNilpotent_liftDerivation_domain :
    ∃ N, (liftDerivation e hd (polyDeriv R))^[N] b = 0
```

Base change along `R[X] → E[X]`, with `E` an algebraic closure of the fraction field of `R`, makes
the algebra `E[X] ⊗[R[X]] B`, again finite free with unit discriminant
(`AlgebraDiscriminantBaseChange`), so its lift is locally nilpotent.  The two derivations are
compared without constructing any derivation on the tensor product: `b ↦ ∂̄ (1 ⊗ b)` and
`b ↦ 1 ⊗ ∂ b` are two derivations `B → E[X] ⊗ B` agreeing on the image of `R[X]`, hence equal by the
module-valued uniqueness of `EtaleModuleDerivation`.  Nilpotency then descends because `b ↦ 1 ⊗ b`
is injective — its coordinates in the base-changed basis are the images of the coordinates of `b`.
-/


namespace GaloisForLFunctions.HTGeometry

open Polynomial Lift
open scoped TensorProduct

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

universe u

/-- **The lift of `d/dX` to a finite étale algebra over `R[X]` is locally nilpotent**, for any
characteristic-zero domain `R`. -/
theorem locallyNilpotent_liftDerivation_domain {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    {B : Type u} [CommRing B] [Algebra R[X] B] [Algebra R B] [IsScalarTower R R[X] B]
    [Module.Free R[X] B] [Module.Finite R[X] B]
    {n : ℕ} (e : Module.Basis (Fin n) R[X] B) (hd : IsUnit (Algebra.discr R[X] e)) (b : B) :
    ∃ N : ℕ, (⇑(liftDerivation e hd (polyDeriv R)))^[N] b = 0 := by
  set F := FractionRing R with hF
  set E := AlgebraicClosure F with hE
  letI algRXEX : Algebra R[X] E[X] := (Polynomial.mapRingHom (algebraMap R E)).toAlgebra
  have hmapRX : ∀ p : R[X], algebraMap R[X] E[X] p = p.map (algebraMap R E) := fun _ => rfl
  haveI towerR : IsScalarTower R R[X] E[X] :=
    IsScalarTower.of_algebraMap_eq (fun r => by rw [hmapRX]; simp)
  have hdb0 := discr_baseChange R[X] E[X] B e
  have hdb : IsUnit (Algebra.discr E[X] (Module.Basis.baseChange E[X] e)) := by
    have h := hd.map (algebraMap R[X] E[X])
    rw [← hdb0] at h
    exact h
  letI algBBbar : Algebra B (E[X] ⊗[R[X]] B) :=
    RingHom.toAlgebra
      (Algebra.TensorProduct.includeRight : B →ₐ[R[X]] (E[X] ⊗[R[X]] B)).toRingHom
  haveI towerRXB : IsScalarTower R[X] B (E[X] ⊗[R[X]] B) :=
    IsScalarTower.of_algebraMap_eq (fun p => by
      show algebraMap R[X] (E[X] ⊗[R[X]] B) p
        = (Algebra.TensorProduct.includeRight : B →ₐ[R[X]] (E[X] ⊗[R[X]] B))
            (algebraMap R[X] B p)
      rw [AlgHom.commutes])
  set dB := liftDerivation e hd (polyDeriv R) with hdBdef
  set dBar := liftDerivation (Module.Basis.baseChange E[X] e) hdb (polyDeriv E) with hdBardef
  have hmulB : ∀ (x : B) (m : E[X] ⊗[R[X]] B), x • m = ((1 : E[X]) ⊗ₜ[R[X]] x) * m := by
    intro x m
    rw [Algebra.smul_def]
    rfl
  let f₁ : B →+ (E[X] ⊗[R[X]] B) :=
    AddMonoidHom.mk' (fun b => dBar ((1 : E[X]) ⊗ₜ[R[X]] b))
      (by intro x y; rw [TensorProduct.tmul_add, map_add])
  let f₂ : B →+ (E[X] ⊗[R[X]] B) :=
    AddMonoidHom.mk' (fun b => (1 : E[X]) ⊗ₜ[R[X]] (dB b))
      (by intro x y; rw [map_add, TensorProduct.tmul_add])
  let D₁ : Derivation ℤ B (E[X] ⊗[R[X]] B) :=
    { toLinearMap := f₁.toIntLinearMap
      map_one_eq_zero' := by
        show dBar ((1 : E[X]) ⊗ₜ[R[X]] (1 : B)) = 0
        rw [show ((1 : E[X]) ⊗ₜ[R[X]] (1 : B)) = 1 from rfl, Derivation.map_one_eq_zero]
      leibniz' := fun x y => by
        show dBar ((1 : E[X]) ⊗ₜ[R[X]] (x * y)) = x • dBar (1 ⊗ₜ y) + y • dBar (1 ⊗ₜ x)
        rw [show ((1 : E[X]) ⊗ₜ[R[X]] (x * y)) = ((1 : E[X]) ⊗ₜ[R[X]] x) * ((1 : E[X]) ⊗ₜ[R[X]] y)
            from by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
          Derivation.leibniz, hmulB, hmulB, smul_eq_mul, smul_eq_mul] }
  let D₂ : Derivation ℤ B (E[X] ⊗[R[X]] B) :=
    { toLinearMap := f₂.toIntLinearMap
      map_one_eq_zero' := by
        show (1 : E[X]) ⊗ₜ[R[X]] (dB 1) = 0
        rw [Derivation.map_one_eq_zero, TensorProduct.tmul_zero]
      leibniz' := fun x y => by
        show (1 : E[X]) ⊗ₜ[R[X]] (dB (x * y)) = x • (1 ⊗ₜ dB y) + y • (1 ⊗ₜ dB x)
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, TensorProduct.tmul_add, hmulB, hmulB,
          Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul] }
  have hagree : ∀ p : R[X], D₁ (algebraMap R[X] B p) = D₂ (algebraMap R[X] B p) := by
    intro p
    show dBar ((1 : E[X]) ⊗ₜ[R[X]] (algebraMap R[X] B p))
      = (1 : E[X]) ⊗ₜ[R[X]] (dB (algebraMap R[X] B p))
    have h1 : ∀ q : R[X], ((1 : E[X]) ⊗ₜ[R[X]] (algebraMap R[X] B q))
        = algebraMap E[X] (E[X] ⊗[R[X]] B) (algebraMap R[X] E[X] q) := by
      intro q
      rw [← IsScalarTower.algebraMap_apply R[X] E[X] (E[X] ⊗[R[X]] B)]
      exact (Algebra.TensorProduct.includeRight (R := R[X]) (A := E[X])).commutes q
    rw [h1 p, hdBardef, liftDerivation_algebraMap, hdBdef, liftDerivation_algebraMap, h1]
    congr 1
    show Polynomial.derivative (p.map (algebraMap R E)) = (Polynomial.derivative p).map _
    rw [Polynomial.derivative_map]
  have heq : D₁ = D₂ := derivation_module_ext e hd D₁ D₂ hagree
  have hstep : ∀ b : B, dBar ((1 : E[X]) ⊗ₜ[R[X]] b) = (1 : E[X]) ⊗ₜ[R[X]] (dB b) := by
    intro b
    exact congrArg (fun (F : Derivation ℤ B (E[X] ⊗[R[X]] B)) => F b) heq
  have hiter : ∀ (N : ℕ) (b : B),
      (⇑dBar)^[N] ((1 : E[X]) ⊗ₜ[R[X]] b) = (1 : E[X]) ⊗ₜ[R[X]] ((⇑dB)^[N] b) := by
    intro N
    induction N with
    | zero => intro b; rfl
    | succ N ih =>
        intro b
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hstep, ih]
  have hRE : Function.Injective (algebraMap R E) := by
    rw [IsScalarTower.algebraMap_eq R F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective R F)
  have hinj : Function.Injective (fun x : B => (1 : E[X]) ⊗ₜ[R[X]] x) := by
    intro x y hxy
    have hrepr : ∀ i : Fin n, algebraMap R[X] E[X] (e.repr x i)
        = algebraMap R[X] E[X] (e.repr y i) := by
      intro i
      have h1 := congrArg (fun z => (Module.Basis.baseChange E[X] e).repr z i) hxy
      simp only [Module.Basis.baseChange_repr_tmul] at h1
      simpa [Algebra.smul_def] using h1
    have hxe := e.sum_repr x
    have hye := e.sum_repr y
    rw [← hxe, ← hye]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    exact Polynomial.map_injective (algebraMap R E) hRE (hrepr i)
  obtain ⟨N, hN⟩ := locallyNilpotent_liftDerivation E (Module.Basis.baseChange E[X] e) hdb
    ((1 : E[X]) ⊗ₜ[R[X]] b)
  refine ⟨N, ?_⟩
  apply hinj
  show (1 : E[X]) ⊗ₜ[R[X]] ((⇑dB)^[N] b) = (1 : E[X]) ⊗ₜ[R[X]] (0 : B)
  rw [← hiter N b, TensorProduct.tmul_zero]
  exact hN

end GaloisForLFunctions.HTGeometry
