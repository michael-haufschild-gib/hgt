import GaloisForLFunctions.HTGeometry.SplitFibresPackage
import GaloisForLFunctions.HTGeometry.SplitFibreAlgHom
import GaloisForLFunctions.HTGeometry.ComplexAffineLineSimplyConnectedGeneral
import GaloisForLFunctions.HTGeometry.AlgebraDiscriminantBaseChange
import GaloisForLFunctions.HTGeometry.SplitFiniteAlgebraDiscriminant

/-!
# A unit discriminant splits every complex fibre

For a finite free `ℂ[X]`-algebra, "every fibre is split" is exactly "the discriminant of a basis is
a unit".  This module proves the direction that the covering-space argument consumes:

```text
IsUnit (Algebra.discr ℂ[X] e)   ⟹   SplitFibres B n
```

The fibre at a parameter `s` is the base change `ℂ ⊗[ℂ[X]] B` along evaluation at `s`; its
discriminant is the value at `s` of the discriminant of `B` (`AlgebraDiscriminantBaseChange`), which
is a nonzero constant.  `SplitFiniteAlgebraDiscriminant` then splits that fibre, and the universal
property of base change (`AlgHom.liftEquiv`) identifies the algebra maps of the fibre with the
complex points of `B` above `s`.

The point of the reformulation is that `IsUnit (Algebra.discr ℂ[X] e)` is a statement about a single
ring element, hence transportable along an arbitrary ring homomorphism, while `SplitFibres` is not.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 1600000

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- **A unit discriminant splits every fibre of the complex-point space.** -/
theorem splitFibres_of_isUnit_discr [Module.Free ℂ[X] B] [Module.Finite ℂ[X] B] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ[X] B) (hd : IsUnit (Algebra.discr ℂ[X] e)) :
    SplitFibres B n := by
  intro s
  letI algCX : Algebra ℂ[X] ℂ := (Polynomial.evalRingHom s).toAlgebra
  have hmap : ∀ q : ℂ[X], algebraMap ℂ[X] ℂ q = q.eval s := fun q => rfl
  haveI tower1 : IsScalarTower ℂ ℂ[X] ℂ :=
    IsScalarTower.of_algebraMap_eq (fun c => by rw [hmap]; simp)
  haveI tower2 : IsScalarTower ℂ[X] ℂ ℂ :=
    IsScalarTower.of_algebraMap_eq (fun q => by simp)
  have hdisc : Algebra.discr ℂ (e.baseChange ℂ : Module.Basis (Fin n) ℂ (ℂ ⊗[ℂ[X]] B)) ≠ 0 := by
    rw [discr_baseChange ℂ[X] ℂ B e, hmap]
    obtain ⟨c, hc, hce⟩ := (Polynomial.isUnit_iff).mp hd
    rw [← hce]
    simpa using hc.ne_zero
  obtain ⟨ξ, hsurj, hexh⟩ := exists_algHom_family_of_discr_ne_zero (e.baseChange ℂ) hdisc
  set L : (B →ₐ[ℂ[X]] ℂ) ≃ (ℂ ⊗[ℂ[X]] B →ₐ[ℂ] ℂ) := AlgHom.liftEquiv ℂ[X] ℂ B ℂ with hL
  refine ⟨fun i => (AlgHom.restrictScalars ℂ (L.symm (ξ i)) : B →ₐ[ℂ] ℂ), ?_, ?_, ?_⟩
  · intro i
    show (L.symm (ξ i)) (algebraMap ℂ[X] B X) = s
    rw [(L.symm (ξ i)).commutes, hmap]
    simp
  · intro y
    have hχ : ∀ (i : Fin n) (b : B),
        (AlgHom.restrictScalars ℂ (L.symm (ξ i)) : B →ₐ[ℂ] ℂ) b = ξ i (1 ⊗ₜ[ℂ[X]] b) :=
      fun i b => rfl
    have key : ∀ c : ℂ ⊗[ℂ[X]] B, ∃ b : B, ∀ i, ξ i c = ξ i (1 ⊗ₜ[ℂ[X]] b) := by
      intro c
      induction c using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul a b =>
          refine ⟨a • b, fun i => ?_⟩
          have h1 : (a : ℂ) ⊗ₜ[ℂ[X]] b = a • ((1 : ℂ) ⊗ₜ[ℂ[X]] b) := by
            rw [TensorProduct.smul_tmul']
            simp
          rw [h1, map_smul, ← hχ i b, ← hχ i (a • b), map_smul]
      | add x z hx hz =>
          obtain ⟨b₁, hb₁⟩ := hx
          obtain ⟨b₂, hb₂⟩ := hz
          refine ⟨b₁ + b₂, fun i => ?_⟩
          rw [map_add, hb₁, hb₂, ← map_add, ← TensorProduct.tmul_add]
    obtain ⟨c, hc⟩ := hsurj y
    obtain ⟨b, hb⟩ := key c
    refine ⟨b, ?_⟩
    funext i
    show (AlgHom.restrictScalars ℂ (L.symm (ξ i)) : B →ₐ[ℂ] ℂ) b = y i
    rw [hχ i b, ← hb i]
    exact congrFun hc i
  · ext χ'
    constructor
    · intro (hs : AlgSpec.proj B χ' = s)
      let ψ : B →ₐ[ℂ[X]] ℂ :=
        { (χ' : B →ₐ[ℂ] ℂ).toRingHom with
          commutes' := fun q => by
            show χ' (algebraMap ℂ[X] B q) = algebraMap ℂ[X] ℂ q
            rw [AlgSpec.apply_algebraMap, hmap, hs] }
      obtain ⟨i, hi⟩ := hexh (L ψ)
      refine ⟨i, ?_⟩
      have hψ : L.symm (ξ i) = ψ := by rw [← hi, Equiv.symm_apply_apply]
      show (AlgHom.restrictScalars ℂ (L.symm (ξ i)) : B →ₐ[ℂ] ℂ) = χ'
      rw [hψ]
      rfl
    · rintro ⟨i, rfl⟩
      show (L.symm (ξ i)) (algebraMap ℂ[X] B X) = s
      rw [(L.symm (ξ i)).commutes, hmap]
      simp

/-- **A finite free `ℂ[X]`-algebra with unit discriminant admits a `ℂ[X]`-algebra map to
`ℂ[X]`.** -/
theorem nonempty_algHom_of_isUnit_discr [Module.Free ℂ[X] B] [Module.Finite ℂ[X] B] {n : ℕ}
    (hn : 1 ≤ n) (e : Module.Basis (Fin n) ℂ[X] B) (hd : IsUnit (Algebra.discr ℂ[X] e)) :
    Nonempty (B →ₐ[ℂ[X]] ℂ[X]) :=
  nonempty_algHom_of_splitFibres hn e (splitFibres_of_isUnit_discr e hd)

/-- **Algebraic simple connectedness of the complex affine line, discriminant form.** -/
theorem rank_eq_one_of_isUnit_discr [IsDomain B] [Module.Free ℂ[X] B] [Module.Finite ℂ[X] B]
    {n : ℕ} (hn : 1 ≤ n) (e : Module.Basis (Fin n) ℂ[X] B)
    (hd : IsUnit (Algebra.discr ℂ[X] e)) : n = 1 :=
  rank_eq_one_of_splitFibres hn e (splitFibres_of_isUnit_discr e hd)

end

end GaloisForLFunctions.HTGeometry
