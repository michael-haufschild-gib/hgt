/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Endomorphisms under scalar extension

This file proves that extending scalars commutes with endomorphism rings of finite projective
modules.  The finite-free case is a basis calculation.  A finite projective module is a retract of
a finite free module, and the general result follows by transporting the free calculation across
that retract.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- For a finite free module, every endomorphism after scalar extension comes by scalar extending
an endomorphism before scalar extension. -/
theorem tensorProductEnd_surjective_of_free
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Function.Surjective (LinearMap.tensorProductEnd R S M) := by
  classical
  let b := Module.Free.chooseBasis R M
  let bS := Algebra.TensorProduct.basis S b
  apply LinearMap.range_eq_top.1
  apply top_unique
  rw [← bS.end.span_eq]
  refine Submodule.span_le.2 ?_
  rintro f ⟨ij, rfl⟩
  refine ⟨1 ⊗ₜ[R] b.end ij, ?_⟩
  simp only [LinearMap.tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
    TensorProduct.lift.tmul]
  dsimp
  simp only [one_smul, LinearMap.baseChangeHom_apply]
  rw [b.baseChange_end S ij]

/-- For a finite free module, scalar extension identifies the endomorphism modules. -/
theorem tensorProductEnd_bijective_of_free
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Function.Bijective (LinearMap.tensorProductEnd R S M) := by
  classical
  let b := Module.Free.chooseBasis R M
  letI : Fintype (Module.Free.ChooseBasisIndex R M) :=
    Module.Free.ChooseBasisIndex.fintype R M
  let bS := Algebra.TensorProduct.basis S b
  let e := (Algebra.TensorProduct.basis S b.end).equiv bS.end (Equiv.refl _)
  have hmap : (LinearMap.tensorProductEnd R S M :
      (S ⊗[R] Module.End R M) →ₗ[S] Module.End S (S ⊗[R] M)) = e.toLinearMap := by
    apply (Algebra.TensorProduct.basis S b.end).ext
    intro ij
    rw [Algebra.TensorProduct.basis_apply]
    change LinearMap.tensorProductEnd R S M (1 ⊗ₜ[R] b.end ij) =
      e (1 ⊗ₜ[R] b.end ij)
    simp only [LinearMap.tensorProductEnd_apply, TensorProduct.liftAux_tmul]
    change (1 : S) • LinearMap.baseChange S (b.end ij) = e (1 ⊗ₜ[R] b.end ij)
    simp only [one_smul]
    rw [b.baseChange_end S ij]
    rw [← Algebra.TensorProduct.basis_apply (A := S) b.end ij]
    symm
    exact Module.Basis.equiv_apply (Algebra.TensorProduct.basis S b.end) ij bS.end (Equiv.refl _)
  constructor
  · intro x y hxy
    apply e.injective
    calc
      e x = LinearMap.tensorProductEnd R S M x := (DFunLike.congr_fun hmap x).symm
      _ = LinearMap.tensorProductEnd R S M y := hxy
      _ = e y := DFunLike.congr_fun hmap y
  · intro y
    obtain ⟨x, hx⟩ := e.surjective y
    exact ⟨x, (DFunLike.congr_fun hmap x).trans hx⟩

/-- The endomorphism base-change map commutes with passing between a module and a retract. -/
theorem tensorProductEnd_map_comp
    {R S M F : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup F] [Module R M] [Module R F]
    (p : F →ₗ[R] M) (i : M →ₗ[R] F) (t : S ⊗[R] Module.End R F) :
    LinearMap.tensorProductEnd R S M
        (TensorProduct.map (LinearMap.id) {
          toFun := fun f => p ∘ₗ f ∘ₗ i
          map_add' := by intro f g; ext; simp
          map_smul' := by intro r f; ext; simp } t) =
      (LinearMap.baseChange S p) ∘ₗ
        (LinearMap.tensorProductEnd R S F t) ∘ₗ (LinearMap.baseChange S i) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    ext
    simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    ext
    simp
  | tmul s f =>
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      change
        (LinearMap.tensorProductEnd R S M
          (TensorProduct.map (LinearMap.id) {
            toFun := fun f => p ∘ₗ f ∘ₗ i
            map_add' := by intro f g; ext; simp
            map_smul' := by intro r f; ext; simp } (s ⊗ₜ[R] f))) (x + y) =
          ((LinearMap.baseChange S p) ∘ₗ
            (LinearMap.tensorProductEnd R S F (s ⊗ₜ[R] f)) ∘ₗ
              (LinearMap.baseChange S i)) (x + y)
      rw [map_add, map_add, hx, hy]
    | tmul s' x =>
      simp only [TensorProduct.map_tmul, LinearMap.tensorProductEnd_apply,
        TensorProduct.liftAux_tmul]
      change (s • LinearMap.baseChange S (p ∘ₗ f ∘ₗ i)) (s' ⊗ₜ[R] x) =
        (LinearMap.baseChange S p ∘ₗ (s • LinearMap.baseChange S f) ∘ₗ
          LinearMap.baseChange S i) (s' ⊗ₜ[R] x)
      simp only [LinearMap.smul_apply, LinearMap.baseChange_tmul, LinearMap.comp_apply]
      simp

/-- Scalar extension identifies endomorphisms of every finite projective module. -/
theorem tensorProductEnd_bijective_of_projective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Projective R M] [Module.Finite R M] :
    Function.Bijective (LinearMap.tensorProductEnd R S M) := by
  classical
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let F := Fin n → R
  let pS := LinearMap.baseChange S p
  let iS := LinearMap.baseChange S i
  let j : Module.End R M →ₗ[R] Module.End R F := {
    toFun := fun f => i ∘ₗ f ∘ₗ p
    map_add' := by intro f g; ext; simp
    map_smul' := by intro r f; ext; simp }
  let q : Module.End R F →ₗ[R] Module.End R M := {
    toFun := fun f => p ∘ₗ f ∘ₗ i
    map_add' := by intro f g; ext; simp
    map_smul' := by intro r f; ext; simp }
  let jS : (S ⊗[R] Module.End R M) →ₗ[R] (S ⊗[R] Module.End R F) :=
    TensorProduct.map (LinearMap.id : S →ₗ[R] S) j
  let qS : (S ⊗[R] Module.End R F) →ₗ[R] (S ⊗[R] Module.End R M) :=
    TensorProduct.map (LinearMap.id : S →ₗ[R] S) q
  have hpiS : pS ∘ₗ iS = LinearMap.id := by
    dsimp [pS, iS]
    rw [← LinearMap.baseChange_comp, hpi, LinearMap.baseChange_id]
  have hqj : Function.LeftInverse qS jS := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [qS, jS]
    | add x y hx hy => simp [qS, jS, hx, hy]
    | tmul s f =>
      change (LinearMap.id s) ⊗ₜ[R] (q (j f)) = s ⊗ₜ[R] f
      congr 1
      ext x
      dsimp [q, j]
      change p (i (f (p (i x)))) = f x
      have hpi_apply (z : M) : p (i z) = z := LinearMap.congr_fun hpi z
      rw [hpi_apply x, hpi_apply (f x)]
  constructor
  · intro x y hxy
    apply hqj.injective
    apply (tensorProductEnd_bijective_of_free (R := R) (S := S) (M := F)).1
    calc
      LinearMap.tensorProductEnd R S F (jS x) =
          iS ∘ₗ LinearMap.tensorProductEnd R S M x ∘ₗ pS := by
            simpa [jS, j, iS, pS] using
              (tensorProductEnd_map_comp (p := i) (i := p) x)
      _ = iS ∘ₗ LinearMap.tensorProductEnd R S M y ∘ₗ pS := by rw [hxy]
      _ = LinearMap.tensorProductEnd R S F (jS y) := by
            simpa [jS, j, iS, pS] using
              (tensorProductEnd_map_comp (p := i) (i := p) y).symm
  · intro g
    let gF : Module.End S (S ⊗[R] F) := iS ∘ₗ g ∘ₗ pS
    obtain ⟨u, hu⟩ := (tensorProductEnd_bijective_of_free (R := R) (S := S) (M := F)).2 gF
    refine ⟨qS u, ?_⟩
    calc
      LinearMap.tensorProductEnd R S M (qS u) =
          pS ∘ₗ LinearMap.tensorProductEnd R S F u ∘ₗ iS := by
            simpa [qS, q, pS, iS] using (tensorProductEnd_map_comp (p := p) (i := i) u)
      _ = pS ∘ₗ gF ∘ₗ iS := by rw [hu]
      _ = g := by
        dsimp [gF]
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply]
        have hpiS_apply (z : S ⊗[R] M) : pS (iS z) = z := LinearMap.congr_fun hpiS z
        rw [hpiS_apply x, hpiS_apply (g x)]

end GaloisForLFunctions.HTGeometry.ABHN
