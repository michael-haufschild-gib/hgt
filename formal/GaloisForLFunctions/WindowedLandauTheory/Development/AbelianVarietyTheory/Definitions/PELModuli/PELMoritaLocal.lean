import Mathlib.RingTheory.Morita.Matrix
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Morita comparison of free modules over a local scalar quotient of an order. -/

noncomputable section

open CategoryTheory
open scoped Matrix.Module

namespace GlobalTheory.MoritaLocal

private theorem corner_equiv {B : Type} [CommRing B] [IsLocalRing B] {m k : ℕ} (hm : 0 < m)
    (C : Type) [AddCommGroup C] [Module B C] (e : (Fin m → C) ≃ₗ[B] (Fin (m * k) → B)) :
    Nonempty (C ≃ₗ[B] (Fin k → B)) := by
  let i : Fin m := ⟨0, hm⟩
  let s : C →ₗ[B] (Fin m → C) := LinearMap.single B (fun _ => C) i
  let p : (Fin m → C) →ₗ[B] C := LinearMap.proj i
  haveI : Module.Free B (Fin m → C) := Module.Free.of_equiv e.symm
  haveI : Module.Finite B (Fin m → C) := Module.Finite.equiv e.symm
  haveI : Module.Projective B C := Module.Projective.of_split s p (LinearMap.ext fun x => by simp [s, p])
  haveI : Module.Finite B C := Module.Finite.of_surjective p (fun x => ⟨Pi.single i x, by simp [p]⟩)
  haveI : Module.Free B C := Module.free_of_flat_of_isLocalRing
  have h : Module.finrank B (Fin m → C) = m * k := e.finrank_eq.trans (Module.finrank_fin_fun B)
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  exact ⟨LinearEquiv.ofFinrankEq C (Fin k → B)
    ((Nat.eq_of_mul_eq_mul_left hm h).trans (Module.finrank_fin_fun B).symm)⟩

/-- Equal free ranks over the local scalar ring yield isomorphic matrix modules. -/
private theorem matrix_equiv {B : Type} [CommRing B] [IsLocalRing B] {m k : ℕ} (hm : 0 < m)
    {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module (Matrix (Fin m) (Fin m) B) M] [Module (Matrix (Fin m) (Fin m) B) N]
    [Module B M] [Module B N] [IsScalarTower B (Matrix (Fin m) (Fin m) B) M]
    [IsScalarTower B (Matrix (Fin m) (Fin m) B) N]
    (eM : M ≃ₗ[B] (Fin (m * k) → B)) (eN : N ≃ₗ[B] (Fin (m * k) → B)) :
    Nonempty (M ≃ₗ[Matrix (Fin m) (Fin m) B] N) := by
  let A := Matrix (Fin m) (Fin m) B
  let i : Fin m := ⟨0, hm⟩
  let e₁ := toModuleCatFromModuleCatLinearEquiv B (ModuleCat.of A M) i
  let e₂ := toModuleCatFromModuleCatLinearEquiv B (ModuleCat.of A N) i
  obtain ⟨f₁⟩ := corner_equiv hm _ ((e₁.restrictScalars B).symm.trans eM)
  obtain ⟨f₂⟩ := corner_equiv hm _ ((e₂.restrictScalars B).symm.trans eN)
  let g := f₁.trans f₂.symm
  let g' := LinearEquiv.ofBijective (g.toLinearMap.mapMatrixModule (Fin m)) (by
    constructor
    · intro a b h
      exact funext fun i => g.injective (congrFun h i)
    · intro b
      exact ⟨fun i => g.symm (b i), funext fun i => g.apply_symm_apply (b i)⟩)
  exact ⟨e₁.trans (g'.trans e₂.symm)⟩

/-- An order module on which the kernel acts trivially factors through the quotient ring. -/
private abbrev quotientModule {O B M : Type} [Ring O] [Ring B] [AddCommGroup M] [Module O M]
    {φ : O →+* B} (hφ : Function.Surjective φ)
    (hM : Module.IsTorsionBySet O M (RingHom.ker φ)) : Module B M :=
  letI := hM.module
  Module.compHom M (RingHom.quotientKerEquivOfSurjective hφ).symm.toRingHom

private theorem quotientModule_smul {O B M : Type} [Ring O] [Ring B] [AddCommGroup M] [Module O M]
    {φ : O →+* B} (hφ : Function.Surjective φ) (hM : Module.IsTorsionBySet O M (RingHom.ker φ))
    (o : O) (x : M) : letI := quotientModule hφ hM; (φ o) • x = o • x := by
  letI := hM.module
  change ((RingHom.quotientKerEquivOfSurjective hφ).symm (φ o)) • x = o • x
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  exact hM.mk_smul o x

private theorem torsion_ker {R O B M : Type} [CommRing R] [Ring O] [Ring B] [Algebra R O]
    [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower R O M]
    (I : Ideal R) (φ : O →+* B)
    (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O))
    (hI : ∀ c ∈ I, ∀ x : M, c • x = 0) : Module.IsTorsionBySet O M (RingHom.ker φ) := by
  intro x b
  have h : b.val ∈ I • (⊤ : Submodule R O) := hker _ (RingHom.mem_ker.mp b.2)
  refine Submodule.smul_induction_on h ?_ ?_
  · intro c hc o _
    rw [smul_assoc, hI c hc]
  · intro y z hy hz
    rw [add_smul, hy, hz, zero_add]

/-- Two modules with the same free rank over the local scalar quotient are linearly isomorphic over the order. -/
theorem morita_local {R : Type} [CommRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)]
    {m k : ℕ} (hm : 0 < m) {O : Type} [Ring O] [Algebra R O]
    (φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)) (hφ : Function.Surjective φ)
    (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O))
    {M N : Type} [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower R O M]
    [AddCommGroup N] [Module O N] [Module R N] [IsScalarTower R O N]
    (eM : M ≃ₗ[R] (Fin (m * k) → R ⧸ I)) (eN : N ≃ₗ[R] (Fin (m * k) → R ⧸ I)) :
    Nonempty (M ≃ₗ[O] N) := by
  let B := R ⧸ I
  let A := Matrix (Fin m) (Fin m) B
  have ht (P : Type) [AddCommGroup P] [Module R P] (e : P ≃ₗ[R] (Fin (m * k) → B))
      (c : R) (hc : c ∈ I) (x : P) : c • x = 0 := by
    apply e.injective
    rw [map_smul, map_zero]
    funext i
    change (algebraMap R B c) * e x i = 0
    rw [show algebraMap R B c = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_mul]
  have hM := torsion_ker I φ.toRingHom hker (ht M eM)
  have hN := torsion_ker I φ.toRingHom hker (ht N eN)
  letI : Module A M := quotientModule (φ := φ.toRingHom) hφ hM
  letI : Module A N := quotientModule (φ := φ.toRingHom) hφ hN
  letI : Module B M := Module.compHom M (algebraMap B A)
  letI : Module B N := Module.compHom N (algebraMap B A)
  haveI : IsScalarTower B A M := IsScalarTower.of_compHom B A M
  haveI : IsScalarTower B A N := IsScalarTower.of_compHom B A N
  have hMs (o : O) (x : M) : φ o • x = o • x := quotientModule_smul hφ hM o x
  have hNs (o : O) (x : N) : φ o • x = o • x := quotientModule_smul hφ hN o x
  have hMR (r : R) (x : M) : (algebraMap R B r) • x = r • x := by
    change (algebraMap B A (algebraMap R B r)) • x = r • x
    rw [← IsScalarTower.algebraMap_apply R B A, ← φ.commutes, hMs, algebraMap_smul]
  have hNR (r : R) (x : N) : (algebraMap R B r) • x = r • x := by
    change (algebraMap B A (algebraMap R B r)) • x = r • x
    rw [← IsScalarTower.algebraMap_apply R B A, ← φ.commutes, hNs, algebraMap_smul]
  haveI : IsScalarTower R B M := IsScalarTower.of_algebraMap_smul hMR
  haveI : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul hNR
  have hB : Function.Surjective (algebraMap R B) := Ideal.Quotient.mk_surjective (I := I)
  let fM : M ≃ₗ[B] (Fin (m * k) → B) := LinearEquiv.extendScalarsOfSurjective hB eM
  let fN : N ≃ₗ[B] (Fin (m * k) → B) := LinearEquiv.extendScalarsOfSurjective hB eN
  obtain ⟨e⟩ := matrix_equiv hm fM fN
  refine ⟨{ e.toAddEquiv with map_smul' := ?_ }⟩
  intro o x
  change e (o • x) = o • e x
  exact (congrArg e (hMs o x).symm).trans ((e.map_smul (φ o) x).trans (hNs o (e x)))

end GlobalTheory.MoritaLocal
