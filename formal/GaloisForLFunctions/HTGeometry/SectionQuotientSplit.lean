import GaloisForLFunctions.HTGeometry.SectionIdempotent
import GaloisForLFunctions.HTGeometry.ProductAlgebraDiscriminant
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# A section splits off a copy of the base, and the complement is again étale

Let `B` be a finite free `A`-algebra with unit discriminant and `ψ : B →ₐ[A] A` a section, with
idempotent `ε` (`SectionIdempotent`).  Then

```text
B  ≃ₐ[A]  A × (B ⧸ (ε))
```

by `b ↦ (ψ b, mk b)`: injectivity because an element of `(ε)` is `a • ε` and `ψ (a • ε) = a`,
surjectivity because `a • ε + c - ψ c • ε` has the prescribed image.

Over a principal ideal domain the complementary quotient is again finite free — it is finitely
generated and torsion-free, being a direct summand of `B` — of rank one less, and its discriminant
is again a unit by `ProductAlgebraDiscriminant`.  This is the inductive step of the splitting of an
étale algebra over the affine line.
-/

namespace GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

section Base

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B]
  {n : ℕ} (e : Module.Basis (Fin n) A B) (hd : IsUnit (Algebra.discr A e)) (ψ : B →ₐ[A] A)

/-- The complementary quotient attached to a section. -/
abbrev sectionQuot : Type _ := B ⧸ Ideal.span {sectionIdem e ψ}

include hd in
theorem mem_span_sectionIdem_iff {x : B} :
    x ∈ Ideal.span {sectionIdem e ψ} ↔ ∃ a : A, x = a • sectionIdem e ψ := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨ψ c, by rw [hc, sectionIdem_mul e hd ψ]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨algebraMap A B a, by rw [Algebra.smul_def, mul_comm]⟩

/-- The comparison map to the product of the base and the complementary quotient. -/
noncomputable def sectionProdHom : B →ₐ[A] A × sectionQuot e ψ :=
  AlgHom.prod ψ (Ideal.Quotient.mkₐ A (Ideal.span {sectionIdem e ψ}))

include hd in
theorem sectionProdHom_bijective : Function.Bijective (sectionProdHom e ψ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 : ψ b = 0 := by
      have := congrArg Prod.fst hb
      simpa [sectionProdHom] using this
    have h2 : b ∈ Ideal.span {sectionIdem e ψ} := by
      have := congrArg Prod.snd hb
      simp only [sectionProdHom, AlgHom.prod_apply, Prod.snd_zero] at this
      rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at this
    obtain ⟨a, rfl⟩ := (mem_span_sectionIdem_iff e hd ψ).mp h2
    rw [map_smul, apply_sectionIdem e hd ψ, smul_eq_mul, mul_one] at h1
    rw [h1, zero_smul]
  · rintro ⟨a, q⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨a • sectionIdem e ψ + c - (ψ c) • sectionIdem e ψ, ?_⟩
    have hmem₁ : a • sectionIdem e ψ ∈ Ideal.span {sectionIdem e ψ} :=
      (mem_span_sectionIdem_iff e hd ψ).mpr ⟨a, rfl⟩
    have hmem₂ : (ψ c) • sectionIdem e ψ ∈ Ideal.span {sectionIdem e ψ} :=
      (mem_span_sectionIdem_iff e hd ψ).mpr ⟨ψ c, rfl⟩
    have hfst : ψ (a • sectionIdem e ψ + c - (ψ c) • sectionIdem e ψ) = a := by
      rw [map_sub, map_add, map_smul, map_smul, apply_sectionIdem e hd ψ, smul_eq_mul,
        smul_eq_mul, mul_one, mul_one]
      ring
    have hsnd : (Ideal.Quotient.mk (Ideal.span {sectionIdem e ψ}))
        (a • sectionIdem e ψ + c - (ψ c) • sectionIdem e ψ)
        = Ideal.Quotient.mk _ c := by
      rw [map_sub, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hmem₁,
        (Ideal.Quotient.eq_zero_iff_mem).mpr hmem₂, zero_add, sub_zero]
    apply Prod.ext
    · simpa [sectionProdHom] using hfst
    · simpa [sectionProdHom] using hsnd

/-- **A section of a finite étale algebra splits off a copy of the base.** -/
noncomputable def sectionProdEquiv : B ≃ₐ[A] A × sectionQuot e ψ :=
  AlgEquiv.ofBijective (sectionProdHom e ψ) (sectionProdHom_bijective e hd ψ)


end Base

section Pid

variable {A B : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
  {n : ℕ} (e : Module.Basis (Fin (n + 1)) A B) (hd : IsUnit (Algebra.discr A e))
  (ψ : B →ₐ[A] A)

include hd in
theorem finite_sectionQuot : Module.Finite A (sectionQuot e ψ) :=
  Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ A (Ideal.span {sectionIdem e ψ})).toLinearMap
    Ideal.Quotient.mk_surjective

include hd in
theorem torsionFree_sectionQuot : Module.IsTorsionFree A (sectionQuot e ψ) := by
  haveI hBtf : Module.IsTorsionFree A B := Module.free_iff_isTorsionFree.mp inferInstance
  haveI : Module.IsTorsionFree A (A × sectionQuot e ψ) :=
    Function.Injective.moduleIsTorsionFree (N := B) (sectionProdEquiv e hd ψ).symm
      (sectionProdEquiv e hd ψ).symm.injective (fun r m => by simp)
  exact Function.Injective.moduleIsTorsionFree (N := A × sectionQuot e ψ)
    (fun q => ((0 : A), q)) (fun q q' h => by simpa using h) (fun r m => by simp)

include hd in
theorem finrank_sectionQuot : Module.finrank A (sectionQuot e ψ) = n := by
  haveI := finite_sectionQuot e hd ψ
  haveI := torsionFree_sectionQuot e hd ψ
  haveI : Module.Free A (sectionQuot e ψ) := Module.free_of_finite_type_torsion_free'
  have h1 : Module.finrank A B = n + 1 := by
    rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  have h2 : Module.finrank A B = Module.finrank A (A × sectionQuot e ψ) :=
    LinearEquiv.finrank_eq (sectionProdEquiv e hd ψ).toLinearEquiv
  rw [Module.finrank_prod, Module.finrank_self] at h2
  omega

include hd in
theorem exists_basis_sectionQuot :
    ∃ e' : Module.Basis (Fin n) A (sectionQuot e ψ), IsUnit (Algebra.discr A e') := by
  classical
  haveI := finite_sectionQuot e hd ψ
  haveI := torsionFree_sectionQuot e hd ψ
  haveI : Module.Free A (sectionQuot e ψ) := Module.free_of_finite_type_torsion_free'
  set b' := Module.finBasisOfFinrankEq A (sectionQuot e ψ) (finrank_sectionQuot e hd ψ) with hb'
  refine ⟨b', ?_⟩
  set Θ := sectionProdEquiv e hd ψ with hΘ
  set bAB' : Module.Basis (Unit ⊕ Fin n) A (A × sectionQuot e ψ) :=
    (Module.Basis.singleton Unit A).prod b' with hbAB'
  set bB : Module.Basis (Unit ⊕ Fin n) A B := bAB'.map Θ.symm.toLinearEquiv with hbB
  set σ : (Unit ⊕ Fin n) ≃ Fin (n + 1) :=
    ((Equiv.sumCongr finOneEquiv.symm (Equiv.refl (Fin n))).trans
      finSumFinEquiv).trans (finCongr (Nat.add_comm 1 n)) with hσ
  have h1 : IsUnit (Algebra.discr A (bB.reindex σ)) :=
    isUnit_discr_of_isUnit_discr e (bB.reindex σ) hd
  have h2 : Algebra.discr A ⇑(bB.reindex σ) = Algebra.discr A ⇑bB := by
    rw [Module.Basis.coe_reindex]
    exact Algebra.discr_reindex (A := A) (b := bB) (f := σ)
  have hcoe : ⇑bB = ⇑Θ.symm ∘ ⇑bAB' := by
    funext i; rfl
  have h3 : Algebra.discr A ⇑bB = Algebra.discr A ⇑bAB' := by
    rw [hcoe, ← Algebra.discr_eq_discr_of_algEquiv ⇑bAB' Θ.symm]
  have h4 : Algebra.discr A ⇑bAB' = Algebra.discr A ⇑b' := discr_prod_singleton b'
  rw [← h4, ← h3, ← h2]
  exact h1

end Pid

end GaloisForLFunctions.HTGeometry
