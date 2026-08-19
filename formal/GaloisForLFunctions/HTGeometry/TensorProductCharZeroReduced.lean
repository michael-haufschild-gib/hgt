import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedReduced
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Tensor products of reduced algebras in characteristic zero

Over a field of characteristic zero the tensor product of two reduced algebras is reduced.  This is
the statement that a reduced algebra over a characteristic-zero field is geometrically reduced,
and it is what makes the constants of a Picard--Vessiot torsor a reduced Hopf algebra, so that its
points separate.

The proof runs through the algebraic closure.  A finitely generated subalgebra of the algebraic
closure is a finite separable field extension, and a finite separable extension keeps a reduced base
reduced: expand a nilpotent tensor against a basis of the extension and specialise the coefficients
at each prime of the base, where the tensor product is with a field and unramifiedness applies.
Over the algebraic closure itself points separate, which settles the reduced-times-reduced case
there; the original tensor product embeds into that base change.
-/


namespace GaloisForLFunctions.HTGeometry

open TensorProduct Module

noncomputable section

/-- A finite separable field extension stays reduced after any field base change. -/
theorem isReduced_tensorProduct_field_of_isSeparable
    (F E Ω : Type*) [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra.IsSeparable F E] [Module.Finite F E] : IsReduced (Ω ⊗[F] E) := by
  haveI : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  exact Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[F] E)

/-- **A finite separable field extension stays reduced after any reduced base change.**  A nilpotent
tensor is expanded against a basis of the extension; its image at each prime of the base lies in a
tensor product with a field, hence vanishes, so every coefficient lies in every prime. -/
theorem isReduced_tensorProduct_of_isSeparable
    {F E S : Type*} [Field F] [Field E] [CommRing S] [Algebra F E] [Algebra F S]
    [Algebra.IsSeparable F E] [Module.Finite F E] [IsReduced S] :
    IsReduced (S ⊗[F] E) := by
  classical
  constructor
  intro z hz
  obtain ⟨t, a, rfl⟩ := exists_basis_tmul_repr (Basis.ofVectorSpace F E) z
  set bs := Basis.ofVectorSpace F E with hbs
  have hcoef : ∀ i ∈ t, a i = 0 := by
    intro i hi
    have hnil : IsNilpotent (a i) := by
      rw [nilpotent_iff_mem_prime]
      intro J hJ
      haveI : IsDomain (S ⧸ J) := Ideal.Quotient.isDomain J
      set ψ : S →ₐ[F] FractionRing (S ⧸ J) :=
        (IsScalarTower.toAlgHom F (S ⧸ J) (FractionRing (S ⧸ J))).comp
          (Ideal.Quotient.mkₐ F J) with hψ
      set φ : S ⊗[F] E →ₐ[F] (FractionRing (S ⧸ J)) ⊗[F] E :=
        Algebra.TensorProduct.map ψ (AlgHom.id F E) with hφ
      haveI : IsReduced ((FractionRing (S ⧸ J)) ⊗[F] E) :=
        isReduced_tensorProduct_field_of_isSeparable F E _
      have hzero : φ (∑ i ∈ t, a i ⊗ₜ[F] bs i) = 0 := (hz.map φ).eq_zero
      rw [map_sum] at hzero
      set B := Algebra.TensorProduct.basis (FractionRing (S ⧸ J)) bs with hB
      have hexp : ∑ i ∈ t, φ (a i ⊗ₜ[F] bs i) = ∑ i ∈ t, ψ (a i) • B i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hφ, Algebra.TensorProduct.map_tmul, hB, Algebra.TensorProduct.basis_apply]
        simp [TensorProduct.smul_tmul']
      rw [hexp] at hzero
      have hψzero : ψ (a i) = 0 :=
        linearIndependent_iff'.mp B.linearIndependent t (fun i => ψ (a i)) hzero i hi
      have : (Ideal.Quotient.mk J) (a i) = 0 := by
        have hinj : Function.Injective (algebraMap (S ⧸ J) (FractionRing (S ⧸ J))) :=
          IsFractionRing.injective _ _
        apply hinj
        rw [map_zero]
        simpa [hψ] using hψzero
      exact (Ideal.Quotient.eq_zero_iff_mem).mp this
    exact hnil.eq_zero
  rw [Finset.sum_congr rfl (fun i hi => by rw [hcoef i hi, TensorProduct.zero_tmul])]
  simp

/-- **Characteristic zero: an algebraic closure stays reduced after any reduced base change.**
Every finitely generated subalgebra of the algebraic closure is a finite separable field extension,
and a reduced algebra survives such a base change. -/
theorem isReduced_tensorProduct_algebraicClosure
    {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A] [IsReduced A] :
    IsReduced (A ⊗[K] (AlgebraicClosure K)) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun E' hE' => ?_)
  haveI : Algebra.FiniteType K ↥E' := ⟨(Subalgebra.fg_top E').mpr hE'⟩
  haveI : Algebra.IsAlgebraic K ↥E' :=
    Algebra.IsAlgebraic.of_injective E'.val Subtype.val_injective
  haveI : Algebra.IsIntegral K ↥E' := inferInstance
  haveI : Module.Finite K ↥E' := Algebra.IsIntegral.finite
  letI : Field ↥E' := (Subalgebra.isField_of_algebraic E').toField
  haveI : Algebra.IsSeparable K ↥E' := inferInstance
  exact isReduced_tensorProduct_of_isSeparable

/-- **In characteristic zero the tensor product of reduced algebras is reduced.**  Both factors
become reduced over the algebraic closure, where points separate, and the original tensor product
embeds into that base change. -/
theorem isReduced_tensorProduct_of_charZero
    {K A B : Type*} [Field K] [CharZero K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [IsReduced A] [IsReduced B] :
    IsReduced (A ⊗[K] B) := by
  haveI h0A : IsReduced (A ⊗[K] (AlgebraicClosure K)) := isReduced_tensorProduct_algebraicClosure
  haveI h0B : IsReduced (B ⊗[K] (AlgebraicClosure K)) := isReduced_tensorProduct_algebraicClosure
  haveI h1 : IsReduced ((AlgebraicClosure K) ⊗[K] A) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K (AlgebraicClosure K) A)
      (Algebra.TensorProduct.comm K (AlgebraicClosure K) A).injective
  haveI h2 : IsReduced ((AlgebraicClosure K) ⊗[K] B) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K (AlgebraicClosure K) B)
      (Algebra.TensorProduct.comm K (AlgebraicClosure K) B).injective
  haveI h3 : IsReduced (((AlgebraicClosure K) ⊗[K] A) ⊗[AlgebraicClosure K]
      ((AlgebraicClosure K) ⊗[K] B)) := isReduced_tensorProduct_of_isAlgClosed
  haveI h4 : IsReduced (((AlgebraicClosure K) ⊗[K] A) ⊗[K] B) := by
    have e := Algebra.TensorProduct.cancelBaseChange K (AlgebraicClosure K) (AlgebraicClosure K)
      ((AlgebraicClosure K) ⊗[K] A) B
    exact isReduced_of_injective e.symm e.symm.injective
  haveI h5 : IsReduced ((AlgebraicClosure K) ⊗[K] (A ⊗[K] B)) := by
    have e := Algebra.TensorProduct.assoc K K (AlgebraicClosure K) (AlgebraicClosure K) A B
    exact isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : (A ⊗[K] B) →ₐ[K] (AlgebraicClosure K) ⊗[K] (A ⊗[K] B))
    (Algebra.TensorProduct.includeRight_injective (RingHom.injective _))

end

end GaloisForLFunctions.HTGeometry
