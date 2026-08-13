import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.Algebra.Algebra.Rat

/-!
# Reduced tensor products in characteristic zero

This module proves the reducedness theorem needed in Hazewinkel's argument without assuming
linear disjointness.  Over a perfect field, the tensor product of two arbitrary field extensions
is reduced.  The proof passes from finitely generated extensions to a separating transcendence
basis, identifies the purely transcendental part with a localization of a polynomial ring, and
then uses separability for the algebraic remainder.  Finitely generated subalgebra descent removes
all finiteness assumptions.

As an integral corollary, the tensor product over `ℤ` of any two characteristic-zero domains is
reduced.  This is the exact tensor-reducedness input in the Deninger--Hazewinkel stage argument;
only primeness of the individual Hankel determinantal ideals remains.
-/

namespace RHTower

open scoped TensorProduct

noncomputable section

/-- Base change of a finite separable field extension to an arbitrary domain is reduced. -/
theorem deningerFiniteSeparableBaseChange_isReduced
    {F C L : Type*} [Field F] [CommRing C] [IsDomain C] [Algebra F C]
    [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L] :
    IsReduced (C ⊗[F] L) := by
  let KC := FractionRing C
  let φ : C ⊗[F] L →ₐ[F] KC ⊗[F] L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom F C KC) (AlgHom.id F L)
  have hφ : Function.Injective φ := by
    exact TensorProduct.map_injective_of_flat_flat
      (IsScalarTower.toAlgHom F C KC).toLinearMap LinearMap.id
      (IsFractionRing.injective C KC) Function.injective_id
  haveI : IsReduced (KC ⊗[F] L) := by
    letI : Algebra.FormallyUnramified F L :=
      Algebra.FormallyUnramified.of_isSeparable F L
    apply Algebra.FormallyUnramified.isReduced_of_field KC
  exact isReduced_of_injective φ hφ

/-- Base change of an arbitrary algebraic separable field extension to a domain is reduced. -/
theorem deningerAlgebraicSeparableBaseChange_isReduced
    {F C L : Type*} [Field F] [CommRing C] [IsDomain C] [Algebra F C]
    [Field L] [Algebra F L] [Algebra.IsAlgebraic F L] [Algebra.IsSeparable F L] :
    IsReduced (C ⊗[F] L) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  letI : Field B := (Subalgebra.isField_of_algebraic B).toField
  letI : Algebra.IsIntegral F B :=
    (Subalgebra.isIntegral_iff B).mpr fun x _ =>
      isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic (x : L))
  letI : Algebra.FiniteType F B := (Subalgebra.fg_iff_finiteType B).mp hB
  letI : FiniteDimensional F B := Algebra.IsIntegral.finite
  letI : Algebra.IsSeparable F B :=
    Subalgebra.isSeparable_iff.mpr fun x _ =>
      Algebra.IsSeparable.isSeparable F (x : L)
  exact deningerFiniteSeparableBaseChange_isReduced

/-- A field tensored with a multivariate rational-function field is a domain. -/
theorem deningerFieldTensorRationalFunction_isDomain
    {F K ι : Type*} [Field F] [Field K] [Algebra F K] :
    IsDomain (K ⊗[F] FractionRing (MvPolynomial ι F)) := by
  let P := MvPolynomial ι F
  let Q := FractionRing P
  let T0 := K ⊗[F] P
  let T1 := K ⊗[F] Q
  change IsDomain T1
  let ψ : T0 →ₐ[F] T1 :=
    Algebra.TensorProduct.map (AlgHom.id F K) (IsScalarTower.toAlgHom F P Q)
  letI : Algebra T0 T1 := ψ.toAlgebra
  letI : IsScalarTower K T0 T1 :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := T0) (A := T1) (by
      apply DFunLike.ext _ _
      intro x
      change x ⊗ₜ[F] (1 : Q) = ψ (x ⊗ₜ[F] (1 : P))
      dsimp [ψ]
      rw [Algebra.TensorProduct.map_tmul]
      simp)
  have hloc : IsLocalization
      ((nonZeroDivisors P).map
        (Algebra.TensorProduct.includeRight (R := F) (A := K))) T1 := by
    refine IsLocalization.tensorProduct_tensorProduct_right F K
      (nonZeroDivisors P) Q ?_
    apply DFunLike.ext _ _
    intro x
    change ψ (1 ⊗ₜ[F] x) = 1 ⊗ₜ[F] algebraMap P Q x
    dsimp [ψ]
    rw [Algebra.TensorProduct.map_tmul]
    simp
  letI := hloc
  haveI : IsDomain T0 :=
    (MvPolynomial.algebraTensorAlgEquiv F K).toMulEquiv.isDomain _
  refine IsLocalization.isDomain_of_le_nonZeroDivisors
    (R := T0)
    (M := (nonZeroDivisors P).map
      (Algebra.TensorProduct.includeRight (R := F) (A := K))) T1 ?_
  intro z hz
  rw [Submonoid.mem_map] at hz
  rcases hz with ⟨y, hy, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := F) (A := K) : P →ₐ[F] T0) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hy)
    (hinj (hzero.trans (map_zero
      (Algebra.TensorProduct.includeRight (R := F) (A := K) : P →ₐ[F] T0)).symm))

/-- A field tensored with an essentially finite-type field extension of a perfect field is
reduced. -/
theorem deningerPerfectFieldTensorEssFiniteType_isReduced
    {F K L : Type*} [Field F] [PerfectField F] [Field K] [Algebra F K]
    [Field L] [Algebra F L] [Algebra.EssFiniteType F L] :
    IsReduced (K ⊗[F] L) := by
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField F L
  let E := IntermediateField.adjoin F (s : Set L)
  have hC : IsDomain (K ⊗[F] E) := by
    let e : FractionRing (MvPolynomial s F) ≃ₐ[F] E := by
      have hrange : Set.range ((↑) : s → L) = (s : Set L) := by
        ext x
        simp
      exact hs.1.aevalEquivField.trans
        (IntermediateField.equivOfEq (by rw [hrange]))
    letI : IsDomain (K ⊗[F] FractionRing (MvPolynomial s F)) :=
      deningerFieldTensorRationalFunction_isDomain
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[F] K) e).symm
      |>.toMulEquiv.isDomain _
  letI : IsDomain (K ⊗[F] E) := hC
  letI hAlgE : Algebra E (K ⊗[F] E) :=
    Algebra.TensorProduct.rightAlgebra
  letI : AddCommMonoid (K ⊗[F] E) := Semiring.toAddCommMonoid
  letI : SMul E (K ⊗[F] E) := hAlgE.toSMul
  letI : Module E (K ⊗[F] E) := hAlgE.toModule
  letI hAlgEL : Algebra E L := inferInstance
  letI : SMul E L := hAlgEL.toSMul
  letI : Module E L := hAlgEL.toModule
  letI hAlgEK : Algebra E (E ⊗[F] K) :=
    Algebra.TensorProduct.leftAlgebra
  letI : AddCommMonoid (E ⊗[F] K) := Semiring.toAddCommMonoid
  letI : SMul E (E ⊗[F] K) := hAlgEK.toSMul
  letI : Module E (E ⊗[F] K) := hAlgEK.toModule
  letI hAlgLK : Algebra E (L ⊗[F] K) :=
    Algebra.TensorProduct.leftAlgebra
  letI : AddCommMonoid (L ⊗[F] K) := Semiring.toAddCommMonoid
  letI : SMul E (L ⊗[F] K) := hAlgLK.toSMul
  letI : Module E (L ⊗[F] K) := hAlgLK.toModule
  letI : Algebra.IsSeparable E L := by simpa [E] using hsep
  have hred : IsReduced ((K ⊗[F] E) ⊗[E] L) :=
    deningerAlgebraicSeparableBaseChange_isReduced
      (F := E) (C := K ⊗[F] E) (L := L)
  letI : IsReduced ((K ⊗[F] E) ⊗[E] L) := hred
  let e₁ : (K ⊗[F] E) ⊗[E] L ≃ₐ[E] (E ⊗[F] K) ⊗[E] L :=
    Algebra.TensorProduct.congr
      (Algebra.TensorProduct.commRight F E K).symm (AlgEquiv.refl : L ≃ₐ[E] L)
  let e₂ : (E ⊗[F] K) ⊗[E] L ≃ₐ[E] L ⊗[E] (E ⊗[F] K) :=
    Algebra.TensorProduct.comm E (E ⊗[F] K) L
  let e₃ : L ⊗[E] (E ⊗[F] K) ≃ₐ[E] L ⊗[F] K :=
    Algebra.TensorProduct.cancelBaseChange F E E L K
  let e₄ : L ⊗[F] K ≃ₐ[F] K ⊗[F] L :=
    Algebra.TensorProduct.comm F L K
  let e : (K ⊗[F] E) ⊗[E] L ≃+* K ⊗[F] L :=
    e₁.toRingEquiv.trans <| e₂.toRingEquiv.trans <|
      e₃.toRingEquiv.trans e₄.toRingEquiv
  exact isReduced_of_injective e.symm.toRingHom (by exact e.symm.injective)

/-- Tensor products of arbitrary field extensions over a perfect field are reduced. -/
theorem deningerPerfectFieldTensor_isReduced
    {F K L : Type*} [Field F] [PerfectField F] [Field K] [Algebra F K]
    [Field L] [Algebra F L] : IsReduced (K ⊗[F] L) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  let Q := FractionRing B
  letI : Algebra.FiniteType F B := (Subalgebra.fg_iff_finiteType B).mp hB
  letI : Algebra.EssFiniteType B Q :=
    Algebra.EssFiniteType.of_isLocalization Q (nonZeroDivisors B)
  letI : Algebra.EssFiniteType F Q := Algebra.EssFiniteType.comp F B Q
  let φ : K ⊗[F] B →ₐ[F] K ⊗[F] Q :=
    Algebra.TensorProduct.map (AlgHom.id F K) (IsScalarTower.toAlgHom F B Q)
  have hφ : Function.Injective φ := by
    exact TensorProduct.map_injective_of_flat_flat
      LinearMap.id (IsScalarTower.toAlgHom F B Q).toLinearMap
      Function.injective_id (IsFractionRing.injective B Q)
  haveI : IsReduced (K ⊗[F] Q) :=
    deningerPerfectFieldTensorEssFiniteType_isReduced
  exact isReduced_of_injective φ hφ

/-- The tensor product over `ℤ` of two characteristic-zero domains is reduced. -/
theorem deningerCharZeroDomainTensorInt_isReduced
    {A B : Type*} [CommRing A] [IsDomain A] [CharZero A]
    [CommRing B] [IsDomain B] [CharZero B] : IsReduced (A ⊗[ℤ] B) := by
  let KA := FractionRing A
  let KB := FractionRing B
  letI hAlgZKA : Algebra ℤ KA := Ring.toIntAlgebra KA
  letI hModZKA : Module ℤ KA := AddCommGroup.toIntModule KA
  letI : SMul ℤ KA := hModZKA.toSMul
  letI : DistribMulAction ℤ KA := hModZKA.toDistribMulAction
  letI hAlgZKB : Algebra ℤ KB := Ring.toIntAlgebra KB
  letI hModZKB : Module ℤ KB := AddCommGroup.toIntModule KB
  letI : SMul ℤ KB := hModZKB.toSMul
  letI : DistribMulAction ℤ KB := hModZKB.toDistribMulAction
  letI hAlgQKA : Algebra ℚ KA := DivisionRing.toRatAlgebra
  letI : SMul ℚ KA := hAlgQKA.toSMul
  letI : Module ℚ KA := hAlgQKA.toModule
  letI hAlgQKB : Algebra ℚ KB := DivisionRing.toRatAlgebra
  letI : SMul ℚ KB := hAlgQKB.toSMul
  letI : Module ℚ KB := hAlgQKB.toModule
  let φ : A ⊗[ℤ] B →ₐ[ℤ] KA ⊗[ℤ] KB :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℤ A KA)
      (IsScalarTower.toAlgHom ℤ B KB)
  have hφ : Function.Injective φ := by
    exact TensorProduct.map_injective_of_flat_flat
      (IsScalarTower.toAlgHom ℤ A KA).toLinearMap
      (IsScalarTower.toAlgHom ℤ B KB).toLinearMap
      (IsFractionRing.injective A KA) (IsFractionRing.injective B KB)
  haveI : IsReduced (KA ⊗[ℤ] KB) := by
    haveI : IsReduced (KA ⊗[ℚ] KB) :=
      deningerPerfectFieldTensor_isReduced (F := ℚ) (K := KA) (L := KB)
    letI : TensorProduct.CompatibleSMul ℚ ℤ KA KB :=
      TensorProduct.CompatibleSMul.int
    let e : KA ⊗[ℚ] KB ≃ₐ[ℚ] KA ⊗[ℤ] KB :=
      Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ KA KB
    exact isReduced_of_injective e.symm.toRingHom (by exact e.symm.injective)
  exact isReduced_of_injective φ hφ

end

end RHTower
