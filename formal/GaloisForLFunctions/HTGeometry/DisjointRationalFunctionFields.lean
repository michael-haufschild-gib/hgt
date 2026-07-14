import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Disjoint rational-function fields

This file isolates the standard commutative-algebra input used by the prime-tail field-building
construction.  Polynomial rings on disjoint variable sets tensor to the polynomial ring on the
disjoint union.  Localizing successively at the two sets of nonzero polynomials therefore shows
that the tensor product of the corresponding rational-function fields is a domain.

The final theorem records the exact common-base meet supplied by linear disjointness.  It is the
load-bearing field-intersection statement: no transcendence-degree count is used in its place.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A multivariate rational-function field tensored with a polynomial ring on a disjoint variable
set is a domain.  No finiteness assumption is made on either variable set. -/
theorem isDomain_fractionRing_mvPolynomial_tensor_mvPolynomial
    {F ι κ : Type*} [Field F] :
    IsDomain (FractionRing (MvPolynomial ι F) ⊗[F] MvPolynomial κ F) := by
  let PX := MvPolynomial ι F
  let PY := MvPolynomial κ F
  let KX := FractionRing PX
  let T0 := PX ⊗[F] PY
  let T1 := KX ⊗[F] PY
  change IsDomain T1
  let φ : T0 →ₐ[F] T1 :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom F PX KX) (AlgHom.id F PY)
  letI : Algebra T0 T1 := φ.toAlgebra
  letI : IsScalarTower PX T0 T1 :=
    IsScalarTower.of_algebraMap_eq' (R := PX) (S := T0) (A := T1) (by
      apply DFunLike.ext _ _
      intro x
      change (algebraMap PX KX x) ⊗ₜ[F] (1 : PY) =
        φ (x ⊗ₜ[F] (1 : PY))
      dsimp [φ]
      rw [Algebra.TensorProduct.map_tmul]
      simp)
  have hloc : IsLocalization
      (Algebra.algebraMapSubmonoid T0 (nonZeroDivisors PX)) T1 := by
    refine IsLocalization.tensorProduct_tensorProduct F PY (nonZeroDivisors PX) KX ?_
    apply DFunLike.ext _ _
    intro x
    change φ (1 ⊗ₜ[F] x) = 1 ⊗ₜ[F] x
    dsimp [φ]
    rw [Algebra.TensorProduct.map_tmul]
    simp
  letI := hloc
  haveI hT0 : IsDomain T0 :=
    (MvPolynomial.tensorEquivSum F ι κ F).toMulEquiv.isDomain
  refine IsLocalization.isDomain_of_le_nonZeroDivisors
    (R := T0) (M := Algebra.algebraMapSubmonoid T0 (nonZeroDivisors PX)) T1 ?_
  intro z hz
  change z ∈ Submonoid.map (algebraMap PX T0) (nonZeroDivisors PX) at hz
  rw [Submonoid.mem_map] at hz
  rcases hz with ⟨x, hx, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  have hinj : Function.Injective (algebraMap PX T0) := by
    change Function.Injective (Algebra.TensorProduct.includeLeft : PX →ₐ[F] T0)
    exact Algebra.TensorProduct.includeLeft_injective (algebraMap F PY).injective
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hx)
    (hinj (by simpa using hzero))

/-- Rational-function fields on two arbitrary disjoint variable sets have domain tensor product.
Equivalently, there is no tensor zero divisor introduced by passing from either polynomial block
to its fraction field. -/
theorem isDomain_fractionRing_mvPolynomial_tensor_fractionRing_mvPolynomial
    {F ι κ : Type*} [Field F] :
    IsDomain (FractionRing (MvPolynomial ι F) ⊗[F]
      FractionRing (MvPolynomial κ F)) := by
  let PX := MvPolynomial ι F
  let PY := MvPolynomial κ F
  let KX := FractionRing PX
  let KY := FractionRing PY
  let T1 := KX ⊗[F] PY
  let T2 := KX ⊗[F] KY
  change IsDomain T2
  let ψ : T1 →ₐ[F] T2 :=
    Algebra.TensorProduct.map (AlgHom.id F KX) (IsScalarTower.toAlgHom F PY KY)
  letI : Algebra T1 T2 := ψ.toAlgebra
  letI : IsScalarTower KX T1 T2 :=
    IsScalarTower.of_algebraMap_eq' (R := KX) (S := T1) (A := T2) (by
      apply DFunLike.ext _ _
      intro x
      change x ⊗ₜ[F] (1 : KY) = ψ (x ⊗ₜ[F] (1 : PY))
      dsimp [ψ]
      rw [Algebra.TensorProduct.map_tmul]
      simp)
  have hloc : IsLocalization
      ((nonZeroDivisors PY).map
        (Algebra.TensorProduct.includeRight (R := F) (A := KX))) T2 := by
    refine IsLocalization.tensorProduct_tensorProduct_right F KX
      (nonZeroDivisors PY) KY ?_
    apply DFunLike.ext _ _
    intro x
    change ψ (1 ⊗ₜ[F] x) = 1 ⊗ₜ[F] algebraMap PY KY x
    dsimp [ψ]
    rw [Algebra.TensorProduct.map_tmul]
    simp
  letI := hloc
  haveI hT1 : IsDomain T1 :=
    isDomain_fractionRing_mvPolynomial_tensor_mvPolynomial
      (F := F) (ι := ι) (κ := κ)
  refine IsLocalization.isDomain_of_le_nonZeroDivisors
    (R := T1)
    (M := (nonZeroDivisors PY).map
      (Algebra.TensorProduct.includeRight (R := F) (A := KX))) T2 ?_
  intro z hz
  rw [Submonoid.mem_map] at hz
  rcases hz with ⟨y, hy, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := F) (A := KX) : PY →ₐ[F] T1) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F KX).injective
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hy)
    (hinj (hzero.trans (map_zero
      (Algebra.TensorProduct.includeRight (R := F) (A := KX) : PY →ₐ[F] T1)).symm))

/-- The fraction-field map induced by an injective renaming of variables. -/
def mvFractionRename {F σ τ : Type*} [Field F]
    (e : σ → τ) (he : Function.Injective e) :
    FractionRing (MvPolynomial σ F) →ₐ[F]
      FractionRing (MvPolynomial τ F) := by
  let g : MvPolynomial σ F →ₐ[F] FractionRing (MvPolynomial τ F) :=
    (IsScalarTower.toAlgHom F (MvPolynomial τ F)
      (FractionRing (MvPolynomial τ F))).comp (MvPolynomial.rename e)
  exact IsFractionRing.liftAlgHom (g := g)
    ((IsFractionRing.injective (MvPolynomial τ F)
      (FractionRing (MvPolynomial τ F))).comp (MvPolynomial.rename_injective e he))

@[simp]
theorem mvFractionRename_algebraMap {F σ τ : Type*} [Field F]
    (e : σ → τ) (he : Function.Injective e) (x : MvPolynomial σ F) :
    mvFractionRename e he (algebraMap _ _ x) =
      algebraMap (MvPolynomial τ F) (FractionRing (MvPolynomial τ F))
        (MvPolynomial.rename e x) := by
  simp [mvFractionRename, IsFractionRing.liftAlgHom_apply,
    IsFractionRing.lift_algebraMap]

set_option maxHeartbeats 800000 in
/-- The canonical product map from rational functions in two disjoint variable blocks into the
rational-function field on their disjoint union is injective.  This identifies the actual
embeddings, not merely an abstract pair of isomorphic rational fields. -/
theorem canonicalRationalProductMap_injective
    {F ι κ : Type*} [Field F] :
    let PX := MvPolynomial ι F
    let PY := MvPolynomial κ F
    let KX := FractionRing PX
    let KY := FractionRing PY
    let PXY := MvPolynomial (ι ⊕ κ) F
    let KXY := FractionRing PXY
    let fx : KX →ₐ[F] KXY := mvFractionRename Sum.inl Sum.inl_injective
    let fy : KY →ₐ[F] KXY := mvFractionRename Sum.inr Sum.inr_injective
    Function.Injective (Algebra.TensorProduct.productMap fx fy) := by
  dsimp only
  let PX := MvPolynomial ι F
  let PY := MvPolynomial κ F
  let KX := FractionRing PX
  let KY := FractionRing PY
  let PXY := MvPolynomial (ι ⊕ κ) F
  let KXY := FractionRing PXY
  let T0 := PX ⊗[F] PY
  let T1 := KX ⊗[F] PY
  let T2 := KX ⊗[F] KY
  let e0 : T0 ≃ₐ[F] PXY := MvPolynomial.tensorEquivSum F ι κ F
  let g0 : T0 →ₐ[F] KXY :=
    (IsScalarTower.toAlgHom F PXY KXY).comp e0.toAlgHom
  let fx : KX →ₐ[F] KXY := mvFractionRename Sum.inl Sum.inl_injective
  let fy : KY →ₐ[F] KXY := mvFractionRename Sum.inr Sum.inr_injective
  let μ : T2 →ₐ[F] KXY := Algebra.TensorProduct.productMap fx fy
  let φ : T0 →ₐ[F] T1 :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom F PX KX) (AlgHom.id F PY)
  let ψ : T1 →ₐ[F] T2 :=
    Algebra.TensorProduct.map (AlgHom.id F KX) (IsScalarTower.toAlgHom F PY KY)
  let ω : T0 →ₐ[F] T2 := ψ.comp φ
  letI : Algebra T0 T1 := φ.toAlgebra
  letI : IsScalarTower PX T0 T1 :=
    IsScalarTower.of_algebraMap_eq' (R := PX) (S := T0) (A := T1) (by
      apply DFunLike.ext _ _
      intro x
      change (algebraMap PX KX x) ⊗ₜ[F] (1 : PY) = φ (x ⊗ₜ[F] (1 : PY))
      dsimp [φ]
      rw [Algebra.TensorProduct.map_tmul]
      simp)
  have hloc1 : IsLocalization
      (Algebra.algebraMapSubmonoid T0 (nonZeroDivisors PX)) T1 := by
    refine IsLocalization.tensorProduct_tensorProduct F PY (nonZeroDivisors PX) KX ?_
    apply DFunLike.ext _ _
    intro x
    change φ (1 ⊗ₜ[F] x) = 1 ⊗ₜ[F] x
    dsimp [φ]
    rw [Algebra.TensorProduct.map_tmul]
    simp
  letI := hloc1
  letI : Algebra T1 T2 := ψ.toAlgebra
  letI : IsScalarTower KX T1 T2 :=
    IsScalarTower.of_algebraMap_eq' (R := KX) (S := T1) (A := T2) (by
      apply DFunLike.ext _ _
      intro x
      change x ⊗ₜ[F] (1 : KY) = ψ (x ⊗ₜ[F] (1 : PY))
      dsimp [ψ]
      rw [Algebra.TensorProduct.map_tmul]
      simp)
  let N : Submonoid T1 := (nonZeroDivisors PY).map
    (Algebra.TensorProduct.includeRight (R := F) (A := KX))
  have hloc2 : IsLocalization N T2 := by
    dsimp [N]
    refine IsLocalization.tensorProduct_tensorProduct_right F KX
      (nonZeroDivisors PY) KY ?_
    apply DFunLike.ext _ _
    intro x
    change ψ (1 ⊗ₜ[F] x) = 1 ⊗ₜ[F] algebraMap PY KY x
    dsimp [ψ]
    rw [Algebra.TensorProduct.map_tmul]
    simp
  letI := hloc2
  letI : Algebra T0 T2 := ω.toAlgebra
  letI : IsScalarTower T0 T1 T2 :=
    IsScalarTower.of_algebraMap_eq' (R := T0) (S := T1) (A := T2) rfl
  let M : Submonoid T0 := Algebra.algebraMapSubmonoid T0 (nonZeroDivisors PX)
  let Mtot : Submonoid T0 := IsLocalization.localizationLocalizationSubmodule M N
  have hlocTot : IsLocalization Mtot T2 := by
    dsimp [Mtot]
    exact IsLocalization.localization_localization_isLocalization M N T2
  letI := hlocTot
  have hg0 : Function.Injective g0 :=
    (IsFractionRing.injective PXY KXY).comp e0.injective
  have homega_left (x : PX) :
      ω (x ⊗ₜ[F] (1 : PY)) = algebraMap PX KX x ⊗ₜ[F] (1 : KY) := by
    change ψ (φ (x ⊗ₜ[F] (1 : PY))) = _
    have hφ : φ (x ⊗ₜ[F] (1 : PY)) =
        algebraMap PX KX x ⊗ₜ[F] (1 : PY) := by
      dsimp [φ]
      rw [Algebra.TensorProduct.map_tmul]
      simp
    rw [hφ]
    dsimp [ψ]
    rw [Algebra.TensorProduct.map_tmul]
    simp
  have homega_right (y : PY) :
      ω ((1 : PX) ⊗ₜ[F] y) = (1 : KX) ⊗ₜ[F] algebraMap PY KY y := by
    change ψ (φ ((1 : PX) ⊗ₜ[F] y)) = _
    have hφ : φ ((1 : PX) ⊗ₜ[F] y) = (1 : KX) ⊗ₜ[F] y := by
      dsimp [φ]
      rw [Algebra.TensorProduct.map_tmul]
      simp
    rw [hφ]
    dsimp [ψ]
    rw [Algebra.TensorProduct.map_tmul]
    simp
  have hmu_left (x : KX) : μ (x ⊗ₜ[F] (1 : KY)) = fx x :=
    Algebra.TensorProduct.productMap_left_apply fx fy x
  have hmu_right (y : KY) : μ ((1 : KX) ⊗ₜ[F] y) = fy y :=
    Algebra.TensorProduct.productMap_right_apply fx fy y
  have hcomp : μ.toRingHom.comp (algebraMap T0 T2) = g0.toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply MvPolynomial.ringHom_ext <;> intro x
      · change μ (ω (MvPolynomial.C x ⊗ₜ[F] (1 : PY))) =
          g0 (MvPolynomial.C x ⊗ₜ[F] (1 : PY))
        rw [homega_left, hmu_left, mvFractionRename_algebraMap]
        dsimp [g0, e0]
        rw [MvPolynomial.rename_C]
        exact congrArg (algebraMap PXY KXY)
          (MvPolynomial.tensorEquivSum_C_tmul_one
            (R := F) (σ := ι) (ι := κ) (S := F) x).symm
      · change μ (ω (MvPolynomial.X x ⊗ₜ[F] (1 : PY))) =
          g0 (MvPolynomial.X x ⊗ₜ[F] (1 : PY))
        rw [homega_left, hmu_left, mvFractionRename_algebraMap]
        dsimp [g0, e0]
        rw [MvPolynomial.rename_X]
        exact congrArg (algebraMap PXY KXY)
          (MvPolynomial.tensorEquivSum_X_tmul_one
            (R := F) (σ := ι) (ι := κ) (S := F) x).symm
    · apply MvPolynomial.ringHom_ext <;> intro y
      · change μ (ω ((1 : PX) ⊗ₜ[F] MvPolynomial.C y)) =
          g0 ((1 : PX) ⊗ₜ[F] MvPolynomial.C y)
        rw [homega_right, hmu_right, mvFractionRename_algebraMap]
        dsimp [g0, e0]
        rw [MvPolynomial.rename_C]
        have he : (MvPolynomial.tensorEquivSum F ι κ F)
            ((1 : PX) ⊗ₜ[F] MvPolynomial.C y) = MvPolynomial.C y := by
          simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
            (MvPolynomial.tensorEquivSum_one_tmul_C
              (R := F) (σ := ι) (ι := κ) (S := F) y)
        exact congrArg (algebraMap PXY KXY) he.symm
      · change μ (ω ((1 : PX) ⊗ₜ[F] MvPolynomial.X y)) =
          g0 ((1 : PX) ⊗ₜ[F] MvPolynomial.X y)
        rw [homega_right, hmu_right, mvFractionRename_algebraMap]
        dsimp [g0, e0]
        rw [MvPolynomial.rename_X]
        have he : (MvPolynomial.tensorEquivSum F ι κ F)
            ((1 : PX) ⊗ₜ[F] MvPolynomial.X y) =
              MvPolynomial.X (Sum.inr y) :=
          MvPolynomial.tensorEquivSum_one_tmul_X
            (R := F) (σ := ι) (ι := κ) (S := F) y
        exact congrArg (algebraMap PXY KXY) he.symm
  change Function.Injective μ.toRingHom
  apply (IsLocalization.injective_iff_map_algebraMap_eq Mtot μ.toRingHom).2
  intro x y
  constructor
  · intro h
    exact congrArg μ h
  · intro h
    apply congrArg (algebraMap T0 T2)
    apply hg0
    exact (DFunLike.congr_fun hcomp x).symm.trans
      (h.trans (DFunLike.congr_fun hcomp y))

/-- The two canonical rational-function subfields in the rational field on a disjoint union are
linearly disjoint. -/
theorem canonicalRationalFieldRanges_linearDisjoint
    {F ι κ : Type*} [Field F] :
    let KX := FractionRing (MvPolynomial ι F)
    let KY := FractionRing (MvPolynomial κ F)
    let KXY := FractionRing (MvPolynomial (ι ⊕ κ) F)
    let fx : KX →ₐ[F] KXY := mvFractionRename Sum.inl Sum.inl_injective
    let fy : KY →ₐ[F] KXY := mvFractionRename Sum.inr Sum.inr_injective
    fx.fieldRange.LinearDisjoint fy.fieldRange := by
  dsimp only
  let KX := FractionRing (MvPolynomial ι F)
  let KY := FractionRing (MvPolynomial κ F)
  let KXY := FractionRing (MvPolynomial (ι ⊕ κ) F)
  let fx : KX →ₐ[F] KXY := mvFractionRename Sum.inl Sum.inl_injective
  let fy : KY →ₐ[F] KXY := mvFractionRename Sum.inr Sum.inr_injective
  have hprod : Function.Injective (Algebra.TensorProduct.productMap fx fy) :=
    canonicalRationalProductMap_injective (F := F) (ι := ι) (κ := κ)
  rw [IntermediateField.linearDisjoint_iff']
  rw [Subalgebra.linearDisjoint_iff_injective]
  let ex : KX ≃ₐ[F] fx.range := AlgEquiv.ofInjective fx fx.injective
  let ey : KY ≃ₐ[F] fy.range := AlgEquiv.ofInjective fy fy.injective
  let e : KX ⊗[F] KY ≃ₐ[F] fx.range ⊗[F] fy.range :=
    Algebra.TensorProduct.congr ex ey
  have hmul :
      (fx.fieldRange.mulMap fy.fieldRange.toSubalgebra).toRingHom.comp e.toRingHom =
        (Algebra.TensorProduct.productMap fx fy).toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply DFunLike.ext _ _
      intro x
      rfl
    · apply DFunLike.ext _ _
      intro y
      rfl
  intro u v huv
  obtain ⟨u', rfl⟩ := e.surjective u
  obtain ⟨v', rfl⟩ := e.surjective v
  apply congrArg e
  apply hprod
  exact (DFunLike.congr_fun hmul u').symm.trans
    (huv.trans (DFunLike.congr_fun hmul v'))

/-- Exact meet law above a common intermediate field.  If two extensions of `K` inside `E` are
linearly disjoint over `K`, then after both are viewed over the original field `F`, their
intersection is exactly `K`. -/
theorem restrictScalars_inf_eq_commonBase_of_linearDisjoint
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (A B : IntermediateField K E)
    (h : A.LinearDisjoint B) :
    A.restrictScalars F ⊓ B.restrictScalars F = K := by
  rw [IntermediateField.restrictScalars_inf, h.inf_eq_bot,
    IntermediateField.restrictScalars_bot_eq_self]

/-- Adjoin form of the common-base meet law. -/
theorem restrictScalars_adjoin_inf_eq_commonBase_of_linearDisjoint
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (S T : Set E)
    (h : (IntermediateField.adjoin K S).LinearDisjoint
      (IntermediateField.adjoin K T)) :
    (IntermediateField.adjoin K S).restrictScalars F ⊓
      (IntermediateField.adjoin K T).restrictScalars F = K :=
  restrictScalars_inf_eq_commonBase_of_linearDisjoint K _ _ h

end

end GaloisForLFunctions.HTGeometry
