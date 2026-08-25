/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraTowerRepresentation

/-!
# Split centralizer for cyclic-algebra inflation through a Galois tower

For a finite cyclic Galois tower `K ⊆ L ⊆ M`, the induced representation of
`(M/K, a ^ (q * [M:L]))` inside `End_K(M) ⊗ (L/K,a)` has a split transformation crossed
product as its commuting centralizer.  The two commuting actions have the full target dimension,
hence give an algebra equivalence

`(M/K, a ^ (q * [M:L])) ⊗ Mat_[L:K](K) ≃ End_K(M) ⊗ (L/K,a)`.

Consequently the upper and lower cyclic algebras define the same Brauer class.  This is the
explicit double-centralizer proof of compatibility between cyclic Brauer realization and genuine
inflation; no class-field-theory theorem is assumed.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

noncomputable section

noncomputable def piEndCoordinateAlgHom
    (K L ι : Type) [Field K] [Field L] [Algebra K L] :
    Module.End K L →ₐ[K] Module.End K (ι → L) where
  toFun f :=
    { toFun := fun x i ↦ f (x i)
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro c x; ext i; simp }
  map_one' := by ext x i; rfl
  map_mul' := by intro f g; ext x i; rfl
  map_zero' := by ext x i; rfl
  map_add' := by intro f g; ext x i; rfl
  commutes' := by intro c; ext x i; simp

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional L M] [FiniteDimensional K M]

noncomputable def towerBasisEquivFun :
    M ≃ₗ[K] (Fin (Module.finrank L M) → L) :=
  (Module.finBasis L M).equivFun.restrictScalars K

noncomputable def moduleEndCoordinateExtensionAlgHom :
    Module.End K L →ₐ[K] Module.End K M :=
  ((towerBasisEquivFun K L M).conjAlgEquiv K).symm.toAlgHom.comp
    (piEndCoordinateAlgHom K L (Fin (Module.finrank L M)))

omit [FiniteDimensional K M] in
theorem moduleEndCoordinateExtensionAlgHom_lmul (x : L) :
    moduleEndCoordinateExtensionAlgHom K L M (Algebra.lmul K L x) =
      Algebra.lmul K M (algebraMap L M x) := by
  classical
  apply ((towerBasisEquivFun K L M).conjAlgEquiv K).injective
  apply LinearMap.ext
  intro v
  funext i
  simp [moduleEndCoordinateExtensionAlgHom, towerBasisEquivFun,
    piEndCoordinateAlgHom, LinearEquiv.conjAlgEquiv_apply,
    ← Algebra.smul_def, Finsupp.single_apply, mul_comm]

variable [FiniteDimensional K L] [IsGalois K L] [IsGalois K M]
  [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]

noncomputable def cyclicGaloisSplitTensorTowerAlgHom (a : K) :
    (cyclicGaloisAlgebra K L 1 ⊗[K] cyclicGaloisAlgebra K L a) →ₐ[K]
      (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
  Algebra.TensorProduct.map
    ((moduleEndCoordinateExtensionAlgHom K L M).comp
      (cyclicGaloisAlgebraSplitAlgEquiv K L).toAlgHom)
    (AlgHom.id K (cyclicGaloisAlgebra K L a))

omit [FiniteDimensional K M] [IsGalois K M] [IsCyclic Gal(M/K)] in
@[simp] theorem cyclicGaloisSplitTensorTowerAlgHom_tmul_C
    (a : K) (x : L) (y : cyclicGaloisAlgebra K L a) :
    cyclicGaloisSplitTensorTowerAlgHom K L M a
        (cyclicGaloisAlgebraC K L 1 x ⊗ₜ[K] y) =
      (Algebra.lmul K M (algebraMap L M x)) ⊗ₜ[K] y := by
  change moduleEndCoordinateExtensionAlgHom K L M
      (cyclicGaloisAlgebraSplitAlgEquiv K L (cyclicGaloisAlgebraC K L 1 x)) ⊗ₜ[K] y = _
  rw [show cyclicGaloisAlgebraSplitAlgEquiv K L (cyclicGaloisAlgebraC K L 1 x) =
      Algebra.lmul K L x by exact cyclicGaloisAlgebraSplitRepresentation_C K L x]
  rw [moduleEndCoordinateExtensionAlgHom_lmul]

omit [FiniteDimensional K M] [IsGalois K M] [IsCyclic Gal(M/K)] in
@[simp] theorem cyclicGaloisSplitTensorTowerAlgHom_one_tmul
    (a : K) (y : cyclicGaloisAlgebra K L a) :
    cyclicGaloisSplitTensorTowerAlgHom K L M a (1 ⊗ₜ[K] y) = 1 ⊗ₜ[K] y := by
  simp [cyclicGaloisSplitTensorTowerAlgHom]

noncomputable def cyclicGaloisAlgebraTowerCentralizerSkewAlgHom
    (a : K) (ha : a ≠ 0) :
    SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K) →ₐ[K]
      (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
  (cyclicGaloisSplitTensorTowerAlgHom K L M a).comp
    (cyclicTensorCentralizerSkewAlgHom K L 1 a ha)

noncomputable def cyclicGaloisAlgebraTowerTensorCoefficientAlgHom (a : K) :
    L ⊗[K] L →ₐ[K]
      (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
  Algebra.TensorProduct.map
    ((Algebra.lmul K M).comp (IsScalarTower.toAlgHom K L M))
    (cyclicGaloisCoefficientAlgHom K L a)

omit [FiniteDimensional L M] [FiniteDimensional K M] [FiniteDimensional K L]
  [IsGalois K L] [IsGalois K M] [IsCyclic Gal(M/K)] in
@[simp] theorem cyclicGaloisAlgebraTowerTensorCoefficientAlgHom_tmul
    (a : K) (x y : L) :
    cyclicGaloisAlgebraTowerTensorCoefficientAlgHom K L M a (x ⊗ₜ[K] y) =
      Algebra.lmul K M (algebraMap L M x) ⊗ₜ[K]
        cyclicGaloisAlgebraC K L a y := by
  rfl

omit [IsGalois K M] [IsCyclic Gal(M/K)] in
theorem cyclicGaloisSplitTensorTowerAlgHom_tensorCoefficient
    (a : K) (t : L ⊗[K] L) :
    cyclicGaloisSplitTensorTowerAlgHom K L M a
        (cyclicGaloisTensorCoefficientAlgHom K L 1 a t) =
      cyclicGaloisAlgebraTowerTensorCoefficientAlgHom K L M a t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul x y =>
      simp only [cyclicGaloisTensorCoefficientAlgHom_tmul,
        cyclicGaloisAlgebraTowerTensorCoefficientAlgHom_tmul]
      exact cyclicGaloisSplitTensorTowerAlgHom_tmul_C K L M a x
        (cyclicGaloisAlgebraC K L a y)

noncomputable def cyclicGaloisAlgebraTowerCentralizerCoefficientAlgHom
    (a : K) :
    TransformationFunctions K Gal(L/K) →ₐ[K]
      (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
  (cyclicGaloisAlgebraTowerTensorCoefficientAlgHom K L M a).comp
    (cyclicGaloisTensorFixedCoefficientEmbedding K L)

noncomputable def cyclicGaloisAlgebraTowerCentralizerUnitAction
    (a : K) (ha : a ≠ 0) :
    Gal(L/K) →*
      (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a)ˣ :=
  (Units.map (cyclicGaloisSplitTensorTowerAlgHom K L M a).toRingHom.toMonoidHom).comp
    (cyclicTensorCentralizerUnitAction K L 1 a ha)

@[simp] theorem cyclicGaloisAlgebraTowerCentralizerSkewAlgHom_single
    (a : K) (ha : a ≠ 0) (sigma : Gal(L/K))
    (f : TransformationFunctions K Gal(L/K)) :
    cyclicGaloisAlgebraTowerCentralizerSkewAlgHom K L M a ha
        (SkewMonoidAlgebra.single sigma f) =
      cyclicGaloisAlgebraTowerCentralizerCoefficientAlgHom K L M a f *
        (cyclicGaloisAlgebraTowerCentralizerUnitAction K L M a ha sigma :
          Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) := by
  rw [cyclicGaloisAlgebraTowerCentralizerSkewAlgHom,
    AlgHom.comp_apply, cyclicTensorCentralizerSkewAlgHom_single, map_mul]
  congr 1
  · exact cyclicGaloisSplitTensorTowerAlgHom_tensorCoefficient K L M a
      (cyclicGaloisTensorFixedCoefficientEmbedding K L f)

omit [FiniteDimensional L M] [FiniteDimensional K M] [FiniteDimensional K L]
  [IsGalois K L] [IsGalois K M] [IsCyclic Gal(M/K)] in
theorem cyclicGaloisAlgebraTowerCoefficient_commute_tensorCoefficient
    (a : K) (x : M) (t : L ⊗[K] L) :
    Commute ((Algebra.lmul K M x) ⊗ₜ[K]
        (1 : cyclicGaloisAlgebra K L a))
      (cyclicGaloisAlgebraTowerTensorCoefficientAlgHom K L M a t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu =>
      rw [map_add]
      exact ht.add_right hu
  | tmul y z =>
      simp only [cyclicGaloisAlgebraTowerTensorCoefficientAlgHom_tmul]
      change
        ((Algebra.lmul K M x) ⊗ₜ[K] (1 : cyclicGaloisAlgebra K L a)) *
            (Algebra.lmul K M (algebraMap L M y) ⊗ₜ[K]
              cyclicGaloisAlgebraC K L a z) =
          (Algebra.lmul K M (algebraMap L M y) ⊗ₜ[K]
              cyclicGaloisAlgebraC K L a z) *
            ((Algebra.lmul K M x) ⊗ₜ[K] (1 : cyclicGaloisAlgebra K L a))
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      simp only [one_mul, mul_one]
      congr 1
      ext w
      simp [Module.End.mul_apply, Algebra.coe_lmul_eq_mul, mul_comm, mul_assoc]

theorem cyclicGaloisAlgebraTowerCoefficient_commute_centralizerCoefficient
    (a : K) (x : M) (f : TransformationFunctions K Gal(L/K)) :
    Commute ((Algebra.lmul K M x) ⊗ₜ[K]
        (1 : cyclicGaloisAlgebra K L a))
      (cyclicGaloisAlgebraTowerCentralizerCoefficientAlgHom K L M a f) := by
  exact cyclicGaloisAlgebraTowerCoefficient_commute_tensorCoefficient K L M a x
    (cyclicGaloisTensorFixedCoefficientEmbedding K L f)

noncomputable def cyclicGaloisAlgebraTowerCentralizerRightGenerator (a : K) :
    Module.End K M ⊗[K] cyclicGaloisAlgebra K L a :=
  1 ⊗ₜ[K] cyclicGaloisAlgebraX K L a

noncomputable def cyclicGaloisAlgebraTowerCentralizerGenerator (a : K) :
    Module.End K M ⊗[K] cyclicGaloisAlgebra K L a :=
  cyclicGaloisAlgebraTowerCentralizerCoefficientAlgHom K L M a
      (cyclicTensorCentralizerTwist K L a) *
    cyclicGaloisAlgebraTowerCentralizerRightGenerator K L M a

theorem cyclicGaloisSplitTensorTowerAlgHom_centralizerGenerator (a : K) :
    cyclicGaloisSplitTensorTowerAlgHom K L M a
        (cyclicTensorCentralizerGenerator K L 1 a) =
      cyclicGaloisAlgebraTowerCentralizerGenerator K L M a := by
  rw [cyclicTensorCentralizerGenerator, map_mul]
  congr 1
  · exact cyclicGaloisSplitTensorTowerAlgHom_tensorCoefficient K L M a
      (cyclicGaloisTensorFixedCoefficientEmbedding K L
        (cyclicTensorCentralizerTwist K L a))
  · simp [cyclicTensorCentralizerRightGenerator,
      cyclicGaloisAlgebraTowerCentralizerRightGenerator,
      cyclicGaloisSplitTensorTowerAlgHom]

@[simp] theorem cyclicGaloisAlgebraTowerCentralizerUnitAction_pow_coe
    (a : K) (ha : a ≠ 0) (m : ℕ) :
    ((cyclicGaloisAlgebraTowerCentralizerUnitAction K L M a ha
        (cyclicGaloisGenerator K L ^ m) :
      (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a)ˣ) :
        Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) =
      cyclicGaloisAlgebraTowerCentralizerGenerator K L M a ^ m := by
  change cyclicGaloisSplitTensorTowerAlgHom K L M a
      ((cyclicTensorCentralizerUnitAction K L 1 a ha
        (cyclicGaloisGenerator K L ^ m) :
          (cyclicGaloisAlgebra K L 1 ⊗[K] cyclicGaloisAlgebra K L a)ˣ) :
        cyclicGaloisAlgebra K L 1 ⊗[K] cyclicGaloisAlgebra K L a) = _
  rw [cyclicTensorCentralizerUnitAction_pow_coe, map_pow,
    cyclicGaloisSplitTensorTowerAlgHom_centralizerGenerator]

omit [Algebra L M] [IsScalarTower K L M] [FiniteDimensional L M]
  [FiniteDimensional K M] [FiniteDimensional K L] [IsGalois K L]
  [IsGalois K M] [IsCyclic Gal(M/K)] in
theorem cyclicGaloisAlgebraTowerCoefficient_commute_centralizerRightGenerator
    (a : K) (x : M) :
    Commute ((Algebra.lmul K M x) ⊗ₜ[K]
        (1 : cyclicGaloisAlgebra K L a))
      (cyclicGaloisAlgebraTowerCentralizerRightGenerator K L M a) := by
  change
    ((Algebra.lmul K M x) ⊗ₜ[K] (1 : cyclicGaloisAlgebra K L a)) *
        (1 ⊗ₜ[K] cyclicGaloisAlgebraX K L a) =
      (1 ⊗ₜ[K] cyclicGaloisAlgebraX K L a) *
        ((Algebra.lmul K M x) ⊗ₜ[K] (1 : cyclicGaloisAlgebra K L a))
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem cyclicGaloisAlgebraTowerCoefficient_commute_centralizerGenerator
    (a : K) (x : M) :
    Commute ((Algebra.lmul K M x) ⊗ₜ[K]
        (1 : cyclicGaloisAlgebra K L a))
      (cyclicGaloisAlgebraTowerCentralizerGenerator K L M a) := by
  rw [cyclicGaloisAlgebraTowerCentralizerGenerator]
  exact (cyclicGaloisAlgebraTowerCoefficient_commute_centralizerCoefficient
      K L M a x (cyclicTensorCentralizerTwist K L a)).mul_right
    (cyclicGaloisAlgebraTowerCoefficient_commute_centralizerRightGenerator K L M a x)

theorem cyclicGaloisAlgebraTowerCoefficient_commute_centralizerUnitAction
    (a : K) (ha : a ≠ 0) (x : M) (sigma : Gal(L/K)) :
    Commute ((Algebra.lmul K M x) ⊗ₜ[K]
        (1 : cyclicGaloisAlgebra K L a))
      (cyclicGaloisAlgebraTowerCentralizerUnitAction K L M a ha sigma :
        Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) := by
  let i := (cyclicGaloisGeneratorFinEquiv K L).symm sigma
  have hsigma : cyclicGaloisGenerator K L ^ (i : ℕ) = sigma :=
    (cyclicGaloisGeneratorFinEquiv K L).apply_symm_apply sigma
  rw [← hsigma, cyclicGaloisAlgebraTowerCentralizerUnitAction_pow_coe]
  exact (cyclicGaloisAlgebraTowerCoefficient_commute_centralizerGenerator
    K L M a x).pow_right _

theorem cyclicGaloisAlgebraTowerCoefficient_commute_centralizerSkew
    (a : K) (ha : a ≠ 0) (x : M)
    (F : SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :
    Commute ((Algebra.lmul K M x) ⊗ₜ[K]
        (1 : cyclicGaloisAlgebra K L a))
      (cyclicGaloisAlgebraTowerCentralizerSkewAlgHom K L M a ha F) := by
  classical
  induction F using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add F G hF hG =>
      rw [map_add]
      exact hF.add_right hG
  | single sigma f =>
      rw [cyclicGaloisAlgebraTowerCentralizerSkewAlgHom_single]
      exact (cyclicGaloisAlgebraTowerCoefficient_commute_centralizerCoefficient
        K L M a x f).mul_right
          (cyclicGaloisAlgebraTowerCoefficient_commute_centralizerUnitAction
            K L M a ha x sigma)

theorem cyclicGaloisGenerator_apply_algebraMap_tower (x : L) :
    (cyclicGaloisGenerator K M) (algebraMap L M x) =
      algebraMap L M
        ((cyclicGaloisGenerator K L ^
          (cyclicGaloisRestrictionOrientation K L M).val) x) := by
  rw [← AlgEquiv.restrictNormal_commutes (cyclicGaloisGenerator K M) L x]
  exact congrArg (fun sigma : Gal(L/K) => algebraMap L M (sigma x))
    (cyclicGaloisRestrictionOrientation_spec K L M)

theorem cyclicGaloisAlgebraTowerGenerator_covariant_tensor
    (a : K) (t : L ⊗[K] L) :
    cyclicGaloisAlgebraTowerGeneratorAction K L M a *
        cyclicGaloisAlgebraTowerTensorCoefficientAlgHom K L M a t =
      cyclicGaloisAlgebraTowerTensorCoefficientAlgHom K L M a
          (Algebra.TensorProduct.map
            (cyclicGaloisGenerator K L ^
              (cyclicGaloisRestrictionOrientation K L M).val).toAlgHom
            (cyclicGaloisGenerator K L ^
              (cyclicGaloisRestrictionOrientation K L M).val).toAlgHom t) *
        cyclicGaloisAlgebraTowerGeneratorAction K L M a := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp [map_add, mul_add, add_mul, ht, hu]
  | tmul x y =>
      simp only [cyclicGaloisAlgebraTowerGeneratorAction,
        cyclicGaloisAlgebraTowerTensorCoefficientAlgHom_tmul,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      apply congrArg₂ (fun u v => u ⊗ₜ[K] v)
      · ext z
        simp [Module.End.mul_apply, Algebra.coe_lmul_eq_mul,
          cyclicGaloisGenerator_apply_algebraMap_tower K L M,
          map_mul]
      · let q := (cyclicGaloisRestrictionOrientation K L M).val
        have hpow : (cyclicGaloisGenerator K L ^ q) y =
            ((cyclicGaloisGenerator K L).toRingEquiv ^ q) y := by
          induction q generalizing y with
          | zero => rfl
          | succ q ih =>
              rw [pow_succ, pow_succ]
              exact ih ((cyclicGaloisGenerator K L) y)
        dsimp [q] at hpow
        calc
          cyclicGaloisAlgebraX K L a ^
                (cyclicGaloisRestrictionOrientation K L M).val *
              cyclicGaloisAlgebraC K L a y =
            cyclicGaloisAlgebraC K L a
                (((cyclicGaloisGenerator K L).toRingEquiv ^
                  (cyclicGaloisRestrictionOrientation K L M).val) y) *
              cyclicGaloisAlgebraX K L a ^
                (cyclicGaloisRestrictionOrientation K L M).val :=
            cyclicAlgebraX_pow_mul_C
              (cyclicGaloisGenerator K L).toRingEquiv
              (Module.finrank K L) (algebraMap K L a) y q
          _ = cyclicGaloisAlgebraC K L a
                ((cyclicGaloisGenerator K L ^
                  (cyclicGaloisRestrictionOrientation K L M).val) y) *
              cyclicGaloisAlgebraX K L a ^
                (cyclicGaloisRestrictionOrientation K L M).val := by rw [hpow]

theorem cyclicGaloisAlgebraTowerGenerator_commute_centralizerCoefficient
    (a : K) (f : TransformationFunctions K Gal(L/K)) :
    Commute (cyclicGaloisAlgebraTowerGeneratorAction K L M a)
      (cyclicGaloisAlgebraTowerCentralizerCoefficientAlgHom K L M a f) := by
  change cyclicGaloisAlgebraTowerGeneratorAction K L M a *
      cyclicGaloisAlgebraTowerTensorCoefficientAlgHom K L M a
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f) =
    cyclicGaloisAlgebraTowerTensorCoefficientAlgHom K L M a
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f) *
      cyclicGaloisAlgebraTowerGeneratorAction K L M a
  rw [cyclicGaloisAlgebraTowerGenerator_covariant_tensor,
    cyclicGaloisTensorFixedCoefficientEmbedding_map_diagonal]

theorem cyclicGaloisAlgebraTowerGenerator_commute_centralizerRightGenerator
    (a : K) :
    Commute (cyclicGaloisAlgebraTowerGeneratorAction K L M a)
      (cyclicGaloisAlgebraTowerCentralizerRightGenerator K L M a) := by
  rw [cyclicGaloisAlgebraTowerGeneratorAction,
    cyclicGaloisAlgebraTowerCentralizerRightGenerator]
  exact (Commute.one_right (cyclicGaloisGenerator K M).toLinearMap).tmul
    (Commute.self_pow (cyclicGaloisAlgebraX K L a)
      (cyclicGaloisRestrictionOrientation K L M).val).symm

theorem cyclicGaloisAlgebraTowerGenerator_commute_centralizerGenerator
    (a : K) :
    Commute (cyclicGaloisAlgebraTowerGeneratorAction K L M a)
      (cyclicGaloisAlgebraTowerCentralizerGenerator K L M a) := by
  rw [cyclicGaloisAlgebraTowerCentralizerGenerator]
  exact (cyclicGaloisAlgebraTowerGenerator_commute_centralizerCoefficient K L M a
      (cyclicTensorCentralizerTwist K L a)).mul_right
    (cyclicGaloisAlgebraTowerGenerator_commute_centralizerRightGenerator K L M a)

theorem cyclicGaloisAlgebraTowerGenerator_commute_centralizerUnitAction
    (a : K) (ha : a ≠ 0) (sigma : Gal(L/K)) :
    Commute (cyclicGaloisAlgebraTowerGeneratorAction K L M a)
      (cyclicGaloisAlgebraTowerCentralizerUnitAction K L M a ha sigma :
        Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) := by
  let i := (cyclicGaloisGeneratorFinEquiv K L).symm sigma
  have hsigma : cyclicGaloisGenerator K L ^ (i : ℕ) = sigma :=
    (cyclicGaloisGeneratorFinEquiv K L).apply_symm_apply sigma
  rw [← hsigma, cyclicGaloisAlgebraTowerCentralizerUnitAction_pow_coe]
  exact (cyclicGaloisAlgebraTowerGenerator_commute_centralizerGenerator
    K L M a).pow_right _

theorem cyclicGaloisAlgebraTowerGenerator_commute_centralizerSkew
    (a : K) (ha : a ≠ 0)
    (F : SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :
    Commute (cyclicGaloisAlgebraTowerGeneratorAction K L M a)
      (cyclicGaloisAlgebraTowerCentralizerSkewAlgHom K L M a ha F) := by
  classical
  induction F using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add F G hF hG =>
      rw [map_add]
      exact hF.add_right hG
  | single sigma f =>
      rw [cyclicGaloisAlgebraTowerCentralizerSkewAlgHom_single]
      exact (cyclicGaloisAlgebraTowerGenerator_commute_centralizerCoefficient
        K L M a f).mul_right
          (cyclicGaloisAlgebraTowerGenerator_commute_centralizerUnitAction
            K L M a ha sigma)

theorem cyclicGaloisAlgebraTowerRepresentationAlgHom_commute_centralizerSkew
    (a : K) (ha : a ≠ 0)
    (x : cyclicGaloisAlgebra K M
      (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)))
    (F : SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :
    Commute (cyclicGaloisAlgebraTowerRepresentationAlgHom K L M a x)
      (cyclicGaloisAlgebraTowerCentralizerSkewAlgHom K L M a ha F) := by
  classical
  obtain ⟨v, rfl⟩ :=
    cyclicGaloisAlgebraNormalFormLinearMap_surjective K M
      (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) x
  rw [cyclicGaloisAlgebraNormalFormLinearMap_apply, map_sum]
  apply Finset.sum_induction
    (fun i : Fin (Module.finrank K M) =>
      cyclicGaloisAlgebraTowerRepresentationAlgHom K L M a
        (cyclicGaloisAlgebraC K M
            (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))
            (v i) *
          cyclicGaloisAlgebraX K M
            (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) ^
              (i : ℕ)))
    (fun z => Commute z
      (cyclicGaloisAlgebraTowerCentralizerSkewAlgHom K L M a ha F))
  · intro u w hu hw
    exact hu.add_left hw
  · simp
  · intro i _
    rw [map_mul]
    have hpow :
        cyclicGaloisAlgebraTowerRepresentationAlgHom K L M a
            (cyclicGaloisAlgebraX K M
              (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) ^
                (i : ℕ)) =
          cyclicGaloisAlgebraTowerRepresentationAlgHom K L M a
              (cyclicGaloisAlgebraX K M
                (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))) ^
            (i : ℕ) := map_pow
              (cyclicGaloisAlgebraTowerRepresentationAlgHom K L M a)
              (cyclicGaloisAlgebraX K M
                (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)))
              (i : ℕ)
    rw [hpow]
    have hC :
        cyclicGaloisAlgebraTowerRepresentationAlgHom K L M a
            (cyclicGaloisAlgebraC K M
              (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))
              (v i)) =
          (Algebra.lmul K M (v i)) ⊗ₜ[K] 1 :=
      cyclicGaloisAlgebraTowerRepresentation_C K L M a (v i)
    have hX :
        cyclicGaloisAlgebraTowerRepresentationAlgHom K L M a
            (cyclicGaloisAlgebraX K M
              (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))) =
          cyclicGaloisAlgebraTowerGeneratorAction K L M a :=
      cyclicGaloisAlgebraTowerRepresentation_X K L M a
    rw [hC, hX]
    exact (cyclicGaloisAlgebraTowerCoefficient_commute_centralizerSkew
      K L M a ha (v i) F).mul_left
        ((cyclicGaloisAlgebraTowerGenerator_commute_centralizerSkew
          K L M a ha F).pow_left (i : ℕ))

noncomputable def cyclicGaloisAlgebraTowerCentralizerProductAlgHom
    (a : K) (ha : a ≠ 0) :
    (cyclicGaloisAlgebra K M
        (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) ⊗[K]
      SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) →ₐ[K]
        (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
  Algebra.TensorProduct.lift
    (cyclicGaloisAlgebraTowerRepresentationAlgHom K L M a)
    (cyclicGaloisAlgebraTowerCentralizerSkewAlgHom K L M a ha)
    (cyclicGaloisAlgebraTowerRepresentationAlgHom_commute_centralizerSkew
      K L M a ha)

theorem cyclicGaloisAlgebraTowerCentralizerProductAlgHom_injective
    (a : K) (ha : a ≠ 0) :
    Function.Injective
      (cyclicGaloisAlgebraTowerCentralizerProductAlgHom K L M a ha) := by
  classical
  let p := a ^
    ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)
  have hp : p ≠ 0 := pow_ne_zero _ ha
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L a).symm⟩
  letI : Nontrivial (Module.End K M) := inferInstance
  letI : Nontrivial
      (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) := inferInstance
  letI : IsSimpleRing
      (cyclicGaloisAlgebra K M p ⊗[K]
        SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :=
    tensorProduct_isSimpleRing (cyclicGaloisAlgebraCSA K M p hp)
      (transformationSkewCSA K Gal(L/K))
  let sourceRing : NonAssocRing
      (cyclicGaloisAlgebra K M p ⊗[K]
        SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) := inferInstance
  letI : NonAssocSemiring
      (cyclicGaloisAlgebra K M p ⊗[K]
        SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :=
    sourceRing.toNonAssocSemiring
  let f :
      (cyclicGaloisAlgebra K M p ⊗[K]
        SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) →+*
      (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
    { toFun := cyclicGaloisAlgebraTowerCentralizerProductAlgHom K L M a ha
      map_one' := (cyclicGaloisAlgebraTowerCentralizerProductAlgHom K L M a ha).map_one
      map_mul' := (cyclicGaloisAlgebraTowerCentralizerProductAlgHom K L M a ha).map_mul
      map_zero' := (cyclicGaloisAlgebraTowerCentralizerProductAlgHom K L M a ha).map_zero
      map_add' := (cyclicGaloisAlgebraTowerCentralizerProductAlgHom K L M a ha).map_add }
  change Function.Injective f
  exact RingHom.injective f

theorem cyclicGaloisAlgebraTowerCentralizerProduct_finrank_eq (a : K) :
    Module.finrank K
        (cyclicGaloisAlgebra K M
            (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) ⊗[K]
          SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) =
      Module.finrank K
        (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) := by
  classical
  have hcard : Fintype.card Gal(L/K) = Module.finrank K L := by
    simpa using (Fintype.card_congr (cyclicGaloisGeneratorFinEquiv K L)).symm
  calc
    Module.finrank K
        (cyclicGaloisAlgebra K M
            (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) ⊗[K]
          SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) =
      Module.finrank K (cyclicGaloisAlgebra K M
          (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))) *
        Module.finrank K
          (SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :=
        Module.finrank_tensorProduct
    _ = Module.finrank K M ^ 2 * Fintype.card Gal(L/K) ^ 2 := by
      rw [cyclicGaloisAlgebra_finrank_eq_square,
        transformationSkew_finrank_eq_card_sq]
    _ = Module.finrank K M ^ 2 * Module.finrank K L ^ 2 := by rw [hcard]
    _ = Module.finrank K (Module.End K M) *
        Module.finrank K (cyclicGaloisAlgebra K L a) := by
      rw [Module.finrank_linearMap, cyclicGaloisAlgebra_finrank_eq_square, pow_two]
    _ = Module.finrank K
        (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
      Module.finrank_tensorProduct.symm

theorem cyclicGaloisAlgebraTowerCentralizerProductAlgHom_surjective
    (a : K) (ha : a ≠ 0) :
    Function.Surjective
      (cyclicGaloisAlgebraTowerCentralizerProductAlgHom K L M a ha) := by
  classical
  letI : FiniteDimensional K
      (SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :=
    (transformationSkewCSA K Gal(L/K)).fin_dim
  have hinj :=
    cyclicGaloisAlgebraTowerCentralizerProductAlgHom_injective K L M a ha
  let f :=
    (cyclicGaloisAlgebraTowerCentralizerProductAlgHom K L M a ha).toLinearMap
  change Function.Surjective f
  have hinj' : Function.Injective f := hinj
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := K)
    (V := cyclicGaloisAlgebra K M
        (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) ⊗[K]
      SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K))
    (V₂ := Module.End K M ⊗[K] cyclicGaloisAlgebra K L a)
    (f := f)
    (cyclicGaloisAlgebraTowerCentralizerProduct_finrank_eq K L M a)).mp hinj'

noncomputable def cyclicGaloisAlgebraTowerCentralizerProductAlgEquiv
    (a : K) (ha : a ≠ 0) :
    (cyclicGaloisAlgebra K M
        (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) ⊗[K]
      SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) ≃ₐ[K]
        (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
  AlgEquiv.ofBijective
    (cyclicGaloisAlgebraTowerCentralizerProductAlgHom K L M a ha)
    ⟨cyclicGaloisAlgebraTowerCentralizerProductAlgHom_injective K L M a ha,
      cyclicGaloisAlgebraTowerCentralizerProductAlgHom_surjective K L M a ha⟩

noncomputable def cyclicGaloisAlgebraTowerBrauerProductAlgEquiv
    (a : K) (ha : a ≠ 0) :
    (cyclicGaloisAlgebra K M
        (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) ⊗[K]
      SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) ≃ₐ[K]
        (Matrix (Fin (Module.finrank K M)) (Fin (Module.finrank K M)) K ⊗[K]
          cyclicGaloisAlgebra K L a) :=
  (cyclicGaloisAlgebraTowerCentralizerProductAlgEquiv K L M a ha).trans
    (Algebra.TensorProduct.congr
      (LinearMap.toMatrixAlgEquiv (Module.finBasis K M)) (AlgEquiv.refl))

theorem cyclicGaloisAlgebra_brauerClass_tower_inflation
    (a : K) (ha : a ≠ 0) :
    brauerClass (cyclicGaloisAlgebraCSA K M
        (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))
        (pow_ne_zero _ ha)) =
      brauerClass (cyclicGaloisAlgebraCSA K L a ha) := by
  classical
  letI : NeZero (Module.finrank K M) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := M))⟩
  calc
    brauerClass (cyclicGaloisAlgebraCSA K M
        (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))
        (pow_ne_zero _ ha)) =
      brauerTensorAdd K
        (brauerClass (cyclicGaloisAlgebraCSA K M
          (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))
          (pow_ne_zero _ ha)))
        (brauerSplitClass K) :=
      (brauerTensorAdd_split_right K _).symm
    _ = brauerTensorAdd K
        (brauerClass (cyclicGaloisAlgebraCSA K M
          (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))
          (pow_ne_zero _ ha)))
        (brauerClass (transformationSkewCSA K Gal(L/K))) := by
      rw [transformationSkew_brauerClass_eq_split]
    _ = brauerClass (tensorProductCSA
        (cyclicGaloisAlgebraCSA K M
          (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))
          (pow_ne_zero _ ha))
        (transformationSkewCSA K Gal(L/K))) :=
      brauerTensorAdd_brauerClass K _ _
    _ = brauerClass (tensorProductCSA
        (matrixFinCSA (scalarCSA K) (Module.finrank K M))
        (cyclicGaloisAlgebraCSA K L a ha)) :=
      brauerClass_eq_of_algEquiv _ _
        (cyclicGaloisAlgebraTowerBrauerProductAlgEquiv K L M a ha)
    _ = brauerTensorAdd K
        (brauerClass (matrixFinCSA (scalarCSA K) (Module.finrank K M)))
        (brauerClass (cyclicGaloisAlgebraCSA K L a ha)) := rfl
    _ = brauerTensorAdd K (brauerSplitClass K)
        (brauerClass (cyclicGaloisAlgebraCSA K L a ha)) := by
      rw [brauerClass_matrixFinCSA_scalar_eq]
    _ = brauerClass (cyclicGaloisAlgebraCSA K L a ha) :=
      brauerTensorAdd_split_left K _

end
end GaloisForLFunctions.HTGeometry.ABHN
