import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraSplit
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Galois decomposition of a tensor square

For a finite cyclic Galois extension `L/K`, this file constructs the canonical decomposition

`L ⊗[K] L ≃ₐ[L] (Gal(L/K) → L)`,

sending `x ⊗ y` to the function `σ ↦ x * σ y`.  Bijectivity is proved from linear independence
of distinct Galois automorphisms.  This is the coefficient decomposition needed to identify the
split centralizer in the cyclic-algebra tensor-product formula.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- Canonical Galois evaluation map on the tensor square. -/
noncomputable def cyclicGaloisTensorToPi :
    L ⊗[K] L →ₐ[L] (Gal(L/K) → L) :=
  Algebra.TensorProduct.lift
    (AlgHom.pi (fun _ : Gal(L/K) => AlgHom.id L L))
    (AlgHom.pi (fun σ : Gal(L/K) => σ.toAlgHom))
    (by
      intro x y
      exact Commute.all _ _)

omit [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] in
/-- The canonical Galois evaluation map on pure tensors. -/
@[simp]
theorem cyclicGaloisTensorToPi_tmul (x y : L) (σ : Gal(L/K)) :
    cyclicGaloisTensorToPi K L (x ⊗ₜ[K] y) σ = x * σ y := by
  rfl

/-- The transpose of Galois evaluation is injective.  Its kernel would give an `L`-linear
dependence among the distinct Galois automorphisms. -/
theorem cyclicGaloisTensorToPi_dual_injective :
    Function.Injective (cyclicGaloisTensorToPi K L).toLinearMap.dualMap := by
  classical
  intro φ ψ hφψ
  suffices hzero : (cyclicGaloisTensorToPi K L).toLinearMap.dualMap (φ - ψ) = 0 by
    have hcoeff : ∀ σ : Gal(L/K),
        (φ - ψ) ((Pi.basisFun L Gal(L/K)) σ) = 0 := by
      have hrelation :
          (∑ σ : Gal(L/K),
              (φ - ψ) ((Pi.basisFun L Gal(L/K)) σ) • σ.toLinearMap) = 0 := by
        apply LinearMap.ext
        intro y
        have hy := congrArg
          (fun q : Module.Dual L (L ⊗[K] L) => q (1 ⊗ₜ[K] y)) hzero
        have htensor : (cyclicGaloisTensorToPi K L).toLinearMap (1 ⊗ₜ[K] y) =
            (fun σ : Gal(L/K) => σ y) := by
          ext σ
          simp
        have hy' : (φ - ψ) (fun σ : Gal(L/K) => σ y) = 0 := by
          rw [LinearMap.dualMap_apply, LinearMap.zero_apply, htensor] at hy
          exact hy
        have hexpand : (fun σ : Gal(L/K) => σ y) =
            ∑ σ : Gal(L/K), (σ y) • (Pi.basisFun L Gal(L/K)) σ := by
          calc
            (fun σ : Gal(L/K) => σ y) =
                (Pi.basisFun L Gal(L/K)).equivFun.symm
                  (fun σ : Gal(L/K) => σ y) := by
              rw [Pi.basisFun_equivFun]
              rfl
            _ = ∑ σ : Gal(L/K), (σ y) •
                (Pi.basisFun L Gal(L/K)) σ :=
              (Pi.basisFun L Gal(L/K)).equivFun_symm_apply _
        rw [LinearMap.sum_apply Finset.univ]
        simp only [LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul]
        calc
          ∑ σ : Gal(L/K), (φ - ψ) ((Pi.basisFun L Gal(L/K)) σ) * σ y =
              ∑ σ : Gal(L/K), σ y *
                (φ - ψ) ((Pi.basisFun L Gal(L/K)) σ) := by
            apply Finset.sum_congr rfl
            intro σ _
            rw [mul_comm]
          _ = (φ - ψ)
              (∑ σ : Gal(L/K), (σ y) • (Pi.basisFun L Gal(L/K)) σ) := by
            simp only [map_sum, map_smul, smul_eq_mul]
          _ = (φ - ψ) (fun σ : Gal(L/K) => σ y) := by rw [← hexpand]
          _ = 0 := hy'
      intro σ
      have hbasis (τ : Gal(L/K)) :
          cyclicGaloisAlgebraSplitEndBasis K L τ = τ.toLinearMap := by
        simp only [cyclicGaloisAlgebraSplitEndBasis,
          coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply]
        rfl
      simp_rw [← hbasis] at hrelation
      have hcoordinate := congrArg
        (fun f : Module.End K L =>
          (cyclicGaloisAlgebraSplitEndBasis K L).repr f σ) hrelation
      simp only [map_sum, map_smul, map_zero,
        (cyclicGaloisAlgebraSplitEndBasis K L).repr_self,
        Finsupp.smul_single] at hcoordinate
      simpa only [map_sum, Finset.sum_apply', Finsupp.single_apply,
        Finsupp.smul_single', smul_eq_mul, mul_one, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Pi.zero_apply, Finsupp.zero_apply] using hcoordinate
    have hdiff : φ - ψ = 0 := by
      apply (Pi.basisFun L Gal(L/K)).ext
      intro σ
      exact hcoeff σ
    exact sub_eq_zero.mp hdiff
  rw [map_sub, hφψ, sub_self]

/-- Galois evaluation is surjective. -/
theorem cyclicGaloisTensorToPi_surjective :
    Function.Surjective (cyclicGaloisTensorToPi K L) := by
  exact LinearMap.dualMap_injective_iff.mp
    (cyclicGaloisTensorToPi_dual_injective K L)

/-- **Galois tensor decomposition.** A finite cyclic Galois tensor square is the product of one
copy of `L` for each Galois automorphism. -/
noncomputable def cyclicGaloisTensorPiAlgEquiv :
    L ⊗[K] L ≃ₐ[L] (Gal(L/K) → L) :=
  AlgEquiv.ofBijective (cyclicGaloisTensorToPi K L)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        rw [Module.finrank_tensorProduct, Module.finrank_pi_fintype]
        calc
          Module.finrank L L * Module.finrank K L = Module.finrank K L := by
            rw [Module.finrank_self, one_mul]
          _ = Fintype.card Gal(L/K) := by
            rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
          _ = ∑ _ : Gal(L/K), Module.finrank L L := by
            rw [Module.finrank_self, Finset.sum_const, nsmul_eq_mul, mul_one]
            rfl)).mpr (cyclicGaloisTensorToPi_surjective K L),
      cyclicGaloisTensorToPi_surjective K L⟩

/-- Acting on the right tensor factor translates the Galois coordinate. -/
theorem cyclicGaloisTensorToPi_map_right
    (z : L ⊗[K] L) (σ τ : Gal(L/K)) :
    cyclicGaloisTensorToPi K L
        (Algebra.TensorProduct.map (AlgHom.id K L) σ.toAlgHom z) τ =
      cyclicGaloisTensorToPi K L z (τ * σ) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        cyclicGaloisTensorToPi_tmul]
      rfl

/-- Acting by the same cyclic Galois automorphism on both tensor factors acts pointwise on the
Galois-coordinate values. -/
theorem cyclicGaloisTensorToPi_map_diagonal
    (z : L ⊗[K] L) (σ τ : Gal(L/K)) :
    cyclicGaloisTensorToPi K L
        (Algebra.TensorProduct.map σ.toAlgHom σ.toAlgHom z) τ =
      σ (cyclicGaloisTensorToPi K L z τ) := by
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, cyclicGaloisTensorToPi_tmul, map_mul]
      congr 1
      change (τ * σ) y = (σ * τ) y
      exact congrArg (fun g : Gal(L/K) => g y) (mul_comm τ σ)

/-- Embed `K`-valued functions on the cyclic Galois group as the diagonal-fixed part of the
Galois tensor square. -/
noncomputable def cyclicGaloisTensorFixedCoefficientEmbedding :
    (Gal(L/K) → K) →ₐ[K] L ⊗[K] L :=
  (cyclicGaloisTensorPiAlgEquiv K L).symm.toAlgHom.restrictScalars K |>.comp
    (AlgHom.pi (fun σ : Gal(L/K) =>
      (Algebra.ofId K L).comp (Pi.evalAlgHom K (fun _ : Gal(L/K) => K) σ)))

/-- Galois coordinates of an embedded fixed coefficient are its scalar-valued coordinates. -/
@[simp]
theorem cyclicGaloisTensorFixedCoefficientEmbedding_toPi
    (f : Gal(L/K) → K) (σ : Gal(L/K)) :
    cyclicGaloisTensorToPi K L (cyclicGaloisTensorFixedCoefficientEmbedding K L f) σ =
      algebraMap K L (f σ) := by
  change cyclicGaloisTensorPiAlgEquiv K L
      ((cyclicGaloisTensorPiAlgEquiv K L).symm
        ((AlgHom.pi (fun τ : Gal(L/K) =>
          (Algebra.ofId K L).comp (Pi.evalAlgHom K (fun _ : Gal(L/K) => K) τ))) f)) σ = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- The diagonal-fixed coefficient embedding is faithful. -/
theorem cyclicGaloisTensorFixedCoefficientEmbedding_injective :
    Function.Injective (cyclicGaloisTensorFixedCoefficientEmbedding K L) := by
  intro f g hfg
  apply funext
  intro σ
  apply (algebraMap K L).injective
  have hcoordinate := congrArg
    (fun z : L ⊗[K] L => cyclicGaloisTensorToPi K L z σ) hfg
  simpa using hcoordinate

/-- Embedded scalar-valued functions are fixed by the diagonal cyclic Galois action. -/
theorem cyclicGaloisTensorFixedCoefficientEmbedding_map_diagonal
    (f : Gal(L/K) → K) (σ : Gal(L/K)) :
    Algebra.TensorProduct.map σ.toAlgHom σ.toAlgHom
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f) =
      cyclicGaloisTensorFixedCoefficientEmbedding K L f := by
  apply (cyclicGaloisTensorPiAlgEquiv K L).injective
  ext τ
  change cyclicGaloisTensorToPi K L
      (Algebra.TensorProduct.map σ.toAlgHom σ.toAlgHom
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f)) τ =
    cyclicGaloisTensorToPi K L
      (cyclicGaloisTensorFixedCoefficientEmbedding K L f) τ
  rw [cyclicGaloisTensorToPi_map_diagonal]
  simp

/-- Right-factor Galois action translates the embedded function coordinates. -/
theorem cyclicGaloisTensorFixedCoefficientEmbedding_map_right
    (f : Gal(L/K) → K) (σ : Gal(L/K)) :
    Algebra.TensorProduct.map (AlgHom.id K L) σ.toAlgHom
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f) =
      cyclicGaloisTensorFixedCoefficientEmbedding K L (fun τ => f (τ * σ)) := by
  apply (cyclicGaloisTensorPiAlgEquiv K L).injective
  ext τ
  change cyclicGaloisTensorToPi K L
      (Algebra.TensorProduct.map (AlgHom.id K L) σ.toAlgHom
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f)) τ =
    cyclicGaloisTensorToPi K L
      (cyclicGaloisTensorFixedCoefficientEmbedding K L (fun υ => f (υ * σ))) τ
  rw [cyclicGaloisTensorToPi_map_right]
  rw [cyclicGaloisTensorFixedCoefficientEmbedding_toPi,
    cyclicGaloisTensorFixedCoefficientEmbedding_toPi]

end GaloisForLFunctions.HTGeometry.ABHN
