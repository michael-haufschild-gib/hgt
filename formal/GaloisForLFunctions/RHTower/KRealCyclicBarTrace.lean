import GaloisForLFunctions.RHTower.KRealCyclicBar
import GaloisForLFunctions.RHTower.KRealStructureRealization
import GaloisForLFunctions.RHTower.CyclicBarTraceMorphism

/-!
# Real-equivariant trace augmentations of cyclic bars

A Real-equivariant trace on a Real algebra induces a Real-equivariant morphism from its genuine
cyclic bar construction to the constant scalar cyclic module.  The proof first establishes that
ordered multiplication of every indexed tensor power commutes with the componentwise Real action.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

/-- Complex conjugation in every degree of the constant scalar cyclic module. -/
def scalarConstantCyclicKReal :
    CyclicModule.KReal false (scalarConstantCyclicModule (R := ℂ)) where
  real _ := kRealConjugation
  face_naturality _ _ _ := rfl
  degeneracy_naturality _ _ _ := rfl
  cyclic_naturality _ _ := rfl

/-- Ordered multiplication of a genuine cyclic-bar tensor commutes with its Real action. -/
theorem cyclicBarTotalProduct_kReal
    {A : Type} [Ring A] [Algebra ℂ A]
    (K : KRealAlgebraStructure A) :
    ∀ (n : ℕ) (x : CyclicBarTensor ℂ A n),
      K.sigma (cyclicBarTotalProduct n x) =
        cyclicBarTotalProduct n ((cyclicBarDegreeKReal K n).sigma x) := by
  intro n
  induction n with
  | zero =>
      intro x
      induction x using PiTensorProduct.induction_on' with
      | tprodCoeff r f =>
          change K.sigma
              (cyclicBarDegreeZeroProduct
                (PiTensorProduct.tprodCoeff ℂ r f)) =
            cyclicBarDegreeZeroProduct
              (kRealEvenPiTensorSigma
                (fun _ : Fin 1 => K.toKRealStructure)
                (PiTensorProduct.tprodCoeff ℂ r f))
          rw [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul,
            cyclicBarDegreeZeroProduct_tprod, map_smulₛₗ,
            map_smulₛₗ, map_smul, kRealEvenPiTensorSigma_tprod,
            cyclicBarDegreeZeroProduct_tprod]
      | add x y hx hy => simp only [map_add, hx, hy]
  | succ n ih =>
      intro x
      change K.sigma
          (cyclicBarTotalProduct n (cyclicBarFace (0 : Fin (n + 2)) x)) =
        cyclicBarTotalProduct n
          (cyclicBarFace (0 : Fin (n + 2))
            ((cyclicBarDegreeKReal K (n + 1)).sigma x))
      rw [ih, cyclicBarDegreeKReal_face K]

/-- Every degree of a Real-equivariant trace augmentation commutes with conjugation. -/
theorem cyclicBarTraceAugmentation_kReal
    {A : Type} [Ring A] [Algebra ℂ A]
    (K : KRealAlgebraStructure A) (τ : A →ₗ[ℂ] ℂ)
    (hτ : ∀ a, τ (K.sigma a) = star (τ a))
    (n : ℕ) (x : CyclicBarTensor ℂ A n) :
    star (cyclicBarTraceAugmentation τ n x) =
      cyclicBarTraceAugmentation τ n ((cyclicBarDegreeKReal K n).sigma x) := by
  change star (τ (cyclicBarTotalProduct n x)) =
    τ (cyclicBarTotalProduct n ((cyclicBarDegreeKReal K n).sigma x))
  rw [← hτ, cyclicBarTotalProduct_kReal]

/-- A Real-equivariant trace induces a morphism of Real cyclic modules. -/
def cyclicBarTraceKRealHom
    {A : Type} [Ring A] [Algebra ℂ A]
    (K : KRealAlgebraStructure A) (τ : A →ₗ[ℂ] ℂ)
    (htrace : ∀ a b, τ (a * b) = τ (b * a))
    (hτ : ∀ a, τ (K.sigma a) = star (τ a)) :
    CyclicModule.KRealHom (cyclicBarKReal K) scalarConstantCyclicKReal where
  toHom := cyclicBarTraceCyclicHom τ htrace
  real_naturality n x := cyclicBarTraceAugmentation_kReal K τ hτ n x

end GaloisForLFunctions.RHTower
