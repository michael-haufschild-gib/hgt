import GaloisForLFunctions.RHTower.CyclicBarAlgHomMorphism
import GaloisForLFunctions.RHTower.KRealCyclicBar

/-!
# Real functoriality of the genuine cyclic bar construction

An algebra homomorphism intertwining two conjugate-linear algebra involutions
induces a Real-equivariant morphism of their genuine cyclic bar modules in all
degrees.  This is the functorial bridge needed by exact Real restriction maps;
no degree-zero or free-word replacement is used.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

universe u

variable {A B : Type u} [Ring A] [Algebra ℂ A]
  [Ring B] [Algebra ℂ B]

/-- Tensor powers of a Real-equivariant algebra homomorphism remain
Real-equivariant in every cyclic degree. -/
theorem cyclicBarAlgHomDegree_kReal
    (KA : KRealAlgebraStructure A) (KB : KRealAlgebraStructure B)
    (φ : A →ₐ[ℂ] B)
    (hφ : ∀ x, KB.sigma (φ x) = φ (KA.sigma x))
    (n : ℕ) (x : CyclicBarTensor ℂ A n) :
    (cyclicBarDegreeKReal KB n).sigma
        (cyclicBarAlgHomDegree φ n x) =
      cyclicBarAlgHomDegree φ n
        ((cyclicBarDegreeKReal KA n).sigma x) := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff r f =>
      rw [PiTensorProduct.tprodCoeff_eq_smul_tprod,
        map_smul (cyclicBarAlgHomDegree φ n), map_smulₛₗ,
        map_smulₛₗ, map_smul (cyclicBarAlgHomDegree φ n),
        cyclicBarAlgHomDegree_tprod]
      congr 1
      change kRealEvenPiTensorSigma
          (fun _ : Fin (n + 1) => KB.toKRealStructure)
          (PiTensorProduct.tprod ℂ (fun i => φ (f i))) =
        cyclicBarAlgHomDegree φ n
          (kRealEvenPiTensorSigma
            (fun _ : Fin (n + 1) => KA.toKRealStructure)
            (PiTensorProduct.tprod ℂ f))
      rw [kRealEvenPiTensorSigma_tprod,
        kRealEvenPiTensorSigma_tprod, cyclicBarAlgHomDegree_tprod]
      congr 1
      funext i
      exact hφ (f i)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Genuine all-degree Real cyclic morphism induced by a Real-equivariant
algebra homomorphism. -/
def cyclicBarAlgHomKRealHom
    (KA : KRealAlgebraStructure A) (KB : KRealAlgebraStructure B)
    (φ : A →ₐ[ℂ] B)
    (hφ : ∀ x, KB.sigma (φ x) = φ (KA.sigma x)) :
    CyclicModule.KRealHom (cyclicBarKReal KA) (cyclicBarKReal KB) where
  toHom := cyclicBarAlgHomCyclicHom φ
  real_naturality n x := cyclicBarAlgHomDegree_kReal KA KB φ hφ n x

end GaloisForLFunctions.RHTower
