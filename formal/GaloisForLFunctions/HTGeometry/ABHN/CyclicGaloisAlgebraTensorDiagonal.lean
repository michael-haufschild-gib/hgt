import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaTensorProduct

/-!
# Diagonal cyclic algebra inside a tensor product

For two cyclic Galois algebras with the same defining extension and parameters `a` and `b`, the
tensor product contains the cyclic algebra with parameter `a * b`.  Coefficients enter through the
left factor and the cyclic generator maps to the tensor product of the two generators.

This is the explicit diagonal inclusion used in the standard proof of cyclic Brauer additivity.
The remaining Morita step is to identify its centralizer as split.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- Powers of a pure tensor are the pure tensors of the powers. -/
theorem cyclicTensorProduct_tmul_pow
    {K A B : Type*} [CommSemiring K] [Semiring A] [Semiring B]
    [Algebra K A] [Algebra K B] (x : A) (y : B) (n : ℕ) :
    (x ⊗ₜ[K] y) ^ n = (x ^ n) ⊗ₜ[K] (y ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, Algebra.TensorProduct.one_def]
  | succ n ih =>
      rw [pow_succ, pow_succ, pow_succ, ih, Algebra.TensorProduct.tmul_mul_tmul]

/-- Coefficients for the diagonal cyclic algebra enter through the first tensor factor. -/
noncomputable def cyclicGaloisAlgebraTensorDiagonalCoefficientRingHom
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    (a b : K) :
    L →+* (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) :=
  (Algebra.TensorProduct.includeLeft (R := K) (S := K)
    (A := cyclicGaloisAlgebra K L a) (B := cyclicGaloisAlgebra K L b)).toRingHom.comp
    (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a))

/-- Diagonal cyclic generator in the tensor product. -/
noncomputable def cyclicGaloisAlgebraTensorDiagonalGenerator
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    (a b : K) : cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b :=
  cyclicGaloisAlgebraX K L a ⊗ₜ[K] cyclicGaloisAlgebraX K L b

/-- The diagonal generator implements the chosen Galois action on coefficients. -/
theorem cyclicGaloisAlgebraTensorDiagonal_comm
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    (a b : K) (m : Multiplicative ℕ) (x : L) :
    cyclicGaloisAlgebraTensorDiagonalCoefficientRingHom K L a b
          ((cyclicPowerRingAut (cyclicGaloisGenerator K L).toRingEquiv) m x) *
        cyclicPowerMonoidHom (cyclicGaloisAlgebraTensorDiagonalGenerator K L a b) m =
      cyclicPowerMonoidHom (cyclicGaloisAlgebraTensorDiagonalGenerator K L a b) m *
        cyclicGaloisAlgebraTensorDiagonalCoefficientRingHom K L a b x := by
  dsimp only [cyclicGaloisAlgebraTensorDiagonalCoefficientRingHom,
    cyclicGaloisAlgebraTensorDiagonalGenerator, cyclicPowerRingAut, cyclicPowerMonoidHom]
  change (cyclicGaloisAlgebraC K L a
        (((cyclicGaloisGenerator K L).toRingEquiv ^ Multiplicative.toAdd m) x) ⊗ₜ[K] 1) *
      (cyclicGaloisAlgebraX K L a ⊗ₜ[K] cyclicGaloisAlgebraX K L b) ^
          Multiplicative.toAdd m =
    (cyclicGaloisAlgebraX K L a ⊗ₜ[K] cyclicGaloisAlgebraX K L b) ^
          Multiplicative.toAdd m *
      (cyclicGaloisAlgebraC K L a x ⊗ₜ[K] 1)
  rw [cyclicTensorProduct_tmul_pow]
  change
    (cyclicGaloisAlgebraC K L a
          (((cyclicGaloisGenerator K L).toRingEquiv ^ Multiplicative.toAdd m) x) ⊗ₜ[K] 1) *
        ((cyclicGaloisAlgebraX K L a ^ Multiplicative.toAdd m) ⊗ₜ[K]
          (cyclicGaloisAlgebraX K L b ^ Multiplicative.toAdd m)) =
      ((cyclicGaloisAlgebraX K L a ^ Multiplicative.toAdd m) ⊗ₜ[K]
          (cyclicGaloisAlgebraX K L b ^ Multiplicative.toAdd m)) *
        (cyclicGaloisAlgebraC K L a x ⊗ₜ[K] 1)
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rw [cyclicAlgebraX_pow_mul_C]
  simp

/-- The diagonal generator has parameter `a * b`. -/
theorem cyclicGaloisAlgebraTensorDiagonal_pow
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    (a b : K) :
    cyclicGaloisAlgebraTensorDiagonalGenerator K L a b ^ Module.finrank K L =
      cyclicGaloisAlgebraTensorDiagonalCoefficientRingHom K L a b
        (algebraMap K L (a * b)) := by
  rw [cyclicGaloisAlgebraTensorDiagonalGenerator, cyclicTensorProduct_tmul_pow,
    cyclicGaloisAlgebraX_pow, cyclicGaloisAlgebraX_pow]
  change
    cyclicGaloisAlgebraC K L a (algebraMap K L a) ⊗ₜ[K]
        cyclicGaloisAlgebraC K L b (algebraMap K L b) =
      cyclicGaloisAlgebraC K L a (algebraMap K L (a * b)) ⊗ₜ[K] 1
  rw [← cyclicGaloisAlgebra_algebraMap_apply,
    ← cyclicGaloisAlgebra_algebraMap_apply,
    ← cyclicGaloisAlgebra_algebraMap_apply]
  rw [show (algebraMap K (cyclicGaloisAlgebra K L b)) b =
      b • (1 : cyclicGaloisAlgebra K L b) by simp [Algebra.smul_def]]
  rw [TensorProduct.tmul_smul]
  apply congrArg (fun z : cyclicGaloisAlgebra K L a =>
    z ⊗ₜ[K] (1 : cyclicGaloisAlgebra K L b))
  rw [Algebra.smul_def, ← map_mul, mul_comm b a]

/-- Ring homomorphism from the product-parameter cyclic algebra into the tensor product. -/
noncomputable def cyclicGaloisAlgebraTensorDiagonalRingHom
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    (a b : K) : cyclicGaloisAlgebra K L (a * b) →+*
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) :=
  cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L (a * b))
    (cyclicGaloisAlgebraTensorDiagonalCoefficientRingHom K L a b)
    (cyclicGaloisAlgebraTensorDiagonalGenerator K L a b)
    (cyclicGaloisAlgebraTensorDiagonal_comm K L a b)
    (cyclicGaloisAlgebraTensorDiagonal_pow K L a b)

/-- The diagonal ring homomorphism sends coefficients into the left tensor factor. -/
theorem cyclicGaloisAlgebraTensorDiagonalRingHom_C
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    (a b : K) (c : L) :
    cyclicGaloisAlgebraTensorDiagonalRingHom K L a b
        (cyclicGaloisAlgebraC K L (a * b) c) =
      cyclicGaloisAlgebraC K L a c ⊗ₜ[K] 1 := by
  exact cyclicAlgebraLift_C _ _ _ _ _ _ _ c

/-- The diagonal ring homomorphism sends the generator to the tensor of the generators. -/
theorem cyclicGaloisAlgebraTensorDiagonalRingHom_X
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    (a b : K) :
    cyclicGaloisAlgebraTensorDiagonalRingHom K L a b
        (cyclicGaloisAlgebraX K L (a * b)) =
      cyclicGaloisAlgebraX K L a ⊗ₜ[K] cyclicGaloisAlgebraX K L b := by
  exact cyclicAlgebraLift_X _ _ _ _ _ _ _

/-- The diagonal cyclic inclusion as a base-field algebra homomorphism. -/
noncomputable def cyclicGaloisAlgebraTensorDiagonalAlgHom
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    (a b : K) : cyclicGaloisAlgebra K L (a * b) →ₐ[K]
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) :=
  AlgHom.mk' (cyclicGaloisAlgebraTensorDiagonalRingHom K L a b) (by
    intro c x
    simp only [Algebra.smul_def, map_mul]
    congr 1
    rw [cyclicGaloisAlgebra_algebraMap_apply,
      cyclicGaloisAlgebraTensorDiagonalRingHom_C]
    rfl)

/-- For nonzero product parameter, the diagonal cyclic inclusion is injective. -/
theorem cyclicGaloisAlgebraTensorDiagonalAlgHom_injective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a b : K) (hab : a * b ≠ 0) :
    Function.Injective (cyclicGaloisAlgebraTensorDiagonalAlgHom K L a b) := by
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L a).symm⟩
  letI : Nontrivial (cyclicGaloisAlgebra K L b) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L b).symm⟩
  letI : Nontrivial
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) := inferInstance
  letI : IsSimpleRing (cyclicGaloisAlgebra K L (a * b)) :=
    isSimpleRing_cyclicGaloisAlgebra_of_nonzero K L (a * b) hab
  exact RingHom.injective _

end GaloisForLFunctions.HTGeometry.ABHN
