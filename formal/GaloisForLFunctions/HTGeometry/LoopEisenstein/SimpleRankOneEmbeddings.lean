import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineSL2Embedding

/-!
# Rank-one embeddings with the simple-root orientations

Swapping the two standard coordinates reverses the diagonal coroot and
exchanges upper and lower roots. Applied to the shifted affine embedding,
this sends the standard positive root to the lower root of degree one.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

private theorem sl2_weyl_conj_upper (s : F) :
    MulAut.conj (sl2WeylLower (1 : Fˣ)) (sl2Upper s) = sl2Lower (-s) := by
  rw [MulAut.conj_apply, sl2WeylLower_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2WeylLower, sl2Upper, sl2Lower, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem sl2_weyl_conj_lower (s : F) :
    MulAut.conj (sl2WeylLower (1 : Fˣ)) (sl2Lower s) = sl2Upper (-s) := by
  rw [MulAut.conj_apply, sl2WeylLower_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2WeylLower, sl2Upper, sl2Lower, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem sl2_weyl_conj_diagonal (a : Fˣ) :
    MulAut.conj (sl2WeylLower (1 : Fˣ)) (sl2Diagonal a) = sl2Diagonal a⁻¹ := by
  rw [MulAut.conj_apply, sl2WeylLower_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2WeylLower, sl2Diagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Coordinate swap, including the sign correction to the determinant-one Weyl matrix. -/
def sl2Swap : SL2 F →* SL2 F :=
  (sl2Rescale (-1 : Fˣ)).comp (MulAut.conj (sl2WeylLower (1 : Fˣ))).toMonoidHom

@[simp] theorem coe_sl2Swap (g : SL2 F) :
    (sl2Swap F g : Matrix (Fin 2) (Fin 2) F) = !![g 1 1, g 1 0; g 0 1, g 0 0] := by
  change (sl2Rescale (-1 : Fˣ)
    (MulAut.conj (sl2WeylLower (1 : Fˣ)) g) : Matrix (Fin 2) (Fin 2) F) = _
  rw [MulAut.conj_apply, sl2WeylLower_inv, coe_sl2Rescale]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2WeylLower, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem sl2Swap_involutive : Function.Involutive (sl2Swap F) := by
  intro g
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Swap]

theorem sl2Swap_injective : Function.Injective (sl2Swap F) :=
  (sl2Rescale_injective _).comp (MulAut.conj (sl2WeylLower (1 : Fˣ))).injective

@[simp] theorem sl2Swap_upper (s : F) : sl2Swap F (sl2Upper s) = sl2Lower s := by
  change sl2Rescale (-1 : Fˣ) (MulAut.conj (sl2WeylLower (1 : Fˣ)) (sl2Upper s)) = _
  rw [sl2_weyl_conj_upper, sl2Rescale_lower]
  simp

@[simp] theorem sl2Swap_lower (s : F) : sl2Swap F (sl2Lower s) = sl2Upper s := by
  change sl2Rescale (-1 : Fˣ) (MulAut.conj (sl2WeylLower (1 : Fˣ)) (sl2Lower s)) = _
  rw [sl2_weyl_conj_lower, sl2Rescale_upper]
  simp

@[simp] theorem sl2Swap_diagonal (a : Fˣ) :
    sl2Swap F (sl2Diagonal a) = sl2Diagonal a⁻¹ := by
  change sl2Rescale (-1 : Fˣ) (MulAut.conj (sl2WeylLower (1 : Fˣ)) (sl2Diagonal a)) = _
  rw [sl2_weyl_conj_diagonal, sl2Rescale_diagonal]

namespace LoopSL2

/-- The affine simple embedding with positive root at degree one and coroot `h₀`. -/
def affineSimpleSL2Embedding : SL2 F →* LoopSL2 F :=
  (affineSL2Embedding F).comp (sl2Swap F)

@[simp] theorem projection_affineSimpleSL2Embedding (g : SL2 F) :
    projection F (affineSimpleSL2Embedding F g) = affineConstantSL2Map F (sl2Swap F g) := rfl

theorem affineSimpleSL2Embedding_injective : Function.Injective (affineSimpleSL2Embedding F) :=
  (affineSL2Embedding_injective F).comp (sl2Swap_injective F)

@[simp] theorem affineSimpleSL2Embedding_upper (s : F) :
    affineSimpleSL2Embedding F (sl2Upper s) =
      lowerRoot F (Multiplicative.ofAdd (affineLowerParameter F s)) := by
  change affineSL2Embedding F (sl2Swap F (sl2Upper s)) = _
  rw [sl2Swap_upper, affineSL2Embedding_lower]

@[simp] theorem affineSimpleSL2Embedding_lower (s : F) :
    affineSimpleSL2Embedding F (sl2Lower s) =
      upperRoot F (Multiplicative.ofAdd (affineUpperParameter F s)) := by
  change affineSL2Embedding F (sl2Swap F (sl2Lower s)) = _
  rw [sl2Swap_lower, affineSL2Embedding_upper]

@[simp] theorem affineSimpleSL2Embedding_diagonal (a : Fˣ) :
    affineSimpleSL2Embedding F (sl2Diagonal a) = affineCoroot F a := by
  change affineSL2Embedding F (sl2Swap F (sl2Diagonal a)) = _
  rw [sl2Swap_diagonal, affineSL2Embedding_diagonal, inv_inv]

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
