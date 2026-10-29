import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineSL2Kubota

/-!
# The affine simple rank-one subgroup

The corrected Kubota section is multiplicative on both elementary root
subgroups. Four-factor generation extends these identities to an injective
homomorphism from the entire coefficient-field SL₂.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

namespace LoopSL2

/-- The affine matrix embedding with its exact multiplicative central correction. -/
def affineSL2Section (g : SL2 F) : LoopSL2 F :=
  ⟨affineConstantSL2Map F g, Additive.ofMul (affineSL2Correction F g)⟩

@[simp] theorem projection_affineSL2Section (g : SL2 F) :
    projection F (affineSL2Section F g) = affineConstantSL2Map F g := rfl

@[simp] theorem affineSL2Section_one : affineSL2Section F 1 = 1 := by
  apply SL2SymbolExtension.ext
  · exact map_one _
  · change Additive.ofMul (affineSL2Correction F 1) = 0
    rw [affineSL2Correction_one]
    rfl

@[simp] theorem affineSL2Section_upper (s : F) :
    affineSL2Section F (sl2Upper s) =
      upperRoot F (Multiplicative.ofAdd (affineUpperParameter F s)) := by
  apply SL2SymbolExtension.ext
  · exact affineConstantSL2Map_upper F s
  · change Additive.ofMul (affineSL2Correction F (sl2Upper s)) = 0
    rw [affineSL2Correction_upper]
    rfl

@[simp] theorem affineSL2Section_lower (s : F) :
    affineSL2Section F (sl2Lower s) =
      lowerRoot F (Multiplicative.ofAdd (affineLowerParameter F s)) := by
  apply SL2SymbolExtension.ext
  · exact affineConstantSL2Map_lower F s
  · change Additive.ofMul (affineSL2Correction F (sl2Lower s)) = 0
    rw [affineSL2Correction_lower]
    rfl

@[simp] theorem affineSL2Section_mul_upper (g : SL2 F) (s : F) :
    affineSL2Section F (g * sl2Upper s) =
      affineSL2Section F g * upperRoot F (Multiplicative.ofAdd (affineUpperParameter F s)) := by
  apply SL2SymbolExtension.ext
  · change affineConstantSL2Map F (g * sl2Upper s) =
      affineConstantSL2Map F g * sl2Upper (affineUpperParameter F s)
    rw [map_mul, affineConstantSL2Map_upper]
  · change Additive.ofMul (affineSL2Correction F (g * sl2Upper s)) =
      Additive.ofMul (affineSL2Correction F g) + 0 +
        laurentTameHom F (kubotaCocycle (affineConstantSL2Map F g)
          (sl2Upper (affineUpperParameter F s)))
    rw [affineSL2Correction_mul_upper, kubotaCocycle_mul_upper, map_zero, add_zero, add_zero]

@[simp] theorem affineSL2Section_mul_lower (g : SL2 F) (s : F) :
    affineSL2Section F (g * sl2Lower s) =
      affineSL2Section F g * lowerRoot F (Multiplicative.ofAdd (affineLowerParameter F s)) := by
  apply SL2SymbolExtension.ext
  · change affineConstantSL2Map F (g * sl2Lower s) =
      affineConstantSL2Map F g * sl2Lower (affineLowerParameter F s)
    rw [map_mul, affineConstantSL2Map_lower]
  · change Additive.ofMul (affineSL2Correction F (g * sl2Lower s)) =
      Additive.ofMul (affineSL2Correction F g) + 0 +
        laurentTameHom F (kubotaCocycle (affineConstantSL2Map F g)
          (sl2Lower (affineLowerParameter F s)))
    rw [← affineConstantSL2Map_lower, ← affineSL2KubotaFactor_eq,
      affineSL2Correction_mul_lower, add_zero]
    rfl

/-- Four alternating root factors give the full homomorphism law. -/
theorem affineSL2Section_mul (g h : SL2 F) :
    affineSL2Section F (g * h) = affineSL2Section F g * affineSL2Section F h := by
  obtain ⟨x, y, z, w, hh⟩ := FiniteRingSl2.exists_four_factors h
  change h = sl2Upper x * sl2Lower y * sl2Upper z * sl2Lower w at hh
  rw [hh]
  simp only [← mul_assoc, affineSL2Section_mul_lower, affineSL2Section_mul_upper,
    affineSL2Section_upper]

/-- The actual affine rank-one subgroup, with the lower root at degree one. -/
def affineSL2Embedding : SL2 F →* LoopSL2 F where
  toFun := affineSL2Section F
  map_one' := affineSL2Section_one F
  map_mul' := affineSL2Section_mul F

@[simp] theorem projection_affineSL2Embedding (g : SL2 F) :
    projection F (affineSL2Embedding F g) = affineConstantSL2Map F g := rfl

theorem affineSL2Embedding_injective : Function.Injective (affineSL2Embedding F) := by
  intro g h he
  exact affineConstantSL2Map_injective F (congrArg (projection F) he)

@[simp] theorem affineSL2Embedding_upper (s : F) :
    affineSL2Embedding F (sl2Upper s) =
      upperRoot F (Multiplicative.ofAdd (affineUpperParameter F s)) := affineSL2Section_upper F s

@[simp] theorem affineSL2Embedding_lower (s : F) :
    affineSL2Embedding F (sl2Lower s) =
      lowerRoot F (Multiplicative.ofAdd (affineLowerParameter F s)) := affineSL2Section_lower F s

/-- The shifted lower-root convention reverses the standard diagonal coroot. -/
theorem affineSL2Embedding_diagonal (a : Fˣ) :
    affineSL2Embedding F (sl2Diagonal a) = affineCoroot F a⁻¹ := by
  rw [affineCoroot_eq_central_finite, inv_inv, finiteCoroot_apply]
  apply SL2SymbolExtension.ext
  · change affineConstantSL2Map F (sl2Diagonal a) = 1 * sl2Diagonal (laurentConstantUnit F a)
    rw [one_mul, affineConstantSL2Map_diagonal]
  · change Additive.ofMul (affineSL2Correction F (sl2Diagonal a)) =
      Additive.ofMul a⁻¹ + 0 + laurentTameHom F (kubotaCocycle 1
        (sl2Diagonal (laurentConstantUnit F a)))
    rw [affineSL2Correction_of_left_zero F _ (by rfl), kubotaUnit_diagonal,
      kubotaCocycle_one_left, map_zero, add_zero, add_zero]

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
