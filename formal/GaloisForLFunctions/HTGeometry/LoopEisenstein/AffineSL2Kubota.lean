import GaloisForLFunctions.HTGeometry.LoopEisenstein.ConstantSL2Embedding

/-!
# The central correction for the affine simple SL₂

After shifting the lower root to degree one, the Kubota section has correction
`d` on an upper triangular matrix and one on the other Bruhat chart. The two
endpoint tame identities prove compatibility with right lower-root multiplication.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

theorem sl2_mul_lower_c (g : SL2 F) (s : F) :
    (g * sl2Lower s) 1 0 = g 1 0 + g 1 1 * s := by
  simp [sl2Lower, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_mul_lower_d (g : SL2 F) (s : F) :
    (g * sl2Lower s) 1 1 = g 1 1 := by
  simp [sl2Lower, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_mul_upper_c (g : SL2 F) (s : F) :
    (g * sl2Upper s) 1 0 = g 1 0 := by
  simp [sl2Upper, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_bottom_right_ne_zero (g : SL2 F) (hc : g 1 0 = 0) : g 1 1 ≠ 0 := by
  have hd := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hd
  exact right_ne_zero_of_mul_eq_one hd

theorem kubotaUnit_of_left_zero (g : SL2 F) (hc : g 1 0 = 0) :
    kubotaUnit g = Units.mk0 (g 1 1) (sl2_bottom_right_ne_zero F g hc) := by
  classical
  apply Units.ext
  change (if g 1 0 = 0 then g 1 1 else g 1 0) = g 1 1
  exact if_pos hc

/-- The lower-left monomial of a nontriangular affine constant matrix. -/
theorem kubotaUnit_affine_of_left_ne_zero (g : SL2 F) (hc : g 1 0 ≠ 0) :
    kubotaUnit (affineConstantSL2Map F g) =
      laurentConstantUnit F (Units.mk0 (g 1 0) hc) * laurentXUnit F := by
  have hn : laurentConstantRingHom F (g 1 0) ≠ 0 :=
    (map_ne_zero (laurentConstantRingHom F)).mpr hc
  apply Units.ext
  rw [coe_kubotaUnit, kubotaX, affineConstantSL2Map_one_zero,
    if_neg (mul_ne_zero (laurentXUnit F).ne_zero hn)]
  change (laurentXUnit F : LaurentSeries F) * laurentConstantRingHom F (g 1 0) =
    laurentConstantRingHom F (g 1 0) * (laurentXUnit F : LaurentSeries F)
  exact mul_comm _ _

theorem kubotaUnit_affine_of_left_zero (g : SL2 F) (hc : g 1 0 = 0) :
    kubotaUnit (affineConstantSL2Map F g) = laurentConstantUnit F (kubotaUnit g) := by
  apply Units.ext
  rw [coe_kubotaUnit, kubotaX, affineConstantSL2Map_one_zero,
    affineConstantSL2Map_one_one, hc, map_zero, mul_zero, if_pos rfl,
    kubotaUnit_of_left_zero F g hc]
  rfl

theorem laurentTameSymbol_constant_mul_X_constant (a b : Fˣ) :
    laurentTameSymbol F (laurentConstantUnit F a * laurentXUnit F)
      (laurentConstantUnit F b) = b⁻¹ := by
  rw [laurentTameSymbol_mul_left, laurentTameSymbol_constants, one_mul,
    laurentTameSymbol_antisymm, laurentTameSymbol_constant_X]

theorem laurentConstantUnit_mul_X_div (a b : Fˣ) :
    (laurentConstantUnit F a * laurentXUnit F) /
      (laurentConstantUnit F b * laurentXUnit F) = laurentConstantUnit F (a / b) := by
  rw [div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_assoc (laurentConstantUnit F a),
    mul_inv_cancel, mul_one, div_eq_mul_inv, laurentConstantUnit_mul,
    laurentConstantUnit_inv]

/-- The multiplicative central coordinate of the affine rank-one section. -/
def affineSL2Correction (g : SL2 F) : Fˣ := by
  classical
  exact if g 1 0 = 0 then kubotaUnit g else 1

theorem affineSL2Correction_of_left_zero (g : SL2 F) (hc : g 1 0 = 0) :
    affineSL2Correction F g = kubotaUnit g := by
  simp only [affineSL2Correction, if_pos hc]

theorem affineSL2Correction_of_left_ne_zero (g : SL2 F) (hc : g 1 0 ≠ 0) :
    affineSL2Correction F g = 1 := by
  simp only [affineSL2Correction, if_neg hc]

@[simp] theorem affineSL2Correction_one : affineSL2Correction F 1 = 1 := by
  simp [affineSL2Correction, kubotaUnit_one]

@[simp] theorem affineSL2Correction_upper (s : F) :
    affineSL2Correction F (sl2Upper s) = 1 := by
  rw [affineSL2Correction_of_left_zero F _ (by rfl), kubotaUnit_upper]

@[simp] theorem affineSL2Correction_lower (s : F) :
    affineSL2Correction F (sl2Lower s) = 1 := by
  by_cases hs : s = 0
  · rw [hs, sl2Lower_zero, affineSL2Correction_one]
  · exact affineSL2Correction_of_left_ne_zero F _ hs

theorem affineSL2Correction_mul_upper (g : SL2 F) (s : F) :
    affineSL2Correction F (g * sl2Upper s) = affineSL2Correction F g := by
  classical
  change (if (g * sl2Upper s) 1 0 = 0 then kubotaUnit (g * sl2Upper s) else 1) =
    if g 1 0 = 0 then kubotaUnit g else 1
  rw [sl2_mul_upper_c, kubotaUnit_mul_upper]

/-- The tame cocycle pulled back by the affine coefficient-field matrix map. -/
def affineSL2KubotaFactor (g h : SL2 F) : Fˣ :=
  laurentTameSymbol F
    (kubotaUnit (affineConstantSL2Map F (g * h)) / kubotaUnit (affineConstantSL2Map F g))
    (kubotaUnit (affineConstantSL2Map F (g * h)) / kubotaUnit (affineConstantSL2Map F h))

theorem affineSL2KubotaFactor_eq (g h : SL2 F) :
    Additive.ofMul (affineSL2KubotaFactor F g h) =
      laurentTameHom F (kubotaCocycle (affineConstantSL2Map F g) (affineConstantSL2Map F h)) := by
  rw [kubotaCocycle, laurentTameHom_symbol, affineSL2KubotaFactor, map_mul]

@[simp] theorem affineSL2KubotaFactor_one_right (g : SL2 F) :
    affineSL2KubotaFactor F g 1 = 1 := by
  apply Additive.ofMul.injective
  rw [affineSL2KubotaFactor_eq, map_one, kubotaCocycle_one_right, map_zero]
  rfl

private theorem affine_factor_lower_nonzero (g : SL2 F) (s : F)
    (hc : g 1 0 ≠ 0) (hs : s ≠ 0) (he : g 1 0 + g 1 1 * s ≠ 0) :
    affineSL2KubotaFactor F g (sl2Lower s) = 1 := by
  have he' : (g * sl2Lower s) 1 0 ≠ 0 := by rwa [sl2_mul_lower_c]
  rw [affineSL2KubotaFactor, kubotaUnit_affine_of_left_ne_zero F _ he',
    kubotaUnit_affine_of_left_ne_zero F _ hc,
    kubotaUnit_affine_of_left_ne_zero F (sl2Lower s) hs,
    laurentConstantUnit_mul_X_div, laurentConstantUnit_mul_X_div,
    laurentTameSymbol_constants]

private theorem affine_factor_lower_initial (g : SL2 F) (s : F)
    (hc : g 1 0 = 0) (hs : s ≠ 0) :
    affineSL2KubotaFactor F g (sl2Lower s) = (kubotaUnit g)⁻¹ := by
  have hd := sl2_bottom_right_ne_zero F g hc
  have he : (g * sl2Lower s) 1 0 ≠ 0 := by
    rw [sl2_mul_lower_c, hc, zero_add]
    exact mul_ne_zero hd hs
  let d := kubotaUnit g
  let t := laurentConstantUnit F (Units.mk0 s hs) * laurentXUnit F
  have hx : kubotaUnit (affineConstantSL2Map F (g * sl2Lower s)) =
      laurentConstantUnit F d * t := by
    rw [kubotaUnit_affine_of_left_ne_zero F _ he]
    dsimp only [t]
    rw [← mul_assoc, ← laurentConstantUnit_mul]
    congr 2
    apply Units.ext
    change (g * sl2Lower s) 1 0 = (kubotaUnit g : F) * s
    rw [sl2_mul_lower_c, hc, zero_add, kubotaUnit_of_left_zero F g hc]
    rfl
  rw [affineSL2KubotaFactor, hx, kubotaUnit_affine_of_left_zero F g hc,
    kubotaUnit_affine_of_left_ne_zero F (sl2Lower s) hs]
  change laurentTameSymbol F ((laurentConstantUnit F d * t) / laurentConstantUnit F d)
    ((laurentConstantUnit F d * t) / t) = d⁻¹
  rw [← laurentTameSymbol_initial_shear F _ _ (laurentTameSymbol_constants F d d)]
  dsimp only [t]
  rw [← mul_assoc, ← laurentConstantUnit_mul, laurentTameSymbol_constant_mul_X_constant]

private theorem affine_factor_lower_final (g : SL2 F) (s : F)
    (hc : g 1 0 ≠ 0) (hs : s ≠ 0) (he : g 1 0 + g 1 1 * s = 0) :
    affineSL2KubotaFactor F g (sl2Lower s) = kubotaUnit (g * sl2Lower s) := by
  have he' : (g * sl2Lower s) 1 0 = 0 := by rwa [sl2_mul_lower_c]
  let d := kubotaUnit (g * sl2Lower s)
  let t := laurentConstantUnit F (Units.mk0 s hs) * laurentXUnit F
  have hd : (d : F) = g 1 1 := by
    dsimp only [d]
    rw [kubotaUnit_of_left_zero F _ he']
    exact sl2_mul_lower_d F g s
  have hx : kubotaUnit (affineConstantSL2Map F g) = -laurentConstantUnit F d * t := by
    rw [kubotaUnit_affine_of_left_ne_zero F g hc]
    apply Units.ext
    change laurentConstantRingHom F (g 1 0) * (laurentXUnit F : LaurentSeries F) =
      -(laurentConstantRingHom F (d : F)) *
        (laurentConstantRingHom F s * (laurentXUnit F : LaurentSeries F))
    have hg : g 1 0 = -(d : F) * s := by rw [hd]; linear_combination he
    rw [hg, map_mul, map_neg, mul_assoc]
  have ht : laurentTameSymbol F (-laurentConstantUnit F d * t)
      (laurentConstantUnit F d) = d⁻¹ := by
    rw [← hx, kubotaUnit_affine_of_left_ne_zero F g hc,
      laurentTameSymbol_constant_mul_X_constant]
  have hz := laurentTameSymbol_zero_shear F (laurentConstantUnit F d) t
    (laurentTameSymbol_constants F d d)
  rw [ht] at hz
  rw [affineSL2KubotaFactor, kubotaUnit_affine_of_left_zero F _ he', hx,
    kubotaUnit_affine_of_left_ne_zero F (sl2Lower s) hs]
  change laurentTameSymbol F (laurentConstantUnit F d / (-laurentConstantUnit F d * t))
    (laurentConstantUnit F d / t) = d
  exact (inv_mul_eq_one.mp hz).symm

/-- The correction absorbs every lower-root cocycle, including both triangular endpoints. -/
theorem affineSL2Correction_mul_lower (g : SL2 F) (s : F) :
    affineSL2Correction F (g * sl2Lower s) =
      affineSL2Correction F g * affineSL2KubotaFactor F g (sl2Lower s) := by
  by_cases hs : s = 0
  · rw [hs, sl2Lower_zero, mul_one, affineSL2KubotaFactor_one_right, mul_one]
  by_cases hc : g 1 0 = 0
  · have he : (g * sl2Lower s) 1 0 ≠ 0 := by
      rw [sl2_mul_lower_c, hc, zero_add]
      exact mul_ne_zero (sl2_bottom_right_ne_zero F g hc) hs
    rw [affineSL2Correction_of_left_ne_zero F _ he,
      affineSL2Correction_of_left_zero F g hc, affine_factor_lower_initial F g s hc hs,
      mul_inv_cancel]
  · rw [affineSL2Correction_of_left_ne_zero F g hc, one_mul]
    by_cases he : g 1 0 + g 1 1 * s = 0
    · have he' : (g * sl2Lower s) 1 0 = 0 := by rwa [sl2_mul_lower_c]
      rw [affineSL2Correction_of_left_zero F _ he', affine_factor_lower_final F g s hc hs he]
    · have he' : (g * sl2Lower s) 1 0 ≠ 0 := by rwa [sl2_mul_lower_c]
      rw [affineSL2Correction_of_left_ne_zero F _ he',
        affine_factor_lower_nonzero F g s hc hs he]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
