import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2DiagonalRescaling

/-!
# Diagonal rescaling of the symbol extension

The diagonal general-linear action lifts to the actual Milnor-symbol
central extension. Its correction is the symbol of the scaling unit and
the lower diagonal entry on the triangular chart, and zero elsewhere.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open Matrix
noncomputable section
variable {F A : Type*} [Field F] [AddCommGroup A]

private theorem bottom_left_mul (g h : SL2 F) :
    (g * h) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 := by
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem bottom_right_mul (g h : SL2 F) :
    (g * h) 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := by
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem right_ne_zero_of_triangular (g : SL2 F) (hg : g 1 0 = 0) :
    g 1 1 ≠ 0 := by
  classical
  simpa only [kubotaX, hg, if_true] using kubotaX_ne_zero g

private theorem product_triangular_of_both (g h : SL2 F)
    (hg : g 1 0 = 0) (hh : h 1 0 = 0) : (g * h) 1 0 = 0 := by
  rw [bottom_left_mul, hg, hh, zero_mul, mul_zero, add_zero]

private theorem product_nontriangular_of_left (g h : SL2 F)
    (hg : g 1 0 = 0) (hh : h 1 0 ≠ 0) : (g * h) 1 0 ≠ 0 := by
  rw [bottom_left_mul, hg, zero_mul, zero_add]
  exact mul_ne_zero (right_ne_zero_of_triangular g hg) hh

private theorem product_nontriangular_of_right (g h : SL2 F)
    (hg : g 1 0 ≠ 0) (hh : h 1 0 = 0) : (g * h) 1 0 ≠ 0 := by
  have hd := SpecialLinearGroup.det_coe h
  rw [det_fin_two, hh, mul_zero, sub_zero] at hd
  rw [bottom_left_mul, hh, mul_zero, add_zero]
  exact mul_ne_zero hg (left_ne_zero_of_mul_eq_one hd)

private theorem kubotaUnit_mul_left_triangular (g h : SL2 F)
    (hg : g 1 0 = 0) : kubotaUnit (g * h) = kubotaUnit g * kubotaUnit h := by
  classical
  apply Units.ext
  simp only [coe_kubotaUnit, Units.val_mul]
  unfold kubotaX
  by_cases hh : h 1 0 = 0
  · rw [if_pos (product_triangular_of_both g h hg hh), if_pos hg, if_pos hh,
      bottom_right_mul, hg, zero_mul, zero_add]
  · rw [if_neg (product_nontriangular_of_left g h hg hh), if_pos hg, if_neg hh,
      bottom_left_mul, hg, zero_mul, zero_add]

private theorem kubotaUnit_mul_right_triangular (g h : SL2 F)
    (hg : g 1 0 ≠ 0) (hh : h 1 0 = 0) :
    kubotaUnit (g * h) = kubotaUnit g / kubotaUnit h := by
  classical
  apply Units.ext
  simp only [coe_kubotaUnit, Units.val_div_eq_div_val]
  unfold kubotaX
  rw [if_neg (product_nontriangular_of_right g h hg hh), if_neg hg, if_pos hh,
    bottom_left_mul, hh, mul_zero, add_zero]
  have hd := SpecialLinearGroup.det_coe h
  rw [det_fin_two, hh, mul_zero, sub_zero] at hd
  rw [eq_div_iff (right_ne_zero_of_triangular h hh), mul_assoc, hd, mul_one]

private theorem kubotaUnit_mul_triangular_boundary (g h : SL2 F)
    (hg : g 1 0 ≠ 0) (hh : h 1 0 ≠ 0) (hk : (g * h) 1 0 = 0) :
    kubotaUnit (g * h) = -kubotaUnit g / kubotaUnit h := by
  classical
  apply Units.ext
  simp only [coe_kubotaUnit, kubotaX, hg, hh, hk, if_true, if_false,
    Units.val_div_eq_div_val, Units.val_neg]
  rw [eq_div_iff hh, bottom_right_mul]
  have hc := hk
  rw [bottom_left_mul] at hc
  have hd := SpecialLinearGroup.det_coe h
  rw [det_fin_two] at hd
  linear_combination h 1 1 * hc - g 1 0 * hd

/-- Diagonal rescaling preserves the triangular chart. -/
theorem sl2Rescale_lower_left_eq_zero_iff (r : Fˣ) (g : SL2 F) :
    sl2Rescale r g 1 0 = 0 ↔ g 1 0 = 0 := by
  change (((r⁻¹ : Fˣ) : F) * g 1 0 = 0) ↔ _
  exact mul_eq_zero.trans (or_iff_right (Units.ne_zero _))

theorem kubotaUnit_rescale_triangular (r : Fˣ) (g : SL2 F) (hg : g 1 0 = 0) :
    kubotaUnit (sl2Rescale r g) = kubotaUnit g := by
  classical
  apply Units.ext
  simp only [coe_kubotaUnit, kubotaX, hg,
    (sl2Rescale_lower_left_eq_zero_iff r g).mpr hg, if_true]
  rfl

theorem kubotaUnit_rescale_nontriangular (r : Fˣ) (g : SL2 F) (hg : g 1 0 ≠ 0) :
    kubotaUnit (sl2Rescale r g) = r⁻¹ * kubotaUnit g := by
  classical
  have hr : sl2Rescale r g 1 0 ≠ 0 :=
    fun h => hg ((sl2Rescale_lower_left_eq_zero_iff r g).mp h)
  apply Units.ext
  simp only [coe_kubotaUnit, kubotaX, hg, hr, if_false, Units.val_mul]
  rfl

/-- The correction of the triangular chart in the actual degree-two symbol group. -/
def rescaleSymbolCorrection (r : Fˣ) (g : SL2 F) : MilnorKDeg F 2 := by
  classical
  exact if g 1 0 = 0 then milnorSym2 F r (kubotaUnit g) else 0

private theorem symbol_self_eq_minus_one (r : Fˣ) :
    milnorSym2 F r r = milnorSym2 F r (-1) := by
  have hz := milnorSym2_neg_self r
  have he : (-r : Fˣ) = (-1) * r := by ext; simp
  rw [he, milnorSym2_mul_right, milnorSym2_antisymm r r] at hz
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)).symm

private theorem symbol_mul_both (r a b : Fˣ) :
    milnorSym2 F (r * a) (r * b) = milnorSym2 F a b +
      milnorSym2 F r (b / a) + milnorSym2 F r r := by
  simp only [milnorSym2_mul_left, milnorSym2_mul_right, div_eq_mul_inv,
    milnorSym2_inv_right]
  rw [milnorSym2_antisymm a r]
  abel

/-- The rescaling defect of the Kubota cocycle is the explicit chart correction. -/
theorem kubotaCocycle_rescale (r : Fˣ) (g h : SL2 F) :
    kubotaCocycle (sl2Rescale r g) (sl2Rescale r h) =
      kubotaCocycle g h + rescaleSymbolCorrection r (g * h) -
        rescaleSymbolCorrection r g - rescaleSymbolCorrection r h := by
  classical
  by_cases hg : g 1 0 = 0
  · by_cases hh : h 1 0 = 0
    · have hk := product_triangular_of_both g h hg hh
      simp only [kubotaCocycle, ← (sl2Rescale r).map_mul,
        kubotaUnit_rescale_triangular r g hg, kubotaUnit_rescale_triangular r h hh,
        kubotaUnit_rescale_triangular r (g * h) hk,
        rescaleSymbolCorrection, hg, hh, hk, if_true]
      rw [kubotaUnit_mul_left_triangular g h hg, milnorSym2_mul_right]
      abel
    · have hk := product_nontriangular_of_left g h hg hh
      simp only [kubotaCocycle, ← (sl2Rescale r).map_mul,
        kubotaUnit_rescale_triangular r g hg, kubotaUnit_rescale_nontriangular r h hh,
        kubotaUnit_rescale_nontriangular r (g * h) hk,
        rescaleSymbolCorrection, hg, hh, hk, if_true, if_false, add_zero, sub_zero]
      have hq : (r⁻¹ * kubotaUnit (g * h)) / kubotaUnit g =
          r⁻¹ * (kubotaUnit (g * h) / kubotaUnit g) := by simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      have hp : (r⁻¹ * kubotaUnit (g * h)) / (r⁻¹ * kubotaUnit h) =
          kubotaUnit (g * h) / kubotaUnit h := by simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hq, hp, milnorSym2_mul_left, milnorSym2_inv_left]
      have he : kubotaUnit (g * h) / kubotaUnit h = kubotaUnit g := by
        rw [kubotaUnit_mul_left_triangular g h hg]; simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [he]
      abel
  · by_cases hh : h 1 0 = 0
    · have hk := product_nontriangular_of_right g h hg hh
      simp only [kubotaCocycle, ← (sl2Rescale r).map_mul,
        kubotaUnit_rescale_nontriangular r g hg, kubotaUnit_rescale_triangular r h hh,
        kubotaUnit_rescale_nontriangular r (g * h) hk,
        rescaleSymbolCorrection, hg, hh, hk, if_true, if_false, add_zero, sub_zero]
      have hq : (r⁻¹ * kubotaUnit (g * h)) / (r⁻¹ * kubotaUnit g) =
          kubotaUnit (g * h) / kubotaUnit g := by simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      have hp : (r⁻¹ * kubotaUnit (g * h)) / kubotaUnit h =
          r⁻¹ * (kubotaUnit (g * h) / kubotaUnit h) := by simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hq, hp, milnorSym2_mul_right, milnorSym2_inv_right,
        milnorSym2_antisymm (kubotaUnit (g * h) / kubotaUnit g) r, neg_neg]
      have he : kubotaUnit (g * h) / kubotaUnit g = (kubotaUnit h)⁻¹ := by
        rw [kubotaUnit_mul_right_triangular g h hg hh]; simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [he, milnorSym2_inv_right]
      abel
    · by_cases hk : (g * h) 1 0 = 0
      · simp only [kubotaCocycle, ← (sl2Rescale r).map_mul,
          kubotaUnit_rescale_nontriangular r g hg, kubotaUnit_rescale_nontriangular r h hh,
          kubotaUnit_rescale_triangular r (g * h) hk,
          rescaleSymbolCorrection, hg, hh, hk, if_true, if_false, sub_zero]
        have hq : kubotaUnit (g * h) / (r⁻¹ * kubotaUnit g) =
            r * (kubotaUnit (g * h) / kubotaUnit g) := by simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        have hp : kubotaUnit (g * h) / (r⁻¹ * kubotaUnit h) =
            r * (kubotaUnit (g * h) / kubotaUnit h) := by simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        rw [hq, hp, symbol_mul_both, symbol_self_eq_minus_one]
        have he : (kubotaUnit (g * h) / kubotaUnit h) /
            (kubotaUnit (g * h) / kubotaUnit g) = kubotaUnit g / kubotaUnit h := by simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        rw [he, add_assoc, ← milnorSym2_mul_right]
        congr 2
        rw [kubotaUnit_mul_triangular_boundary g h hg hh hk]
        apply Units.ext
        simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_neg, Units.val_one]
        ring
      · simp only [kubotaCocycle, ← (sl2Rescale r).map_mul,
          kubotaUnit_rescale_nontriangular r g hg, kubotaUnit_rescale_nontriangular r h hh,
          kubotaUnit_rescale_nontriangular r (g * h) hk,
          rescaleSymbolCorrection, hg, hh, hk, if_false, add_zero, sub_zero]
        congr 1 <;> simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

namespace SL2SymbolExtension
variable (τ : MilnorKDeg F 2 →+ A)

private theorem rescaleSymbolCorrection_inverse (r : Fˣ) (g : SL2 F) :
    rescaleSymbolCorrection r⁻¹ (sl2Rescale r g) = -rescaleSymbolCorrection r g := by
  classical
  by_cases hg : g 1 0 = 0
  · simp only [rescaleSymbolCorrection, (sl2Rescale_lower_left_eq_zero_iff r g).mpr hg,
      hg, if_true, kubotaUnit_rescale_triangular r g hg, milnorSym2_inv_left]
  · have hr : sl2Rescale r g 1 0 ≠ 0 :=
      fun h => hg ((sl2Rescale_lower_left_eq_zero_iff r g).mp h)
    simp only [rescaleSymbolCorrection, hg, hr, if_false, neg_zero]

/-- The diagonal general-linear action on the actual symbol central extension. -/
def diagonalRescale (r : Fˣ) : SL2SymbolExtension τ ≃* SL2SymbolExtension τ where
  toFun g := ⟨sl2Rescale r g.base, g.centralCoord + τ (rescaleSymbolCorrection r g.base)⟩
  invFun g := ⟨sl2Rescale r⁻¹ g.base, g.centralCoord + τ (rescaleSymbolCorrection r⁻¹ g.base)⟩
  left_inv g := by
    apply SL2SymbolExtension.ext
    · exact sl2Rescale_inverse r g.base
    · change g.centralCoord + τ (rescaleSymbolCorrection r g.base) +
        τ (rescaleSymbolCorrection r⁻¹ (sl2Rescale r g.base)) = g.centralCoord
      rw [rescaleSymbolCorrection_inverse, map_neg, add_neg_cancel_right]
  right_inv g := by
    apply SL2SymbolExtension.ext
    · simpa only [inv_inv] using sl2Rescale_inverse r⁻¹ g.base
    · have he := rescaleSymbolCorrection_inverse r⁻¹ g.base
      rw [inv_inv] at he
      change g.centralCoord + τ (rescaleSymbolCorrection r⁻¹ g.base) +
        τ (rescaleSymbolCorrection r (sl2Rescale r⁻¹ g.base)) = g.centralCoord
      rw [he, map_neg, add_neg_cancel_right]
  map_mul' g h := by
    apply SL2SymbolExtension.ext
    · exact map_mul (sl2Rescale r) g.base h.base
    · change (g.centralCoord + h.centralCoord + τ (kubotaCocycle g.base h.base)) +
        τ (rescaleSymbolCorrection r (g.base * h.base)) =
        (g.centralCoord + τ (rescaleSymbolCorrection r g.base)) +
        (h.centralCoord + τ (rescaleSymbolCorrection r h.base)) +
        τ (kubotaCocycle (sl2Rescale r g.base) (sl2Rescale r h.base))
      rw [kubotaCocycle_rescale, map_sub, map_sub, map_add]
      abel

end SL2SymbolExtension
end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.kubotaCocycle_rescale
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2SymbolExtension.diagonalRescale
