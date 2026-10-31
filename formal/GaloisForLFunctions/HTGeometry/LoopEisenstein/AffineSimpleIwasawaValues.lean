import GaloisForLFunctions.HTGeometry.LoopEisenstein.FiniteSimpleIwasawaValues
import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveUnipotentFieldMap

/-!
# Exact affine simple Iwasawa values

The affine simple embedding sends a diagonal unit to the central coordinate
and its inverse finite coordinate. Its positive root has trivial torus
coordinates. The coefficient-field column-norm factorization therefore
computes both actual loop Iwasawa valuations.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2
open scoped WithZero WithZeroMulInt
noncomputable section
variable (F : Type*) [Field F]

private theorem upper_triangular_factor (b : SL2 F) (hb : b 1 0 = 0) :
    ∃ a : Fˣ, (a : F) = b 0 0 ∧
      b = sl2Diagonal a * sl2Upper (b 0 1 / (a : F)) := by
  have hd := Matrix.SpecialLinearGroup.det_coe b
  rw [Matrix.det_fin_two, hb, mul_zero, sub_zero] at hd
  have ha : b 0 0 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hd
    exact zero_ne_one hd
  let a := Units.mk0 (b 0 0) ha
  refine ⟨a, rfl, ?_⟩
  have he := sl2_pivot_upper_left b a rfl
  rw [hb, neg_zero, zero_div, sl2Lower_zero, one_mul] at he
  have h := congrArg (fun x : SL2 F => x * sl2Upper (b 0 1 / (a : F))) he
  rw [mul_assoc, ← sl2Upper_add, neg_div, neg_add_cancel, sl2Upper_zero, mul_one] at h
  exact h

private theorem affineUpperRoot_unipotent (t : F) :
    affineSimpleSL2Embedding F (sl2Upper t) ∈ positiveUnipotent F := by
  let p : PowerSeries F := PowerSeries.X * PowerSeries.C t
  have hp : PowerSeries.constantCoeff p = 0 := by
    simp only [p, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have he : (p : LaurentSeries F) = affineLowerParameter F t := by
    change ((PowerSeries.X * PowerSeries.C t : PowerSeries F) : LaurentSeries F) = _
    rw [map_mul, HahnSeries.ofPowerSeries_X]
    change (HahnSeries.single (1 : ℤ) (1 : F)) *
        (HahnSeries.ofPowerSeries ℤ F) (PowerSeries.C t) =
      (laurentXUnit F : LaurentSeries F) *
        (HahnSeries.ofPowerSeries ℤ F) (PowerSeries.C t)
    rw [coe_laurentXUnit]
  refine ⟨FiniteRingSl2.lower p, lower_mem_positiveUnipotentMatrices F p hp, ?_⟩
  rw [positiveEmbedding_lower, he, affineSimpleSL2Embedding_upper]

private def affineUpperBorel (b : SL2 F) (hb : b 1 0 = 0) : positiveBorel F :=
  ⟨affineSimpleSL2Embedding F b, affineSimpleSL2Embedding_upperTriangular F b hb⟩

private theorem affine_diagonal_upper_torus (a : Fˣ) (t : F) :
    borelTorusHom F
      (affineUpperBorel F (sl2Diagonal a) (by rfl) *
        affineUpperBorel F (sl2Upper t) (by rfl)) = (a, a⁻¹) := by
  have hd : affineUpperBorel F (sl2Diagonal a) (by rfl) =
      ⟨cartanEmbedding F (a, a⁻¹), by
        change centralEmbedding F a * finiteCoroot F a⁻¹ ∈ positiveBorel F
        rw [← affineCoroot_eq_central_finite, ← affineSimpleSL2Embedding_diagonal]
        exact affineSimpleSL2Embedding_upperTriangular F _ (by rfl)⟩ := by
    apply Subtype.ext
    exact (affineSimpleSL2Embedding_diagonal F a).trans (affineCoroot_eq_central_finite F a)
  have hu : borelTorusHom F (affineUpperBorel F (sl2Upper t) (by rfl)) = 1 :=
    (borelTorusHom_eq_one_iff _).mpr (affineUpperRoot_unipotent F t)
  rw [map_mul, hu, mul_one, hd, borelTorusHom_cartan]

private theorem affineUpperBorel_values (v : Valuation F ℤᵐ⁰)
    (b : SL2 F) (hb : b 1 0 = 0) :
    borelValuationHom v (affineUpperBorel F b hb) = (v (b 0 0), (v (b 0 0))⁻¹) := by
  obtain ⟨a, ha, he⟩ := upper_triangular_factor F b hb
  have he' : affineUpperBorel F b hb =
      affineUpperBorel F (sl2Diagonal a) (by rfl) *
        affineUpperBorel F (sl2Upper (b 0 1 / (a : F))) (by rfl) := by
    apply Subtype.ext
    exact (congrArg (affineSimpleSL2Embedding F) he).trans
      ((affineSimpleSL2Embedding F).map_mul _ _)
  have ht : borelTorusHom F (affineUpperBorel F b hb) = (a, a⁻¹) := by
    rw [he', affine_diagonal_upper_torus]
  change (v (((borelTorusHom F (affineUpperBorel F b hb)).1 : Fˣ) : F),
    v (((borelTorusHom F (affineUpperBorel F b hb)).2 : Fˣ) : F)) = _
  rw [ht]
  change (v (a : F), v ((a⁻¹ : Fˣ) : F)) = _
  rw [Units.val_inv_eq_inv_val, map_inv₀, ha]

variable {F} (v : Valuation F ℤᵐ⁰)

private theorem affineSimpleSL2Embedding_integral (k : SL2 F)
    (hk : k ∈ valuationIntegralSL2 v) :
    affineSimpleSL2Embedding F k ∈ integralLoop v :=
  integralSimpleLoop_le_integralLoop v
    ((show affineIntegralSimple v ≤ integralSimpleLoop v from le_sup_right) ⟨k, hk, rfl⟩)

/-- An affine-simple matrix has actual loop factors with both column-norm valuations. -/
theorem exists_affineSimpleSL2Embedding_iwasawa_values (g : SL2 F) :
    ∃ k : integralLoop v, ∃ b : positiveBorel F,
      (k : LoopSL2 F) * b = affineSimpleSL2Embedding F g ∧
        borelValuationHom v b =
          (max (v (g 0 0)) (v (g 1 0)), (max (v (g 0 0)) (v (g 1 0)))⁻¹) := by
  obtain ⟨k, b, hk, hb, he, hv⟩ := exists_valued_sl2_integral_upper v g
  refine ⟨⟨affineSimpleSL2Embedding F k, affineSimpleSL2Embedding_integral v k hk⟩,
    affineUpperBorel F b hb, ?_, ?_⟩
  · exact ((affineSimpleSL2Embedding F).map_mul k b).symm.trans
      (congrArg (affineSimpleSL2Embedding F) he)
  · exact (affineUpperBorel_values F v b hb).trans
      (congrArg (fun x : ℤᵐ⁰ => (x, x⁻¹)) hv)

/-- Every full-loop integral–Borel factorization has the same affine-simple values. -/
theorem affineSimpleSL2Embedding_iwasawa_values (g : SL2 F)
    (k : integralLoop v) (b : positiveBorel F)
    (he : (k : LoopSL2 F) * b = affineSimpleSL2Embedding F g) :
    borelValuationHom v b =
      (max (v (g 0 0)) (v (g 1 0)), (max (v (g 0 0)) (v (g 1 0)))⁻¹) := by
  obtain ⟨k₀, b₀, h₀, hv⟩ := exists_affineSimpleSL2Embedding_iwasawa_values v g
  exact (borelValuationHom_iwasawa_unique v k k₀ b b₀ (he.trans h₀.symm)).trans hv

/-- The negative affine simple root has radial central value and inverse finite value. -/
theorem affineLowerRoot_iwasawa_values (x : F) (k : integralLoop v) (b : positiveBorel F)
    (he : (k : LoopSL2 F) * b = affineSimpleSL2Embedding F (sl2Lower x)) :
    borelValuationHom v b = (max 1 (v x), (max 1 (v x))⁻¹) := by
  have h := affineSimpleSL2Embedding_iwasawa_values v (sl2Lower x) k b he
  change borelValuationHom v b = (max (v 1) (v x), (max (v 1) (v x))⁻¹) at h
  simpa only [map_one] using h

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.exists_affineSimpleSL2Embedding_iwasawa_values
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.affineSimpleSL2Embedding_iwasawa_values
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.affineLowerRoot_iwasawa_values
