import GaloisForLFunctions.HTGeometry.LoopEisenstein.IntegralLoopBorelIntersection

/-!
# Exact Iwasawa values on the finite simple loop subgroup

Inverting the coefficient-field upper–integral decomposition gives an
integral–upper decomposition whose torus value is the first-column norm.
The constant positive splitting has central coordinate one. Uniqueness
of actual full-loop Borel valuations makes these values independent of
all choices of integral–Borel factors.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open scoped WithZero WithZeroMulInt
noncomputable section
variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

/-- The integral–upper convention reads the first column, rather than the bottom row. -/
theorem exists_valued_sl2_integral_upper (g : SL2 F) :
    ∃ k b : SL2 F, k ∈ valuationIntegralSL2 v ∧ b 1 0 = 0 ∧ k * b = g ∧
      v (b 0 0) = max (v (g 0 0)) (v (g 1 0)) := by
  obtain ⟨b, k, hb, hk, he, hv⟩ := exists_valued_sl2_upper_integral v g⁻¹
  have hbi : (b⁻¹ : SL2 F) 1 0 = 0 := by
    change (b⁻¹ : SL2 F).1 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    change -(b 1 0) = 0
    rw [hb, neg_zero]
  have hb00 : (b⁻¹ : SL2 F) 0 0 = b 1 1 := by
    change (b⁻¹ : SL2 F).1 0 0 = b 1 1
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hg10 : (g⁻¹ : SL2 F) 1 0 = -(g 1 0) := by
    change (g⁻¹ : SL2 F).1 1 0 = -(g 1 0)
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hg11 : (g⁻¹ : SL2 F) 1 1 = g 0 0 := by
    change (g⁻¹ : SL2 F).1 1 1 = g 0 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  refine ⟨k⁻¹, b⁻¹, (valuationIntegralSL2 v).inv_mem hk, hbi, ?_, ?_⟩
  · calc
      k⁻¹ * b⁻¹ = (b * k)⁻¹ := (mul_inv_rev b k).symm
      _ = (g⁻¹)⁻¹ := congrArg (fun x : SL2 F => x⁻¹) he
      _ = g := inv_inv g
  · rw [hb00, hv, hg10, hg11, Valuation.map_neg, max_comm]

namespace LoopSL2

private def finiteUpperIwahori (b : SL2 F) (hb : b 1 0 = 0) : iwahoriMatrices F :=
  ⟨constantPowerSeriesSL2Map F b, by
    apply (mem_iwahoriMatrices F _).mpr
    change PowerSeries.constantCoeff (PowerSeries.C (b 1 0)) = 0
    rw [PowerSeries.constantCoeff_C, hb]⟩

private theorem finiteUpperBorel_spec (b : SL2 F) (hb : b 1 0 = 0) :
    positiveBorelEmbedding F (1, finiteUpperIwahori b hb) = finiteSL2Embedding F b := by
  change centralEmbedding F 1 * positiveEmbedding F (constantPowerSeriesSL2Map F b) =
    positiveEmbedding F (constantPowerSeriesSL2Map F b)
  rw [map_one, one_mul]

private def finiteUpperBorel (b : SL2 F) (hb : b 1 0 = 0) : positiveBorel F :=
  ⟨finiteSL2Embedding F b, ⟨(1, finiteUpperIwahori b hb), finiteUpperBorel_spec b hb⟩⟩

private theorem finiteUpperBorel_values (b : SL2 F) (hb : b 1 0 = 0) :
    borelValuationHom v (finiteUpperBorel b hb) = (1, v (b 0 0)) := by
  have hf : positiveBorelFactors F (finiteUpperBorel b hb) = (1, finiteUpperIwahori b hb) :=
    positiveBorelEmbedding_injective F
      ((positiveBorelFactors_spec F (finiteUpperBorel b hb)).trans (finiteUpperBorel_spec b hb).symm)
  change (v (((positiveBorelFactors F (finiteUpperBorel b hb)).1 : Fˣ) : F),
    v ((iwahoriFiniteCoordinate F (positiveBorelFactors F (finiteUpperBorel b hb)).2 : Fˣ) : F)) = _
  rw [hf]
  change (v 1, v (PowerSeries.constantCoeff (PowerSeries.C (b 0 0)))) = (1, v (b 0 0))
  rw [map_one, PowerSeries.constantCoeff_C]

private theorem finiteSL2Embedding_integral (k : SL2 F) (hk : k ∈ valuationIntegralSL2 v) :
    finiteSL2Embedding F k ∈ integralLoop v :=
  integralSimpleLoop_le_integralLoop v
    ((show finiteIntegralSimple v ≤ integralSimpleLoop v from le_sup_left) ⟨k, hk, rfl⟩)

/-- A constant matrix has actual loop factors with exact column-norm torus value. -/
theorem exists_finiteSL2Embedding_iwasawa_values (g : SL2 F) :
    ∃ k : integralLoop v, ∃ b : positiveBorel F,
      (k : LoopSL2 F) * b = finiteSL2Embedding F g ∧
        borelValuationHom v b = (1, max (v (g 0 0)) (v (g 1 0))) := by
  obtain ⟨k, b, hk, hb, he, hv⟩ := exists_valued_sl2_integral_upper v g
  refine ⟨⟨finiteSL2Embedding F k, finiteSL2Embedding_integral v k hk⟩,
    finiteUpperBorel b hb, ?_, ?_⟩
  · exact ((finiteSL2Embedding F).map_mul k b).symm.trans (congrArg (finiteSL2Embedding F) he)
  · exact (finiteUpperBorel_values v b hb).trans (congrArg (fun x : ℤᵐ⁰ => (1, x)) hv)

/-- Every actual full-loop Iwasawa factorization of a constant matrix has these values. -/
theorem finiteSL2Embedding_iwasawa_values (g : SL2 F) (k : integralLoop v) (b : positiveBorel F)
    (he : (k : LoopSL2 F) * b = finiteSL2Embedding F g) :
    borelValuationHom v b = (1, max (v (g 0 0)) (v (g 1 0))) := by
  obtain ⟨k₀, b₀, h₀, hv⟩ := exists_finiteSL2Embedding_iwasawa_values v g
  exact (borelValuationHom_iwasawa_unique v k k₀ b b₀ (he.trans h₀.symm)).trans hv

/-- The finite negative root has exactly the radial local Iwasawa value. -/
theorem finiteLowerRoot_iwasawa_values (x : F) (k : integralLoop v) (b : positiveBorel F)
    (he : (k : LoopSL2 F) * b = finiteSL2Embedding F (sl2Lower x)) :
    borelValuationHom v b = (1, max 1 (v x)) := by
  have h := finiteSL2Embedding_iwasawa_values v (sl2Lower x) k b he
  change borelValuationHom v b = (1, max (v 1) (v x)) at h
  simpa only [map_one] using h

end LoopSL2
end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.exists_valued_sl2_integral_upper
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.finiteSL2Embedding_iwasawa_values
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.finiteLowerRoot_iwasawa_values
