import GaloisForLFunctions.HTGeometry.LoopEisenstein.IntegralPositiveVertex
import GaloisForLFunctions.HTGeometry.LoopEisenstein.IntegralPowerSeriesRescaling
import GaloisForLFunctions.HTGeometry.LoopEisenstein.ShiftedPositiveSplitting
import GaloisForLFunctions.HTGeometry.LoopEisenstein.FullVertexMatrixWords

/-!
# The common integral Borel of adjacent vertices

The central discrepancy between shifted positive splittings is a tame
pairing with a power-series unit. Its residue is a valuation unit, so
that discrepancy is a valuation unit as well. Consequently both actual
integral vertex subgroups have exactly the same Borel intersection.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open scoped WithZero WithZeroMulInt
noncomputable section
variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

/-- Pairing with a power-series unit of integral unit residue has valuation one. -/
theorem laurentTameSymbol_powerSeries_valuation_one (r : (LaurentSeries F)ˣ)
    (p : PowerSeries F) (hp : PowerSeries.constantCoeff p ≠ 0)
    (hv : v (PowerSeries.constantCoeff p) = 1) :
    laurentTameSymbol F r (powerSeriesFieldUnit F p (powerSeries_ne_zero_of_constant F p hp))
      ∈ valuationUnitSubgroup v := by
  rw [powerSeriesFieldUnit_eq_laurentUnit F p _ hp, laurentTameSymbol_antisymm,
    laurentTameSymbol_powerSeriesUnit_left]
  apply (valuationUnitSubgroup v).inv_mem
  apply (valuationUnitSubgroup v).zpow_mem
  change v ((powerSeriesResidueUnit F (powerSeriesUnitOfConstant F p hp) : Fˣ) : F) = 1
  simpa only [coe_powerSeriesResidueUnit, coe_powerSeriesUnitOfConstant] using hv

private theorem constant_ne_zero_of_value_one (p : PowerSeries F)
    (hp : v (PowerSeries.constantCoeff p) = 1) : PowerSeries.constantCoeff p ≠ 0 := by
  intro hz
  rw [hz, map_zero] at hp
  exact zero_ne_one hp

namespace LoopSL2

/-- The adjacent integral vertex, using the actual lifted diagonal rescaling. -/
def integralAffineVertex : Subgroup (LoopSL2 F) :=
  (integralPositiveVertex v).map (diagonalRescale F (laurentXUnit F)⁻¹).toMonoidHom

private theorem diagonalRescale_centralPositive_mem
    (r : (LaurentSeries F)ˣ) (c : Fˣ) (p q : PowerSeriesSL2 F)
    (hc : c ∈ valuationUnitSubgroup v) (hq : q ∈ valuationIntegralPowerSeriesSL2 v)
    (he : powerSeriesSL2Map F q = sl2Rescale r (powerSeriesSL2Map F p))
    (hd : v (PowerSeries.constantCoeff (p 1 1)) = 1) :
    diagonalRescale F r (centralPositiveEmbedding F (c, p)) ∈ integralPositiveVertex v := by
  have hn : PowerSeries.constantCoeff (p 1 1) ≠ 0 :=
    constant_ne_zero_of_value_one v (p 1 1) hd
  let t := laurentTameSymbol F r
    (powerSeriesFieldUnit F (p 1 1) (powerSeries_ne_zero_of_constant F _ hn))
  have ht : t ∈ valuationUnitSubgroup v :=
    laurentTameSymbol_powerSeries_valuation_one v r (p 1 1) hn hd
  refine ⟨(c * t, q), ⟨(valuationUnitSubgroup v).mul_mem hc ht, hq⟩, ?_⟩
  change centralEmbedding F (c * t) * positiveEmbedding F q =
    diagonalRescale F r (centralEmbedding F c * positiveEmbedding F p)
  rw [(diagonalRescale F r).map_mul, diagonalRescale_centralEmbedding,
    diagonalRescale_positiveEmbedding F r p q he hn, (centralEmbedding F).map_mul, mul_assoc]

/-- An adjacent integral vertex element in Borel already lies in the standard integral vertex. -/
theorem integralAffineVertex_borel_mem_positive {g : LoopSL2 F}
    (hg : g ∈ integralAffineVertex v) (hb : g ∈ positiveBorel F) :
    g ∈ integralPositiveVertex v := by
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨⟨c, p⟩, ⟨hc, hp⟩, rfl⟩ := hx
  have hproj := projection_mem_laurentIwahori F hb
  change projection F (diagonalRescale F (laurentXUnit F)⁻¹
    (centralEmbedding F c * positiveEmbedding F p)) ∈ laurentIwahori F at hproj
  rw [projection_diagonalRescale, map_mul, projection_centralEmbedding,
    projection_positiveEmbedding, one_mul] at hproj
  have hz : PowerSeries.constantCoeff (p 0 1) = 0 :=
    (vertexMatrixEmbedding_mem_iwahori_iff F true p).mp hproj
  obtain ⟨q, hq, _, he⟩ := exists_integralPowerSeries_affineShift v p hp hz
  exact diagonalRescale_centralPositive_mem v (laurentXUnit F)⁻¹ c p q hc hq he
    (integralPowerSeriesSL2_diagonal_values v p hp (Or.inl hz)).2

/-- The common integral Borel is contained in the adjacent integral vertex. -/
theorem integralPositiveBorel_le_affineVertex : integralPositiveBorel v ≤ integralAffineVertex v := by
  intro g hg
  obtain ⟨⟨c, p⟩, ⟨hc, hp⟩, he⟩ := hg.1
  have hi : p ∈ iwahoriMatrices F := (centralPositiveEmbedding_mem_borel_iff c p).mp
    (he.symm ▸ hg.2)
  obtain ⟨q, hq, hshift⟩ := exists_integralPowerSeries_forwardShift v p hp hi
  have hz : PowerSeries.constantCoeff (p 1 0) = 0 := (mem_iwahoriMatrices F p).mp hi
  have hforward : diagonalRescale F (laurentXUnit F) g ∈ integralPositiveVertex v := by
    rw [← he]
    exact diagonalRescale_centralPositive_mem v (laurentXUnit F) c p q hc hq hshift
      (integralPowerSeriesSL2_diagonal_values v p hp (Or.inr hz)).2
  exact ⟨diagonalRescale F (laurentXUnit F) g, hforward,
    diagonalRescale_inverse F (laurentXUnit F) g⟩

/-- Both adjacent integral vertices meet the full positive Borel in the same actual subgroup. -/
theorem integralAffineVertex_inf_positiveBorel :
    integralAffineVertex v ⊓ positiveBorel F = integralPositiveBorel v := by
  apply le_antisymm
  · intro g hg
    exact ⟨integralAffineVertex_borel_mem_positive v hg.1 hg.2, hg.2⟩
  · exact le_inf (integralPositiveBorel_le_affineVertex v) inf_le_right

/-- Both intrinsic torus values are one on the adjacent integral vertex–Borel intersection. -/
theorem integralAffineVertex_borel_torus_values (g : positiveBorel F)
    (hg : (g : LoopSL2 F) ∈ integralAffineVertex v) :
    v (((borelTorusHom F g).1 : Fˣ) : F) = 1 ∧
      v (((borelTorusHom F g).2 : Fˣ) : F) = 1 :=
  integralPositiveVertex_borel_torus_values v g
    (integralAffineVertex_borel_mem_positive v hg g.property)

end LoopSL2
end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.integralAffineVertex_inf_positiveBorel
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.integralAffineVertex_borel_torus_values
