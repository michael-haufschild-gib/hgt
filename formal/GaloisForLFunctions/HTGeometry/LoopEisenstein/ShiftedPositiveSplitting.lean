import GaloisForLFunctions.HTGeometry.LoopEisenstein.SymbolDiagonalRescaling
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineSL2Embedding

/-!
# The central correction of a shifted positive splitting

When diagonal rescaling sends one positive matrix to another and their
common lower-right entry is a power-series unit, the two positive lifts
differ by its tame pairing with the rescaling unit.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable (F : Type*) [Field F]
attribute [local instance] Classical.propDecidable
namespace LoopSL2

/-- Diagonal general-linear rescaling on the actual Laurent central extension. -/
def diagonalRescale (r : (LaurentSeries F)ˣ) : LoopSL2 F ≃* LoopSL2 F :=
  SL2SymbolExtension.diagonalRescale (laurentTameHom F) r

@[simp] theorem projection_diagonalRescale (r : (LaurentSeries F)ˣ) (g : LoopSL2 F) :
    projection F (diagonalRescale F r g) = sl2Rescale r (projection F g) := rfl

@[simp] theorem diagonalRescale_centralEmbedding (r : (LaurentSeries F)ˣ) (c : Fˣ) :
    diagonalRescale F r (centralEmbedding F c) = centralEmbedding F c := by
  apply SL2SymbolExtension.ext
  · exact map_one (sl2Rescale r)
  · change Additive.ofMul c + laurentTameHom F (rescaleSymbolCorrection r 1) = Additive.ofMul c
    simp only [rescaleSymbolCorrection, kubotaUnit_one, milnorSym2_one_right, ite_self,
      map_zero, add_zero]

/-- Inverting the scaling unit inverts the actual lifted rescaling. -/
theorem diagonalRescale_inverse (r : (LaurentSeries F)ˣ) (g : LoopSL2 F) :
    diagonalRescale F r⁻¹ (diagonalRescale F r g) = g :=
  (diagonalRescale F r).left_inv g

@[simp] theorem diagonalRescale_upperRoot (r : (LaurentSeries F)ˣ) (s : LaurentSeries F) :
    diagonalRescale F r (upperRoot F (Multiplicative.ofAdd s)) =
      upperRoot F (Multiplicative.ofAdd ((r : LaurentSeries F) * s)) := by
  apply SL2SymbolExtension.ext
  · exact sl2Rescale_upper r s
  · change 0 + laurentTameHom F (rescaleSymbolCorrection r (sl2Upper s)) = 0
    have hz : rescaleSymbolCorrection r (sl2Upper s) = 0 := by
      classical
      change (if (0 : LaurentSeries F) = 0 then
        milnorSym2 (LaurentSeries F) r (kubotaUnit (sl2Upper s)) else 0) = 0
      rw [if_pos rfl, kubotaUnit_upper, milnorSym2_one_right]
    rw [hz, map_zero, add_zero]

@[simp] theorem diagonalRescale_lowerRoot (r : (LaurentSeries F)ˣ) (s : LaurentSeries F) :
    diagonalRescale F r (lowerRoot F (Multiplicative.ofAdd s)) =
      lowerRoot F (Multiplicative.ofAdd ((((r⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F)) * s)) := by
  apply SL2SymbolExtension.ext
  · exact sl2Rescale_lower r s
  · change 0 + laurentTameHom F (rescaleSymbolCorrection r (sl2Lower s)) = 0
    have hz : rescaleSymbolCorrection r (sl2Lower s) = 0 := by
      classical
      change (if s = 0 then milnorSym2 (LaurentSeries F) r (kubotaUnit (sl2Lower s)) else 0) = 0
      by_cases hs : s = 0
      · rw [hs, if_pos rfl, sl2Lower_zero, kubotaUnit_one, milnorSym2_one_right]
      · rw [if_neg hs]
    rw [hz, map_zero, add_zero]

/-- The lifted backward shift agrees with the constructed affine simple splitting. -/
theorem diagonalRescale_finiteSL2Embedding (g : SL2 F) :
    diagonalRescale F (laurentXUnit F)⁻¹ (finiteSL2Embedding F g) = affineSL2Embedding F g := by
  obtain ⟨x, y, z, w, he⟩ := FiniteRingSl2.exists_four_factors g
  change g = sl2Upper x * sl2Lower y * sl2Upper z * sl2Lower w at he
  rw [he]
  simp only [map_mul, finiteSL2Embedding_upper, finiteSL2Embedding_lower,
    diagonalRescale_upperRoot, diagonalRescale_lowerRoot,
    affineSL2Embedding_upper, affineSL2Embedding_lower, affineUpperParameter,
    affineLowerParameter, inv_inv]

private theorem centralCoordinate_central_mul (c : Fˣ) (g : LoopSL2 F) :
    centralCoordinate F (centralEmbedding F c * g) = c * centralCoordinate F g := by
  change (Additive.ofMul c + g.centralCoord +
    laurentTameHom F (kubotaCocycle 1 g.base)).toMul = _
  rw [kubotaCocycle_one_left, map_zero, add_zero]
  rfl

private theorem centralCoordinate_diagonalRescale (r : (LaurentSeries F)ˣ) (g : LoopSL2 F) :
    centralCoordinate F (diagonalRescale F r g) = centralCoordinate F g *
      (if g.base 1 0 = 0 then laurentTameSymbol F r (kubotaUnit g.base) else 1) := by
  classical
  by_cases hg : g.base 1 0 = 0
  · change (g.centralCoord + laurentTameHom F (rescaleSymbolCorrection r g.base)).toMul = _
    rw [rescaleSymbolCorrection, if_pos hg, laurentTameHom_symbol, if_pos hg]
    rfl
  · change (g.centralCoord + laurentTameHom F (rescaleSymbolCorrection r g.base)).toMul = _
    rw [rescaleSymbolCorrection, if_neg hg, map_zero, add_zero, if_neg hg, mul_one]
    rfl

/-- The exact central discrepancy between the two positive-loop splittings. -/
theorem diagonalRescale_positiveEmbedding (r : (LaurentSeries F)ˣ)
    (p q : PowerSeriesSL2 F)
    (hpq : powerSeriesSL2Map F q = sl2Rescale r (powerSeriesSL2Map F p))
    (hd : PowerSeries.constantCoeff (p 1 1) ≠ 0) :
    diagonalRescale F r (positiveEmbedding F p) =
      centralEmbedding F (laurentTameSymbol F r
        (powerSeriesFieldUnit F (p 1 1) (powerSeries_ne_zero_of_constant F _ hd))) *
          positiveEmbedding F q := by
  classical
  have hqd : q 1 1 = p 1 1 := by
    exact HahnSeries.ofPowerSeries_injective
      (congrArg (fun g : SL2 (LaurentSeries F) => g 1 1) hpq)
  have hqc : (q 1 0 : LaurentSeries F) =
      (((r⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * (p 1 0 : LaurentSeries F)) :=
    congrArg (fun g : SL2 (LaurentSeries F) => g 1 0) hpq
  have hbase : (diagonalRescale F r (positiveEmbedding F p)).base =
      (centralEmbedding F (laurentTameSymbol F r
        (powerSeriesFieldUnit F (p 1 1) (powerSeries_ne_zero_of_constant F _ hd))) *
          positiveEmbedding F q).base := by
    change sl2Rescale r (powerSeriesSL2Map F p) = 1 * powerSeriesSL2Map F q
    rw [one_mul, hpq]
  apply SL2SymbolExtension.ext hbase
  apply Additive.toMul.injective
  change centralCoordinate F (diagonalRescale F r (positiveEmbedding F p)) =
    centralCoordinate F (centralEmbedding F (laurentTameSymbol F r
      (powerSeriesFieldUnit F (p 1 1) (powerSeries_ne_zero_of_constant F _ hd))) *
        positiveEmbedding F q)
  rw [centralCoordinate_diagonalRescale, centralCoordinate_central_mul]
  change powerSeriesRowCorrection F (p 1 0) (p 1 1) *
      (if (powerSeriesSL2Map F p) 1 0 = 0 then
        laurentTameSymbol F r (kubotaUnit (powerSeriesSL2Map F p)) else 1) =
      laurentTameSymbol F r
        (powerSeriesFieldUnit F (p 1 1) (powerSeries_ne_zero_of_constant F _ hd)) *
          powerSeriesRowCorrection F (q 1 0) (q 1 1)
  by_cases hc : p 1 0 = 0
  · have hq0 : q 1 0 = 0 := by
      have hz : (q 1 0 : LaurentSeries F) = ((0 : PowerSeries F) : LaurentSeries F) := by
        simpa only [hc, map_zero, mul_zero] using hqc
      exact HahnSeries.ofPowerSeries_injective hz
    have hpc : (powerSeriesSL2Map F p) 1 0 = 0 := by
      change (p 1 0 : LaurentSeries F) = 0
      rw [hc, map_zero]
    rw [if_pos hpc, kubotaUnit_powerSeries_of_left_zero F p hc
      (powerSeries_ne_zero_of_constant F _ hd), hc, hq0,
      powerSeriesRowCorrection_zero, powerSeriesRowCorrection_zero, one_mul, mul_one]
  · have hpc : (powerSeriesSL2Map F p) 1 0 ≠ 0 := (powerSeriesFieldUnit F (p 1 0) hc).ne_zero
    have hq0 : q 1 0 ≠ 0 := by
      intro hq
      have hn : (q 1 0 : LaurentSeries F) ≠ 0 := by
        rw [hqc]
        exact mul_ne_zero (Units.ne_zero _) hpc
      apply hn
      rw [hq, map_zero]
    have hdq : PowerSeries.constantCoeff (q 1 1) ≠ 0 := by rwa [hqd]
    have hunit : powerSeriesFieldUnit F (q 1 0) hq0 =
        r⁻¹ * powerSeriesFieldUnit F (p 1 0) hc := by
      apply Units.ext
      exact hqc
    have hunitd : powerSeriesFieldUnit F (q 1 1)
        (powerSeries_ne_zero_of_constant F _ hdq) =
        powerSeriesFieldUnit F (p 1 1) (powerSeries_ne_zero_of_constant F _ hd) := by
      apply Units.ext
      exact congrArg (fun f : PowerSeries F => (f : LaurentSeries F)) hqd
    rw [if_neg hpc, mul_one,
      powerSeriesRowCorrection_of_right_unit F _ _ hc hd,
      powerSeriesRowCorrection_of_right_unit F _ _ hq0 hdq, hunit, hunitd,
      laurentTameSymbol_mul_left, laurentTameSymbol_inv_left,
      ← mul_assoc, mul_inv_cancel, one_mul]

end LoopSL2
end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.diagonalRescale_positiveEmbedding

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.diagonalRescale_finiteSL2Embedding
