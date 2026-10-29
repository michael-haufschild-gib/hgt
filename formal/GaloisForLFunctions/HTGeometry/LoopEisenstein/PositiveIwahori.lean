import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveLoopSplitting
import GaloisForLFunctions.HTGeometry.BorelWeil.BorelSubgroup

/-!
# Positive Iwahori and unipotent loop subgroups

Reduction by constant coefficient defines the Iwahori and its unipotent
radical inside the full power-series group. The canonical central lift of the
unipotent radical has zero additive central coordinate: its right diagonal
entry is a principal unit, whose tame pairings are all trivial.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- Reduction of a positive loop to its constant matrix. -/
def powerSeriesReduction : PowerSeriesSL2 F →* SL2 F :=
  Matrix.SpecialLinearGroup.map (PowerSeries.constantCoeff (R := F))

@[simp] theorem powerSeriesReduction_apply (g : PowerSeriesSL2 F) (i j : Fin 2) :
    powerSeriesReduction F g i j = PowerSeries.constantCoeff (g i j) := rfl

/-- The positive Iwahori is the inverse image of the finite upper Borel. -/
def iwahoriMatrices : Subgroup (PowerSeriesSL2 F) :=
  (BorelWeil.borel (Fin 2) F).comap (powerSeriesReduction F)

theorem mem_iwahoriMatrices (g : PowerSeriesSL2 F) :
    g ∈ iwahoriMatrices F ↔ PowerSeries.constantCoeff (g 1 0) = 0 := by
  change ((powerSeriesReduction F g : Matrix (Fin 2) (Fin 2) F).BlockTriangular id) ↔ _
  constructor
  · intro h
    exact h (show (0 : Fin 2) < 1 by norm_num)
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all [powerSeriesReduction_apply]

/-- The completed positive unipotent matrices reduce to the finite upper root group. -/
def positiveUnipotentMatrices : Subgroup (PowerSeriesSL2 F) :=
  (FiniteRingSl2.upperHom (R := F)).range.comap (powerSeriesReduction F)

private theorem mem_upper_range (g : SL2 F) :
    g ∈ (FiniteRingSl2.upperHom (R := F)).range ↔ g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1 := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨ha, hc, hd⟩
    refine ⟨Multiplicative.ofAdd (g 0 1), ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [FiniteRingSl2.upperHom, FiniteRingSl2.upper, ha, hc, hd]

/-- Entrywise characterization of the full positive unipotent group. -/
theorem mem_positiveUnipotentMatrices (g : PowerSeriesSL2 F) :
    g ∈ positiveUnipotentMatrices F ↔
      PowerSeries.constantCoeff (g 0 0) = 1 ∧
        PowerSeries.constantCoeff (g 1 0) = 0 ∧ PowerSeries.constantCoeff (g 1 1) = 1 := by
  change powerSeriesReduction F g ∈ (FiniteRingSl2.upperHom (R := F)).range ↔ _
  rw [mem_upper_range]
  rfl

theorem positiveUnipotentMatrices_le_iwahori : positiveUnipotentMatrices F ≤ iwahoriMatrices F := by
  intro g hg
  exact (mem_iwahoriMatrices F g).2 ((mem_positiveUnipotentMatrices F g).1 hg).2.1

theorem upper_mem_positiveUnipotentMatrices (s : PowerSeries F) :
    FiniteRingSl2.upper s ∈ positiveUnipotentMatrices F := by
  rw [mem_positiveUnipotentMatrices]
  simp [FiniteRingSl2.upper]

theorem lower_mem_positiveUnipotentMatrices (s : PowerSeries F)
    (hs : PowerSeries.constantCoeff s = 0) :
    FiniteRingSl2.lower s ∈ positiveUnipotentMatrices F := by
  rw [mem_positiveUnipotentMatrices]
  simp [FiniteRingSl2.lower, hs]

/-- A principal right entry makes the positive-loop correction trivial. -/
theorem powerSeriesRowCorrection_principal_right (c d : PowerSeries F)
    (hd : PowerSeries.constantCoeff d = 1) : powerSeriesRowCorrection F c d = 1 := by
  by_cases hc : c = 0
  · rw [hc, powerSeriesRowCorrection_zero]
  have hd₀ : PowerSeries.constantCoeff d ≠ 0 := by
    rw [hd]
    exact one_ne_zero
  rw [powerSeriesRowCorrection_of_right_unit F c d hc hd₀,
    powerSeriesFieldUnit_eq_laurentUnit F d _ hd₀]
  apply laurentTameSymbol_principalUnit_right
  apply Units.ext
  simpa only [coe_powerSeriesResidueUnit, coe_powerSeriesUnitOfConstant, Units.val_one] using hd

namespace LoopSL2

/-- The Iwahori subgroup embedded by the actual positive-loop splitting. -/
def iwahoriSubgroup : Subgroup (LoopSL2 F) := (iwahoriMatrices F).map (positiveEmbedding F)

/-- The full positive unipotent subgroup inside the central loop group. -/
def positiveUnipotent : Subgroup (LoopSL2 F) :=
  (positiveUnipotentMatrices F).map (positiveEmbedding F)

theorem positiveEmbedding_unipotent_centralCoord (g : PowerSeriesSL2 F)
    (hg : g ∈ positiveUnipotentMatrices F) : (positiveEmbedding F g).centralCoord = 0 := by
  change Additive.ofMul (powerSeriesRowCorrection F (g 1 0) (g 1 1)) = 0
  rw [powerSeriesRowCorrection_principal_right F _ _
    ((mem_positiveUnipotentMatrices F g).1 hg).2.2]
  rfl

/-- The unipotent splitting is exactly the zero-coordinate matrix section. -/
theorem positiveEmbedding_unipotent_eq_section (g : positiveUnipotentMatrices F) :
    positiveEmbedding F g = SL2SymbolExtension.sectionOf (laurentTameHom F)
      (powerSeriesSL2Map F g) := by
  apply SL2SymbolExtension.ext
  · rfl
  · exact positiveEmbedding_unipotent_centralCoord F g g.property

/-- The actual tame cocycle is trivial on the positive unipotent subgroup. -/
theorem positiveUnipotent_tameFactor (g h : positiveUnipotentMatrices F) :
    powerSeriesKubotaFactor F g h = 1 := by
  have hm := congrArg SL2SymbolExtension.centralCoord
    (map_mul (positiveEmbedding F) (g : PowerSeriesSL2 F) (h : PowerSeriesSL2 F))
  rw [SL2SymbolExtension.centralCoord_mul,
    positiveEmbedding_unipotent_centralCoord F _ ((positiveUnipotentMatrices F).mul_mem g.property h.property),
    positiveEmbedding_unipotent_centralCoord F _ g.property,
    positiveEmbedding_unipotent_centralCoord F _ h.property, zero_add, zero_add] at hm
  apply Additive.ofMul.injective
  rw [powerSeriesKubotaFactor_eq]
  change laurentTameHom F (kubotaCocycle (powerSeriesSL2Map F g) (powerSeriesSL2Map F h)) = 0
  exact hm.symm

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
