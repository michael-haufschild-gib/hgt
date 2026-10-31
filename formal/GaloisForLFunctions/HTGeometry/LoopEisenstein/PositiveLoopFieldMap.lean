import GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2FieldMap
import GaloisForLFunctions.HTGeometry.LoopEisenstein.RealBorelCharacters
import GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopBruhatDecomposition

/-!
# Naturality of the positive splitting and Borel torus

Compatibility on upper and lower roots extends through four-root generation
to the full positive-loop splitting. Uniqueness of central–Iwahori factors
then makes both intrinsic Borel torus coordinates natural under field maps.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable {F E : Type*} [Field F] [Field E]

private theorem powerSeries_negative_coeff {R : Type*} [Semiring R] (p : PowerSeries R) (n : ℕ) :
    (HahnSeries.ofPowerSeries ℤ R p).coeff (Int.negSucc n) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨m, hm⟩
  change (m : ℤ) = Int.negSucc n at hm
  omega

/-- Mapping coefficients commutes with the actual power-series inclusion into Laurent series. -/
theorem laurentFieldMap_powerSeries (ι : F →+* E) (p : PowerSeries F) :
    laurentFieldMap ι (p : LaurentSeries F) = (PowerSeries.map ι p : LaurentSeries E) := by
  apply HahnSeries.ext
  funext n
  rw [laurentFieldMap_coeff]
  cases n with
  | ofNat n =>
    exact (congrArg ι (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) p n)).trans
      ((PowerSeries.coeff_map ι n p).symm.trans
        (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (PowerSeries.map ι p) n).symm)
  | negSucc n => rw [powerSeries_negative_coeff, powerSeries_negative_coeff, map_zero]

/-- Entrywise coefficient-field mapping on positive determinant-one matrices. -/
def powerSeriesFieldMatrixMap (ι : F →+* E) : PowerSeriesSL2 F →* PowerSeriesSL2 E :=
  Matrix.SpecialLinearGroup.map (PowerSeries.map ι)

@[simp] theorem powerSeriesFieldMatrixMap_apply (ι : F →+* E) (g : PowerSeriesSL2 F) (i j : Fin 2) :
    powerSeriesFieldMatrixMap ι g i j = PowerSeries.map ι (g i j) := rfl

@[simp] theorem powerSeriesFieldMatrixMap_upper (ι : F →+* E) (p : PowerSeries F) :
    powerSeriesFieldMatrixMap ι (FiniteRingSl2.upper p) = FiniteRingSl2.upper (PowerSeries.map ι p) :=
  FiniteRingSl2.map_upper (PowerSeries.map ι) p

@[simp] theorem powerSeriesFieldMatrixMap_lower (ι : F →+* E) (p : PowerSeries F) :
    powerSeriesFieldMatrixMap ι (FiniteRingSl2.lower p) = FiniteRingSl2.lower (PowerSeries.map ι p) :=
  FiniteRingSl2.map_lower (PowerSeries.map ι) p

/-- The actual Iwahori subgroup is preserved by coefficient-field mapping. -/
def iwahoriFieldMap (ι : F →+* E) : iwahoriMatrices F →* iwahoriMatrices E where
  toFun g := ⟨powerSeriesFieldMatrixMap ι g, by
    apply (mem_iwahoriMatrices E _).mpr
    change ι (PowerSeries.constantCoeff ((g : PowerSeriesSL2 F) 1 0)) = 0
    rw [(mem_iwahoriMatrices F g).mp g.property, map_zero]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

/-- The finite torus coordinate is the mapped constant upper-left entry. -/
theorem iwahoriFiniteCoordinate_fieldMap (ι : F →+* E) (g : iwahoriMatrices F) :
    iwahoriFiniteCoordinate E (iwahoriFieldMap ι g) =
      Units.map ι.toMonoidHom (iwahoriFiniteCoordinate F g) := by
  apply Units.ext
  rfl

namespace LoopSL2

/-- Four-root generation makes the actual positive splitting natural. -/
theorem fieldMap_positiveEmbedding (ι : F →+* E) (g : PowerSeriesSL2 F) :
    fieldMap ι (positiveEmbedding F g) = positiveEmbedding E (powerSeriesFieldMatrixMap ι g) := by
  obtain ⟨x, y, z, w, rfl⟩ := powerSeriesSL2_four_factors F g
  simp only [map_mul, powerSeriesFieldMatrixMap_upper, powerSeriesFieldMatrixMap_lower,
    positiveEmbedding_upper, positiveEmbedding_lower, fieldMap_upperRoot, fieldMap_lowerRoot,
    laurentFieldMap_powerSeries]

/-- Coefficient-field mapping preserves the actual positive Borel in the central extension. -/
theorem fieldMap_mem_positiveBorel (ι : F →+* E) {g : LoopSL2 F} (hg : g ∈ positiveBorel F) :
    fieldMap ι g ∈ positiveBorel E := by
  obtain ⟨⟨c, p⟩, rfl⟩ := hg
  refine ⟨(Units.map ι.toMonoidHom c, iwahoriFieldMap ι p), ?_⟩
  change centralEmbedding E (Units.map ι.toMonoidHom c) *
    positiveEmbedding E (powerSeriesFieldMatrixMap ι p) =
      fieldMap ι (centralEmbedding F c * positiveEmbedding F p)
  rw [map_mul, fieldMap_centralEmbedding, fieldMap_positiveEmbedding]

/-- A faithful coefficient-field map also reflects positive-Borel membership. -/
theorem fieldMap_mem_positiveBorel_iff (ι : F →+* E) (g : LoopSL2 F) :
    fieldMap ι g ∈ positiveBorel E ↔ g ∈ positiveBorel F := by
  constructor
  · intro hg
    have h := (mem_laurentIwahori E _).mp (projection_mem_laurentIwahori E hg)
    apply (mem_positiveBorel_iff_projection F g).mpr
    apply (mem_laurentIwahori F _).mpr
    constructor
    · intro i j
      have hv := h.1 i j
      change laurentValuation E (laurentFieldMap ι (g.base i j)) ≤ 1 at hv
      rw [laurentFieldMap_valuation] at hv
      exact hv
    · have hv := h.2
      change laurentValuation E (laurentFieldMap ι (g.base 1 0)) < 1 at hv
      rw [laurentFieldMap_valuation] at hv
      exact hv
  · exact fieldMap_mem_positiveBorel ι

/-- Restrict the actual central-loop field map to positive Borel. -/
def borelFieldMap (ι : F →+* E) : positiveBorel F →* positiveBorel E where
  toFun b := ⟨fieldMap ι b, fieldMap_mem_positiveBorel ι b.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- Faithful central–Iwahori factorization commutes with the coefficient-field map. -/
theorem positiveBorelFactors_fieldMap (ι : F →+* E) (b : positiveBorel F) :
    positiveBorelFactors E (borelFieldMap ι b) =
      (Units.map ι.toMonoidHom (positiveBorelFactors F b).1,
        iwahoriFieldMap ι (positiveBorelFactors F b).2) := by
  apply positiveBorelEmbedding_injective E
  rw [positiveBorelFactors_spec]
  change fieldMap ι (b : LoopSL2 F) = _
  rw [← positiveBorelFactors_spec F b]
  change fieldMap ι (centralEmbedding F (positiveBorelFactors F b).1 *
    positiveEmbedding F (positiveBorelFactors F b).2) =
      centralEmbedding E (Units.map ι.toMonoidHom (positiveBorelFactors F b).1) *
        positiveEmbedding E (powerSeriesFieldMatrixMap ι (positiveBorelFactors F b).2)
  rw [map_mul, fieldMap_centralEmbedding, fieldMap_positiveEmbedding]

/-- Both intrinsic torus coordinates commute with coefficient-field inclusion. -/
theorem borelTorusHom_fieldMap (ι : F →+* E) (b : positiveBorel F) :
    borelTorusHom E (borelFieldMap ι b) =
      (Units.map ι.toMonoidHom (borelTorusHom F b).1,
        Units.map ι.toMonoidHom (borelTorusHom F b).2) := by
  change ((positiveBorelFactors E (borelFieldMap ι b)).1,
    iwahoriFiniteCoordinate E (positiveBorelFactors E (borelFieldMap ι b)).2) =
      (Units.map ι.toMonoidHom (positiveBorelFactors F b).1,
        Units.map ι.toMonoidHom (iwahoriFiniteCoordinate F (positiveBorelFactors F b).2))
  rw [positiveBorelFactors_fieldMap, iwahoriFiniteCoordinate_fieldMap]

end LoopSL2
end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.fieldMap_positiveEmbedding
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.borelTorusHom_fieldMap

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.fieldMap_mem_positiveBorel_iff
