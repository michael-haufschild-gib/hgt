import GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2Rotation
import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveLoopFieldMap

/-!
# Degree rotation of the positive central splitting

Power-series rescaling agrees with Laurent rotation coefficientwise.
Four-root generation extends compatibility to the actual positive central
lift. The central and constant Iwahori coordinates are unchanged, so degree
rotation fixes both intrinsic positive-Borel spectral coordinates.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable {F : Type*} [Field F]

private theorem powerSeries_coeff_negative (p : PowerSeries F) (n : ℕ) :
    (HahnSeries.ofPowerSeries ℤ F p).coeff (Int.negSucc n) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨m, hm⟩
  change (m : ℤ) = Int.negSucc n at hm
  omega

/-- Actual Laurent rotation restricts to power-series rescaling. -/
theorem laurentRotation_powerSeries (q : Fˣ) (p : PowerSeries F) :
    laurentRotation q (p : LaurentSeries F) =
      (PowerSeries.rescale (q : F) p : LaurentSeries F) := by
  apply HahnSeries.ext
  funext n
  rw [laurentRotation_coeff]
  cases n with
  | ofNat n =>
    have hq : ((q ^ (n : ℤ) : Fˣ) : F) = (q : F) ^ n :=
      (Units.val_zpow_eq_zpow_val q (n : ℤ)).trans (zpow_natCast (q : F) n)
    calc
      ((q ^ (n : ℤ) : Fˣ) : F) * (p : LaurentSeries F).coeff n =
          (q : F) ^ n * PowerSeries.coeff n p :=
        congrArg₂ (fun a b : F => a * b) hq
          (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) p n)
      _ = PowerSeries.coeff n (PowerSeries.rescale (q : F) p) :=
        (PowerSeries.coeff_rescale p (q : F) n).symm
      _ = _ := (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ)
        (PowerSeries.rescale (q : F) p) n).symm
  | negSucc n => rw [powerSeries_coeff_negative, powerSeries_coeff_negative, mul_zero]

private theorem rescale_constantCoeff (q : F) (p : PowerSeries F) :
    PowerSeries.constantCoeff (PowerSeries.rescale q p) = PowerSeries.constantCoeff p := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
    pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Entrywise rescaling of the power-series variable. -/
def powerSeriesRotation (q : Fˣ) : PowerSeriesSL2 F →* PowerSeriesSL2 F :=
  Matrix.SpecialLinearGroup.map (PowerSeries.rescale (q : F))

theorem powerSeriesRotation_upper (q : Fˣ) (p : PowerSeries F) :
    powerSeriesRotation q (FiniteRingSl2.upper p) =
      FiniteRingSl2.upper (PowerSeries.rescale (q : F) p) :=
  FiniteRingSl2.map_upper (PowerSeries.rescale (q : F)) p

theorem powerSeriesRotation_lower (q : Fˣ) (p : PowerSeries F) :
    powerSeriesRotation q (FiniteRingSl2.lower p) =
      FiniteRingSl2.lower (PowerSeries.rescale (q : F) p) :=
  FiniteRingSl2.map_lower (PowerSeries.rescale (q : F)) p

/-- Rescaling preserves the actual positive Iwahori matrix group. -/
def iwahoriRotation (q : Fˣ) : iwahoriMatrices F →* iwahoriMatrices F where
  toFun p := ⟨powerSeriesRotation q p, by
    apply (mem_iwahoriMatrices F _).mpr
    change PowerSeries.constantCoeff (PowerSeries.rescale (q : F) (p.1 1 0)) = 0
    rw [rescale_constantCoeff]
    exact (mem_iwahoriMatrices F p).mp p.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem iwahoriFiniteCoordinate_rotation (q : Fˣ) (p : iwahoriMatrices F) :
    iwahoriFiniteCoordinate F (iwahoriRotation q p) = iwahoriFiniteCoordinate F p := by
  apply Units.ext
  exact rescale_constantCoeff (q : F) (p.1 0 0)

namespace LoopSL2

/-- The canonical positive central splitting commutes with actual degree rotation. -/
theorem rotation_positiveEmbedding (q : Fˣ) (p : PowerSeriesSL2 F) :
    rotation q (positiveEmbedding F p) = positiveEmbedding F (powerSeriesRotation q p) := by
  obtain ⟨x, y, z, w, rfl⟩ := powerSeriesSL2_four_factors F p
  simp only [map_mul, powerSeriesRotation_upper, powerSeriesRotation_lower,
    positiveEmbedding_upper, positiveEmbedding_lower, rotation_upperRoot, rotation_lowerRoot,
    laurentRotation_powerSeries]

/-- Actual degree rotation preserves the positive Borel in the central extension. -/
theorem rotation_mem_positiveBorel (q : Fˣ) {g : LoopSL2 F}
    (hg : g ∈ positiveBorel F) : rotation q g ∈ positiveBorel F := by
  obtain ⟨⟨c, p⟩, rfl⟩ := hg
  refine ⟨(c, iwahoriRotation q p), ?_⟩
  change centralEmbedding F c * positiveEmbedding F (powerSeriesRotation q p) =
    rotation q (centralEmbedding F c * positiveEmbedding F p)
  rw [map_mul, rotation_centralEmbedding, rotation_positiveEmbedding]

/-- Restrict the actual degree automorphism to the positive Borel. -/
def borelRotation (q : Fˣ) : positiveBorel F →* positiveBorel F where
  toFun b := ⟨rotation q b, rotation_mem_positiveBorel q b.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem positiveBorelFactors_rotation (q : Fˣ) (b : positiveBorel F) :
    positiveBorelFactors F (borelRotation q b) =
      ((positiveBorelFactors F b).1, iwahoriRotation q (positiveBorelFactors F b).2) := by
  apply positiveBorelEmbedding_injective F
  rw [positiveBorelFactors_spec]
  change rotation q (b : LoopSL2 F) = _
  rw [← positiveBorelFactors_spec F b]
  change rotation q (centralEmbedding F (positiveBorelFactors F b).1 *
    positiveEmbedding F (positiveBorelFactors F b).2) =
      centralEmbedding F (positiveBorelFactors F b).1 *
        positiveEmbedding F (powerSeriesRotation q (positiveBorelFactors F b).2)
  rw [map_mul, rotation_centralEmbedding, rotation_positiveEmbedding]

/-- Both intrinsic Borel torus coordinates are invariant under degree rotation. -/
theorem borelTorusHom_rotation (q : Fˣ) (b : positiveBorel F) :
    borelTorusHom F (borelRotation q b) = borelTorusHom F b := by
  change ((positiveBorelFactors F (borelRotation q b)).1,
    iwahoriFiniteCoordinate F (positiveBorelFactors F (borelRotation q b)).2) =
      ((positiveBorelFactors F b).1, iwahoriFiniteCoordinate F (positiveBorelFactors F b).2)
  rw [positiveBorelFactors_rotation, iwahoriFiniteCoordinate_rotation]

end LoopSL2
end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.rotation_positiveEmbedding
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.rotation_mem_positiveBorel
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.borelTorusHom_rotation
