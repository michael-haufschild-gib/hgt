import GaloisForLFunctions.HTGeometry.LoopEisenstein.IwahoriTorusFactorization
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1Coroots

/-!
# Central, finite-torus, and unipotent coordinates on the positive Borel

The center and the split Iwahori embed as a direct product. Factoring the
Iwahori by its constant diagonal gives unique central, finite-coroot, and
completed-unipotent coordinates on the resulting positive Borel subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

namespace LoopSL2

theorem positiveEmbedding_diagonal (a : (PowerSeries F)ˣ) :
    positiveEmbedding F (powerSeriesDiagonal F a) =
      diagonalSection F (powerSeriesLaurentUnit F a) := by
  apply SL2SymbolExtension.ext
  · change powerSeriesSL2Map F (powerSeriesDiagonal F a) =
      sl2Diagonal (powerSeriesLaurentUnit F a)
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [powerSeriesSL2Map_apply, powerSeriesDiagonal, sl2Diagonal, powerSeriesLaurentUnit]
  · change Additive.ofMul (powerSeriesRowCorrection F 0
      ((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F)) = 0
    rw [powerSeriesRowCorrection_zero]
    rfl

/-- The constant diagonal in the split Iwahori is the finite coroot built from root words. -/
theorem positiveEmbedding_iwahoriFiniteCoroot (a : Fˣ) :
    positiveEmbedding F (iwahoriFiniteCoroot F a) = finiteCoroot F a := by
  have hu : powerSeriesLaurentUnit F (powerSeriesConstantUnit F a) = laurentConstantUnit F a := by
    apply Units.ext
    rfl
  change positiveEmbedding F (powerSeriesDiagonal F (powerSeriesConstantUnit F a)) = _
  rw [positiveEmbedding_diagonal, hu, finiteCoroot_apply]

/-- Independent central and Iwahori factors inside the actual central loop group. -/
def positiveBorelEmbedding : Fˣ × iwahoriMatrices F →* LoopSL2 F where
  toFun p := centralEmbedding F p.1 * positiveEmbedding F p.2
  map_one' := by
    change centralEmbedding F 1 * positiveEmbedding F 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' p q := by
    change centralEmbedding F (p.1 * q.1) *
      positiveEmbedding F ((p.2 : PowerSeriesSL2 F) * (q.2 : PowerSeriesSL2 F)) =
      (centralEmbedding F p.1 * positiveEmbedding F p.2) *
        (centralEmbedding F q.1 * positiveEmbedding F q.2)
    rw [map_mul, map_mul]
    have hc : centralEmbedding F q.1 * positiveEmbedding F p.2 =
        positiveEmbedding F p.2 * centralEmbedding F q.1 :=
      SL2SymbolExtension.centralEmbedding_commute
        (Multiplicative.ofAdd (Additive.ofMul q.1)) (positiveEmbedding F p.2)
    calc
      _ = centralEmbedding F p.1 * (centralEmbedding F q.1 * positiveEmbedding F p.2) *
          positiveEmbedding F q.2 := by simp only [mul_assoc]
      _ = centralEmbedding F p.1 * (positiveEmbedding F p.2 * centralEmbedding F q.1) *
          positiveEmbedding F q.2 := by rw [hc]
      _ = _ := by simp only [mul_assoc]

theorem positiveBorelEmbedding_injective : Function.Injective (positiveBorelEmbedding F) := by
  intro p q h
  have hb : (p.2 : PowerSeriesSL2 F) = (q.2 : PowerSeriesSL2 F) := by
    apply powerSeriesSL2Map_injective F
    have hp := congrArg (projection F) h
    change projection F (centralEmbedding F p.1 * positiveEmbedding F p.2) =
      projection F (centralEmbedding F q.1 * positiveEmbedding F q.2) at hp
    simpa only [map_mul, projection_centralEmbedding, projection_positiveEmbedding, one_mul] using hp
  have hbi : p.2 = q.2 := Subtype.ext hb
  have hc : p.1 = q.1 := by
    apply centralEmbedding_injective F
    change centralEmbedding F p.1 * positiveEmbedding F p.2 =
      centralEmbedding F q.1 * positiveEmbedding F q.2 at h
    rw [hbi] at h
    exact mul_right_cancel h
  exact Prod.ext hc hbi

/-- The completed positive Borel, as an actual subgroup of the central loop group. -/
def positiveBorel : Subgroup (LoopSL2 F) := (positiveBorelEmbedding F).range

/-- Central unit, finite-coroot unit, and full positive unipotent matrix. -/
abbrev BorelCoordinates := Fˣ × (Fˣ × positiveUnipotentMatrices F)

/-- Evaluate the three positive-Borel factors in the central loop group. -/
def borelCoordinateMap (p : BorelCoordinates F) : LoopSL2 F :=
  centralEmbedding F p.1 * finiteCoroot F p.2.1 * positiveEmbedding F p.2.2

theorem borelCoordinateMap_eq (p : BorelCoordinates F) :
    borelCoordinateMap F p =
      positiveBorelEmbedding F (p.1, iwahoriTorusUnipotentEquiv F p.2) := by
  change centralEmbedding F p.1 * finiteCoroot F p.2.1 * positiveEmbedding F p.2.2 =
    centralEmbedding F p.1 * positiveEmbedding F
      ((iwahoriFiniteCoroot F p.2.1 : PowerSeriesSL2 F) * (p.2.2 : PowerSeriesSL2 F))
  rw [map_mul, positiveEmbedding_iwahoriFiniteCoroot, mul_assoc]

/-- All three positive-Borel coordinates are uniquely determined by the group element. -/
theorem borelCoordinateMap_injective : Function.Injective (borelCoordinateMap F) := by
  intro p q h
  rw [borelCoordinateMap_eq, borelCoordinateMap_eq] at h
  have hpq := positiveBorelEmbedding_injective F h
  have hc := congrArg Prod.fst hpq
  have hu := (iwahoriTorusUnipotentEquiv F).injective (congrArg Prod.snd hpq)
  exact Prod.ext hc hu

theorem mem_positiveBorel_iff (g : LoopSL2 F) :
    g ∈ positiveBorel F ↔ ∃ p : BorelCoordinates F, borelCoordinateMap F p = g := by
  constructor
  · rintro ⟨⟨c, b⟩, hb⟩
    refine ⟨(c, (iwahoriFiniteCoordinate F b, iwahoriUnipotentPart F b)), ?_⟩
    rw [borelCoordinateMap_eq]
    change positiveBorelEmbedding F (c, iwahoriFiniteCoroot F (iwahoriFiniteCoordinate F b) *
      positiveUnipotentToIwahori F (iwahoriUnipotentPart F b)) = g
    rw [iwahori_torus_unipotent]
    exact hb
  · rintro ⟨p, hp⟩
    refine ⟨(p.1, iwahoriTorusUnipotentEquiv F p.2), ?_⟩
    exact (borelCoordinateMap_eq F p).symm.trans hp

/-- Exact central/finite/unipotent factorization on the completed positive Borel. -/
theorem positiveBorel_unique_coordinates (g : positiveBorel F) :
    ∃! p : BorelCoordinates F, borelCoordinateMap F p = (g : LoopSL2 F) := by
  obtain ⟨p, hp⟩ := (mem_positiveBorel_iff F g).1 g.property
  exact ⟨p, hp, fun q hq => borelCoordinateMap_injective F (hq.trans hp.symm)⟩

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
