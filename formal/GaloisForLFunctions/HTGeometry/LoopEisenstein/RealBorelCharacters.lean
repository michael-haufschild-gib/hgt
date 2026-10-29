import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveBorelCoordinates
import GaloisForLFunctions.HTGeometry.LoopEisenstein.RealCartanCharacters

/-!
# Intrinsic weight characters of the real positive Borel

The central and Iwahori factors are unique and multiplicative. Composing
their two torus coordinates with logarithmic absolute-value characters
gives nonvanishing complex characters of the actual positive Borel.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

namespace LoopSL2

variable (F : Type*) [Field F]

/-- The unique central and Iwahori factors of a positive-Borel element. -/
def positiveBorelFactors (g : positiveBorel F) : Fˣ × iwahoriMatrices F :=
  Classical.choose g.property

theorem positiveBorelFactors_spec (g : positiveBorel F) :
    positiveBorelEmbedding F (positiveBorelFactors F g) = (g : LoopSL2 F) :=
  Classical.choose_spec g.property

/-- Inverting the faithful central–Iwahori embedding preserves multiplication. -/
def positiveBorelFactorHom : positiveBorel F →* (Fˣ × iwahoriMatrices F) where
  toFun := positiveBorelFactors F
  map_one' := by
    apply positiveBorelEmbedding_injective F
    rw [positiveBorelFactors_spec, map_one]
    rfl
  map_mul' g h := by
    apply positiveBorelEmbedding_injective F
    rw [positiveBorelFactors_spec, map_mul,
      positiveBorelFactors_spec, positiveBorelFactors_spec]
    rfl

/-- Central and finite-coroot coordinates, after discarding the positive unipotent. -/
def borelTorusHom : positiveBorel F →* (Fˣ × Fˣ) where
  toFun g := ((positiveBorelFactorHom F g).1,
    iwahoriFiniteCoordinate F (positiveBorelFactorHom F g).2)
  map_one' := by rw [map_one]; simp only [Prod.fst_one, Prod.snd_one, map_one]
  map_mul' g h := by
    rw [map_mul]
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]

/-- The intrinsic coordinates recover every actual central/finite Cartan element. -/
theorem borelTorusHom_cartan (c a : Fˣ)
    (hb : cartanEmbedding F (c, a) ∈ positiveBorel F) :
    borelTorusHom F ⟨cartanEmbedding F (c, a), hb⟩ = (c, a) := by
  let g : positiveBorel F := ⟨cartanEmbedding F (c, a), hb⟩
  have he : positiveBorelEmbedding F (positiveBorelFactors F g) =
      positiveBorelEmbedding F (c, iwahoriFiniteCoroot F a) := by
    rw [positiveBorelFactors_spec]
    change centralEmbedding F c * finiteCoroot F a =
      centralEmbedding F c * positiveEmbedding F (iwahoriFiniteCoroot F a)
    rw [positiveEmbedding_iwahoriFiniteCoroot]
  have hp := positiveBorelEmbedding_injective F he
  change ((positiveBorelFactors F g).1,
    iwahoriFiniteCoordinate F (positiveBorelFactors F g).2) = (c, a)
  rw [hp, iwahoriFiniteCoordinate_finiteCoroot]

end LoopSL2

/-- The weight character on central and finite coordinates, with degree coordinate one. -/
def finiteCartanCoordinateCharacter (L : AffineA1.Weight) : (ℝˣ × ℝˣ) →* ℂ where
  toFun p := Complex.exp (L.level * realUnitLog p.1 + L.finite * realUnitLog p.2)
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, realUnitLog_one,
    Complex.ofReal_zero, mul_zero, add_zero, Complex.exp_zero]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, realUnitLog_mul, Complex.ofReal_add]
    rw [show L.level * ((realUnitLog p.1 : ℂ) + realUnitLog q.1) +
        L.finite * ((realUnitLog p.2 : ℂ) + realUnitLog q.2) =
        (L.level * realUnitLog p.1 + L.finite * realUnitLog p.2) +
        (L.level * realUnitLog q.1 + L.finite * realUnitLog q.2) by ring,
      Complex.exp_add]

@[simp] theorem realUnitLog_neg_one : realUnitLog (-1) = 0 := by
  rw [realUnitLog_eq_log_abs]
  simp

theorem finiteCartanCoordinateCharacter_signs (L : AffineA1.Weight) (c a : ℝˣ)
    (hc : c = 1 ∨ c = -1) (ha : a = 1 ∨ a = -1) :
    finiteCartanCoordinateCharacter L (c, a) = 1 := by
  rcases hc with rfl | rfl <;> rcases ha with rfl | rfl <;>
    simp [finiteCartanCoordinateCharacter]

namespace LoopSL2

/-- A genuine nonvanishing complex weight character on the completed positive Borel. -/
def borelWeightCharacter (L : AffineA1.Weight) : positiveBorel ℝ →* ℂ :=
  (finiteCartanCoordinateCharacter L).comp (borelTorusHom ℝ)

theorem borelWeightCharacter_ne_zero (L : AffineA1.Weight) (g : positiveBorel ℝ) :
    borelWeightCharacter L g ≠ 0 := Complex.exp_ne_zero _

theorem borelWeightCharacter_cartan (L : AffineA1.Weight) (c a : ℝˣ)
    (hb : cartanEmbedding ℝ (c, a) ∈ positiveBorel ℝ) :
    borelWeightCharacter L ⟨cartanEmbedding ℝ (c, a), hb⟩ =
      finiteCartanCoordinateCharacter L (c, a) := by
  change finiteCartanCoordinateCharacter L (borelTorusHom ℝ _) = _
  rw [borelTorusHom_cartan]

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
