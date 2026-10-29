import GaloisForLFunctions.HTGeometry.LoopEisenstein.IwahoriBruhatUniqueness
import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveBorelCoordinates
import GaloisForLFunctions.HTGeometry.LoopEisenstein.ExtendedCartanConjugation

/-!
# Affine Bruhat decomposition of the actual central loop group

The positive Borel is exactly the inverse image of the matrix Iwahori.
Its central kernel absorbs the discrepancy between lifted matrix factors,
so the unique affine Weyl double-coset decomposition lifts to the constructed
central extension without an additional group-theoretic assumption.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

namespace LoopSL2

/-- Representatives built from the actual monomial translation and finite Weyl lift. -/
def affineWeylLift : AffineA1.Weyl → LoopSL2 F
  | .r m => translationLift F (show ℤ from m)
  | .sr m => finiteWeylLift F * translationLift F (show ℤ from m)

theorem projection_affineWeylLift (w : AffineA1.Weyl) :
    projection F (affineWeylLift F w) = affineWeylMatrix F w := by
  cases w with
  | r m => rfl
  | sr m =>
    rw [affineWeylLift, map_mul]
    change sl2WeylLower 1 * sl2Diagonal (laurentXUnit F ^ (-(show ℤ from m))) =
      sl2WeylLower (laurentXUnit F ^ (-(show ℤ from m)))
    rw [sl2WeylLower_mul_diagonal, one_mul]

/-- Equality of actual positive-Borel double cosets in the central loop group. -/
def borelEquivalent (g h : LoopSL2 F) : Prop :=
  ∃ l ∈ positiveBorel F, ∃ r ∈ positiveBorel F, l * g * r = h

theorem positiveEmbedding_mem_positiveBorel (p : PowerSeriesSL2 F) (hp : p ∈ iwahoriMatrices F) :
    positiveEmbedding F p ∈ positiveBorel F := by
  refine ⟨(1, ⟨p, hp⟩), ?_⟩
  change centralEmbedding F 1 * positiveEmbedding F p = positiveEmbedding F p
  rw [map_one, one_mul]

theorem projection_mem_laurentIwahori {g : LoopSL2 F} (hg : g ∈ positiveBorel F) :
    projection F g ∈ laurentIwahori F := by
  obtain ⟨⟨c, p⟩, rfl⟩ := hg
  change projection F (centralEmbedding F c * positiveEmbedding F p) ∈ laurentIwahori F
  rw [map_mul, projection_centralEmbedding, one_mul, projection_positiveEmbedding]
  exact ⟨p, p.property, rfl⟩

/-- The positive Borel is precisely the full inverse image of the matrix Iwahori. -/
theorem mem_positiveBorel_iff_projection (g : LoopSL2 F) :
    g ∈ positiveBorel F ↔ projection F g ∈ laurentIwahori F := by
  constructor
  · exact projection_mem_laurentIwahori F
  · rintro ⟨p, hp, hproj⟩
    have hk : g * (positiveEmbedding F p)⁻¹ ∈ (projection F).ker := by
      change projection F (g * (positiveEmbedding F p)⁻¹) = 1
      rw [map_mul, map_inv, projection_positiveEmbedding, hproj, mul_inv_cancel]
    rw [projection_ker_eq_range] at hk
    obtain ⟨c, hc⟩ := hk
    refine ⟨(c, ⟨p, hp⟩), ?_⟩
    change centralEmbedding F c * positiveEmbedding F p = g
    rw [hc]
    group

theorem centralEmbedding_mem_positiveBorel (c : Fˣ) : centralEmbedding F c ∈ positiveBorel F := by
  apply (mem_positiveBorel_iff_projection F _).2
  rw [projection_centralEmbedding]
  exact (laurentIwahori F).one_mem

/-- Every Iwahori matrix has its canonical lift in the positive Borel. -/
theorem exists_positiveBorel_lift (i : SL2 (LaurentSeries F)) (hi : i ∈ laurentIwahori F) :
    ∃ b ∈ positiveBorel F, projection F b = i := by
  obtain ⟨p, hp, hpi⟩ := hi
  exact ⟨positiveEmbedding F p, positiveEmbedding_mem_positiveBorel F p hp,
    (projection_positiveEmbedding F p).trans hpi⟩

theorem borelEquivalent_projection {g h : LoopSL2 F} (hgh : borelEquivalent F g h) :
    iwahoriEquivalent F (projection F g) (projection F h) := by
  obtain ⟨l, hl, r, hr, h⟩ := hgh
  refine ⟨projection F l, projection_mem_laurentIwahori F hl,
    projection F r, projection_mem_laurentIwahori F hr, ?_⟩
  rw [← map_mul, ← map_mul, h]

/-- Central exactness lifts the full matrix Bruhat decomposition to the loop group. -/
theorem exists_bruhat (g : LoopSL2 F) :
    ∃ w : AffineA1.Weyl, borelEquivalent F g (affineWeylLift F w) := by
  obtain ⟨w, l, hl, r, hr, hw⟩ := exists_iwahori_bruhat F (projection F g)
  obtain ⟨l', hlB, hl'⟩ := exists_positiveBorel_lift F l hl
  obtain ⟨r', hrB, hr'⟩ := exists_positiveBorel_lift F r hr
  have he : projection F (l' * g * r') = projection F (affineWeylLift F w) := by
    rw [map_mul, map_mul, hl', hr', projection_affineWeylLift]
    exact hw
  let k := affineWeylLift F w * (l' * g * r')⁻¹
  have hk : k ∈ positiveBorel F := by
    apply (mem_positiveBorel_iff_projection F k).2
    have hkp : projection F k = 1 := by
      change projection F (affineWeylLift F w * (l' * g * r')⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    rw [hkp]
    exact (laurentIwahori F).one_mem
  refine ⟨w, k * l', (positiveBorel F).mul_mem hk hlB, r', hrB, ?_⟩
  change (affineWeylLift F w * (l' * g * r')⁻¹) * l' * g * r' = affineWeylLift F w
  group

/-- No two distinct affine Weyl elements have the same positive-Borel double coset. -/
theorem borelEquivalent_affineWeyl_iff (w v : AffineA1.Weyl) :
    borelEquivalent F (affineWeylLift F w) (affineWeylLift F v) ↔ w = v := by
  constructor
  · intro h
    have hp := borelEquivalent_projection F h
    rw [projection_affineWeylLift, projection_affineWeylLift] at hp
    exact (iwahoriEquivalent_affineWeyl_iff F w v).1 hp
  · rintro rfl
    exact ⟨1, (positiveBorel F).one_mem, 1, (positiveBorel F).one_mem, by rw [one_mul, mul_one]⟩

/-- Every element of the actual central loop group has a unique affine Weyl Bruhat label. -/
theorem exists_unique_bruhat (g : LoopSL2 F) :
    ∃! w : AffineA1.Weyl, borelEquivalent F g (affineWeylLift F w) := by
  obtain ⟨w, hw⟩ := exists_bruhat F g
  refine ⟨w, hw, ?_⟩
  intro v hv
  have hwp := borelEquivalent_projection F hw
  have hvp := borelEquivalent_projection F hv
  rw [projection_affineWeylLift] at hwp hvp
  exact (iwahoriEquivalent_affineWeyl_iff F v w).1
    (iwahoriEquivalent_trans F (iwahoriEquivalent_symm F hvp) hwp)

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
