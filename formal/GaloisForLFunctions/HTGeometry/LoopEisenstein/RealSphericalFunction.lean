import GaloisForLFunctions.HTGeometry.LoopEisenstein.CompactBorelIntersection
import GaloisForLFunctions.HTGeometry.LoopEisenstein.RealBorelCharacters

/-!
# Spherical functions on the real central loop group

The logarithmic Borel characters are trivial on the exact compact–Borel
intersection. Iwasawa existence therefore extends them uniquely to
functions that transform on the left by Borel and are invariant on the
right by the actual generated rotation subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2

noncomputable section

theorem borelWeightCharacter_signTorus (L : AffineA1.Weight) (b : positiveBorel ℝ)
    (hb : (b : LoopSL2 ℝ) ∈ signTorus) : borelWeightCharacter L b = 1 := by
  obtain ⟨⟨c, a⟩, ⟨hc, ha⟩, he⟩ := hb
  have hB : cartanEmbedding ℝ (c, a) ∈ positiveBorel ℝ := he.symm ▸ b.property
  have hb' : b = ⟨cartanEmbedding ℝ (c, a), hB⟩ := Subtype.ext he.symm
  rw [hb', borelWeightCharacter_cartan]
  exact finiteCartanCoordinateCharacter_signs L c a hc ha

/-- The two Borel factors of the same Iwasawa product have the same weight character. -/
theorem borelWeightCharacter_iwasawa_unique (L : AffineA1.Weight)
    (b₁ b₂ : positiveBorel ℝ) (k₁ k₂ : realCompact)
    (he : (b₁ : LoopSL2 ℝ) * k₁ = (b₂ : LoopSL2 ℝ) * k₂) :
    borelWeightCharacter L b₁ = borelWeightCharacter L b₂ := by
  have hd : ((b₂⁻¹ * b₁ : positiveBorel ℝ) : LoopSL2 ℝ) =
      (k₂ : LoopSL2 ℝ) * (k₁ : LoopSL2 ℝ)⁻¹ := by
    change (b₂ : LoopSL2 ℝ)⁻¹ * b₁ = _
    calc
      _ = (b₂ : LoopSL2 ℝ)⁻¹ * ((b₁ : LoopSL2 ℝ) * k₁) * (k₁ : LoopSL2 ℝ)⁻¹ := by group
      _ = (b₂ : LoopSL2 ℝ)⁻¹ * ((b₂ : LoopSL2 ℝ) * k₂) * (k₁ : LoopSL2 ℝ)⁻¹ := by rw [he]
      _ = _ := by group
  have hk : ((b₂⁻¹ * b₁ : positiveBorel ℝ) : LoopSL2 ℝ) ∈ realCompact := by
    rw [hd]
    exact realCompact.mul_mem k₂.property (realCompact.inv_mem k₁.property)
  have hm : ((b₂⁻¹ * b₁ : positiveBorel ℝ) : LoopSL2 ℝ) ∈ signTorus := by
    rw [← realCompact_inf_positiveBorel]
    exact ⟨hk, (b₂⁻¹ * b₁ : positiveBorel ℝ).property⟩
  have hχ := borelWeightCharacter_signTorus L (b₂⁻¹ * b₁) hm
  calc
    borelWeightCharacter L b₁ = borelWeightCharacter L (b₂ * (b₂⁻¹ * b₁)) := by
      congr 1
      group
    _ = borelWeightCharacter L b₂ * borelWeightCharacter L (b₂⁻¹ * b₁) := map_mul _ _ _
    _ = borelWeightCharacter L b₂ := by rw [hχ, mul_one]

theorem exists_iwasawaFactors (g : LoopSL2 ℝ) :
    ∃ p : positiveBorel ℝ × realCompact, (p.1 : LoopSL2 ℝ) * p.2 = g := by
  obtain ⟨b, hb, k, hk, he⟩ := exists_iwasawa g
  exact ⟨(⟨b, hb⟩, ⟨k, hk⟩), he⟩

/-- Choose actual Iwasawa factors; character values do not depend on this choice. -/
def iwasawaFactors (g : LoopSL2 ℝ) : positiveBorel ℝ × realCompact :=
  Classical.choose (exists_iwasawaFactors g)

theorem iwasawaFactors_spec (g : LoopSL2 ℝ) :
    ((iwasawaFactors g).1 : LoopSL2 ℝ) * (iwasawaFactors g).2 = g :=
  Classical.choose_spec (exists_iwasawaFactors g)

/-- The actual loop spherical function associated with a complex affine weight. -/
def sphericalFunction (L : AffineA1.Weight) (g : LoopSL2 ℝ) : ℂ :=
  borelWeightCharacter L (iwasawaFactors g).1

theorem sphericalFunction_ne_zero (L : AffineA1.Weight) (g : LoopSL2 ℝ) :
    sphericalFunction L g ≠ 0 := borelWeightCharacter_ne_zero L _

/-- Evaluation on any Iwasawa factors, not merely the chosen ones. -/
theorem sphericalFunction_of_factors (L : AffineA1.Weight) (g : LoopSL2 ℝ)
    (b : positiveBorel ℝ) (k : realCompact) (he : (b : LoopSL2 ℝ) * k = g) :
    sphericalFunction L g = borelWeightCharacter L b :=
  borelWeightCharacter_iwasawa_unique L (iwasawaFactors g).1 b (iwasawaFactors g).2 k
    ((iwasawaFactors_spec g).trans he.symm)

theorem sphericalFunction_borel (L : AffineA1.Weight) (b : positiveBorel ℝ) :
    sphericalFunction L b = borelWeightCharacter L b :=
  sphericalFunction_of_factors L b b 1 (mul_one _)

@[simp] theorem sphericalFunction_one (L : AffineA1.Weight) : sphericalFunction L 1 = 1 := by
  have h := sphericalFunction_borel L (1 : positiveBorel ℝ)
  simpa only [map_one] using h

/-- Left Borel equivariance with the intrinsic weight character. -/
theorem sphericalFunction_borel_mul (L : AffineA1.Weight) (b : positiveBorel ℝ) (g : LoopSL2 ℝ) :
    sphericalFunction L ((b : LoopSL2 ℝ) * g) =
      borelWeightCharacter L b * sphericalFunction L g := by
  have he : ((b * (iwasawaFactors g).1 : positiveBorel ℝ) : LoopSL2 ℝ) *
      (iwasawaFactors g).2 = (b : LoopSL2 ℝ) * g := by
    change ((b : LoopSL2 ℝ) * (iwasawaFactors g).1) * (iwasawaFactors g).2 = _
    rw [mul_assoc, iwasawaFactors_spec]
  rw [sphericalFunction_of_factors L _ (b * (iwasawaFactors g).1) (iwasawaFactors g).2 he,
    map_mul]
  rfl

/-- Right invariance under the full generated rotation subgroup. -/
theorem sphericalFunction_mul_compact (L : AffineA1.Weight) (g : LoopSL2 ℝ) (k : realCompact) :
    sphericalFunction L (g * (k : LoopSL2 ℝ)) = sphericalFunction L g := by
  have he : ((iwasawaFactors g).1 : LoopSL2 ℝ) *
      ((iwasawaFactors g).2 * k : realCompact) = g * (k : LoopSL2 ℝ) := by
    change ((iwasawaFactors g).1 : LoopSL2 ℝ) *
      ((iwasawaFactors g).2 * (k : LoopSL2 ℝ)) = _
    rw [← mul_assoc, iwasawaFactors_spec]
  exact sphericalFunction_of_factors L _ (iwasawaFactors g).1 ((iwasawaFactors g).2 * k) he

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2
