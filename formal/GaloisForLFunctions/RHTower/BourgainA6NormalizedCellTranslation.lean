/-
# Translation-uniform sharp normalized A6 cells

Translation in physical phase space twists every coefficient by a unit
character.  Consequently the sharp exact-curve cell estimate is uniform
over all translates, with both Jacobians unchanged.
-/
import GaloisForLFunctions.RHTower.BourgainA6NormalizedCellTransfer

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Translate one physical fundamental cell in phase space. -/
def bourgainA6TranslatedAffinePhysicalFundamentalCell
    (H : ℕ) (G N₀ M D a b : ℝ) (y : BourgainPhaseSpace) :
    Set BourgainPhaseSpace :=
  (fun x => x + y) ''
    bourgainA6AffinePhysicalFundamentalCell H G N₀ M D a b

/-- Translation invariance of a set integral over the affine physical
fundamental cell. -/
theorem setLIntegral_bourgainA6TranslatedAffinePhysicalFundamentalCell
    (H : ℕ) (G N₀ M D a b : ℝ) (y : BourgainPhaseSpace)
    (f : BourgainPhaseSpace → ENNReal) :
    (∫⁻ z in bourgainA6TranslatedAffinePhysicalFundamentalCell
        H G N₀ M D a b y, f z) =
      ∫⁻ x in bourgainA6AffinePhysicalFundamentalCell
          H G N₀ M D a b,
        f (x + y) := by
  symm
  exact
    (measurePreserving_add_right volume y).setLIntegral_comp_emb
      (Homeomorph.addRight y).isClosedEmbedding.measurableEmbedding
      f (bourgainA6AffinePhysicalFundamentalCell
        H G N₀ M D a b)

/-- Coefficient twist induced by physical phase-space translation. -/
def bourgainA6AffinePhysicalLocalTranslateCoefficients
    (H : ℕ) (G N₀ M D a : ℝ) (c : Fin H → ℂ)
    (y : BourgainPhaseSpace) : Fin H → ℂ :=
  fun n =>
    c n * bourgainUnitCharacter
      (bourgainDot y
        (bourgainA6AffinePhysicalCurve G N₀ M
          (a + (bourgainIndex n : ℝ) / D)))

@[simp] theorem
    norm_bourgainA6AffinePhysicalLocalTranslateCoefficients
    (H : ℕ) (G N₀ M D a : ℝ) (c : Fin H → ℂ)
    (y : BourgainPhaseSpace) (n : Fin H) :
    ‖bourgainA6AffinePhysicalLocalTranslateCoefficients
        H G N₀ M D a c y n‖ = ‖c n‖ := by
  rw [bourgainA6AffinePhysicalLocalTranslateCoefficients, norm_mul,
    norm_bourgainUnitCharacter, mul_one]

/-- Translation of the phase variable is exactly coefficient twisting. -/
theorem bourgainA6AffinePhysicalLocalSum_add
    (H : ℕ) (G N₀ M D a : ℝ) (c : Fin H → ℂ)
    (x y : BourgainPhaseSpace) :
    bourgainA6AffinePhysicalLocalSum H G N₀ M D a c (x + y) =
      bourgainA6AffinePhysicalLocalSum H G N₀ M D a
        (bourgainA6AffinePhysicalLocalTranslateCoefficients
          H G N₀ M D a c y) x := by
  unfold bourgainA6AffinePhysicalLocalSum
  apply Fintype.sum_congr
  intro n
  have hdot :
      bourgainDot (x + y)
          (bourgainA6AffinePhysicalCurve G N₀ M
            (a + (bourgainIndex n : ℝ) / D)) =
        bourgainDot x
            (bourgainA6AffinePhysicalCurve G N₀ M
              (a + (bourgainIndex n : ℝ) / D)) +
          bourgainDot y
            (bourgainA6AffinePhysicalCurve G N₀ M
              (a + (bourgainIndex n : ℝ) / D)) := by
    unfold bourgainDot
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hdot, bourgainUnitCharacter_add]
  unfold bourgainA6AffinePhysicalLocalTranslateCoefficients
  ring

/-- The coefficient `ℓ²` mass is invariant under physical translation. -/
theorem sum_norm_sq_bourgainA6AffinePhysicalLocalTranslateCoefficients
    (H : ℕ) (G N₀ M D a : ℝ) (c : Fin H → ℂ)
    (y : BourgainPhaseSpace) :
    (∑ n : Fin H,
      ‖bourgainA6AffinePhysicalLocalTranslateCoefficients
        H G N₀ M D a c y n‖ ^ (2 : ℕ)) =
      ∑ n : Fin H, ‖c n‖ ^ (2 : ℕ) := by
  apply Fintype.sum_congr
  intro n
  rw [norm_bourgainA6AffinePhysicalLocalTranslateCoefficients]

/-- Translation-uniform sharp bilinear sixth moment for two literal affine
`A₆` blocks. -/
theorem
    setLIntegral_bourgainA6AffinePhysicalLocalSum_translatedCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (_hH : 0 < H)
        {G N₀ M D a b : ℝ}
        (_hG : 0 < G) (_hN₀ : 0 < N₀) (_hM : 0 < M)
        (_hq1 : M / N₀ ≤ 1 / 2)
        (_hD : 0 < D) (_hHD : (H : ℝ) ≤ D)
        (_ha0 : 0 ≤ a) (_ha1 : a + (H : ℝ) / D ≤ 1)
        (_hb0 : 0 ≤ b) (_hb1 : b + (H : ℝ) / D ≤ 1)
        (_hab : 1 / 4 ≤ b - a)
        (_hsmall :
          50331648000 * (H : ℝ) ^ (3 : ℕ) / D ≤ 1 / 24)
        (c₁ c₂ : Fin H → ℂ) (y : BourgainPhaseSpace),
        (∫⁻ x in bourgainA6TranslatedAffinePhysicalFundamentalCell
            H G N₀ M D a b y,
          ENNReal.ofReal
            (‖bourgainA6AffinePhysicalLocalSum
                H G N₀ M D a c₁ x‖ ^ (6 : ℕ) *
              ‖bourgainA6AffinePhysicalLocalSum
                H G N₀ M D b c₂ x‖ ^ (6 : ℕ))) ≤
          ENNReal.ofReal
              |((bourgainA6NormalizedTaylorCoordinateMatrix
                G N₀ M).det)⁻¹| *
            ENNReal.ofReal
              |((((H : ℝ) / D) ^ (6 : ℕ)) *
                (bourgainGenericPhaseCoordinateMatrix
                  (bourgainNormalizedCubicRemainder (M / N₀))
                  (bourgainNormalizedQuarticRemainder (M / N₀))
                  a b).det)⁻¹| *
            ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hcell⟩ :=
    setLIntegral_bourgainA6AffinePhysicalLocalSum_fundamentalCell_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro H hH G N₀ M D a b hG hN₀ hM hq1 hD hHD
    ha0 ha1 hb0 hb1 hab hsmall c₁ c₂ y
  let c₁' :=
    bourgainA6AffinePhysicalLocalTranslateCoefficients
      H G N₀ M D a c₁ y
  let c₂' :=
    bourgainA6AffinePhysicalLocalTranslateCoefficients
      H G N₀ M D b c₂ y
  have hbound :=
    hcell H hH hG hN₀ hM hq1 hD hHD
      ha0 ha1 hb0 hb1 hab hsmall c₁' c₂'
  rw [setLIntegral_bourgainA6TranslatedAffinePhysicalFundamentalCell]
  calc
    (∫⁻ x in bourgainA6AffinePhysicalFundamentalCell
        H G N₀ M D a b,
      ENNReal.ofReal
        (‖bourgainA6AffinePhysicalLocalSum
            H G N₀ M D a c₁ (x + y)‖ ^ (6 : ℕ) *
          ‖bourgainA6AffinePhysicalLocalSum
            H G N₀ M D b c₂ (x + y)‖ ^ (6 : ℕ))) =
      ∫⁻ x in bourgainA6AffinePhysicalFundamentalCell
        H G N₀ M D a b,
      ENNReal.ofReal
        (‖bourgainA6AffinePhysicalLocalSum
            H G N₀ M D a c₁' x‖ ^ (6 : ℕ) *
          ‖bourgainA6AffinePhysicalLocalSum
            H G N₀ M D b c₂' x‖ ^ (6 : ℕ)) := by
        apply lintegral_congr
        intro x
        rw [bourgainA6AffinePhysicalLocalSum_add,
          bourgainA6AffinePhysicalLocalSum_add]
    _ ≤ _ := by
      simpa [c₁', c₂',
        sum_norm_sq_bourgainA6AffinePhysicalLocalTranslateCoefficients]
        using hbound

/-- Finite-cover summation for translated affine physical cells. -/
theorem
    setLIntegral_le_card_mul_of_bourgainA6AffinePhysicalFundamentalCell_cover
    {ι : Type*} [Fintype ι]
    (A : Set BourgainPhaseSpace)
    (H : ℕ) (G N₀ M D a b : ℝ)
    (center : ι → BourgainPhaseSpace)
    (f : BourgainPhaseSpace → ENNReal)
    (hcover :
      A ⊆ ⋃ i,
        bourgainA6TranslatedAffinePhysicalFundamentalCell
          H G N₀ M D a b (center i))
    {B : ENNReal}
    (hlocal :
      ∀ i,
        (∫⁻ x in bourgainA6TranslatedAffinePhysicalFundamentalCell
          H G N₀ M D a b (center i), f x) ≤ B) :
    (∫⁻ x in A, f x) ≤ (Fintype.card ι : ENNReal) * B := by
  exact setLIntegral_le_card_mul_of_finite_cover
    A
    (fun i =>
      bourgainA6TranslatedAffinePhysicalFundamentalCell
        H G N₀ M D a b (center i))
    f hcover hlocal

end

end RHTower
