/-
# Independent translations in Bourgain's Section-1 refinement

Bourgain's equation (1.20) translates the two separated arcs independently.
This module proves that each translation is an exact unit-character twist of
the corresponding full coefficient vector, that restriction to a coarse
block commutes with the twist, and that all sixth coefficient masses are
unchanged.  Thus the global block-pair estimate applies uniformly to the two
independent physical translations used by the recurrence.
-/
import GaloisForLFunctions.RHTower.BourgainSectionOneGlobalBilinear

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Full left-arc coefficient twist induced by a physical translation. -/
def bourgainSectionOneLeftTranslateCoefficients
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ)
    (y : BourgainPhaseSpace) : Fin (J * H) → ℂ :=
  bourgainGenericExactLocalTranslateCoefficients
    (J * H) (bourgainNormalizedCubicRemainder q)
    (bourgainNormalizedQuarticRemainder q)
    (bourgainSectionOneBlockDenominator J H) 0 c y

/-- Full right-arc coefficient twist induced by a physical translation. -/
def bourgainSectionOneRightTranslateCoefficients
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ)
    (y : BourgainPhaseSpace) : Fin (J * H) → ℂ :=
  bourgainGenericExactLocalTranslateCoefficients
    (J * H) (bourgainNormalizedCubicRemainder q)
    (bourgainNormalizedQuarticRemainder q)
    (bourgainSectionOneBlockDenominator J H) (1 / 2) c y

@[simp] theorem norm_bourgainSectionOneLeftTranslateCoefficients
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ)
    (y : BourgainPhaseSpace) (n : Fin (J * H)) :
    ‖bourgainSectionOneLeftTranslateCoefficients J H q c y n‖ =
      ‖c n‖ := by
  exact norm_bourgainGenericExactLocalTranslateCoefficients
    (J * H) (bourgainNormalizedCubicRemainder q)
    (bourgainNormalizedQuarticRemainder q)
    (bourgainSectionOneBlockDenominator J H) 0 c y n

@[simp] theorem norm_bourgainSectionOneRightTranslateCoefficients
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ)
    (y : BourgainPhaseSpace) (n : Fin (J * H)) :
    ‖bourgainSectionOneRightTranslateCoefficients J H q c y n‖ =
      ‖c n‖ := by
  exact norm_bourgainGenericExactLocalTranslateCoefficients
    (J * H) (bourgainNormalizedCubicRemainder q)
    (bourgainNormalizedQuarticRemainder q)
    (bourgainSectionOneBlockDenominator J H) (1 / 2) c y n

/-- Restriction of the full left twist equals the local twist at the exact
left block base. -/
theorem bourgainSectionOne_left_blockCoefficients_translate
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ)
    (y : BourgainPhaseSpace) (i : Fin J) :
    bourgainGenericCurveBlockCoefficients J H
        (bourgainSectionOneLeftTranslateCoefficients J H q c y) i =
      bourgainGenericExactLocalTranslateCoefficients H
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        (bourgainSectionOneBlockDenominator J H)
        (bourgainSectionOneLeftBlockBase J i)
        (bourgainGenericCurveBlockCoefficients J H c i) y := by
  funext n
  have hJ : (J : ℝ) ≠ 0 := by
    exact_mod_cast (Fin.pos_iff_nonempty.mpr ⟨i⟩).ne'
  have hH : (H : ℝ) ≠ 0 := by
    exact_mod_cast (Fin.pos_iff_nonempty.mpr ⟨n⟩).ne'
  have hparameter :
      (bourgainIndex (finProdFinEquiv (i, n)) : ℝ) /
          bourgainSectionOneBlockDenominator J H =
        bourgainSectionOneLeftBlockBase J i +
          (bourgainIndex n : ℝ) /
            bourgainSectionOneBlockDenominator J H := by
    unfold bourgainSectionOneLeftBlockBase bourgainIndex
      bourgainSectionOneBlockDenominator
    rw [finProdFinEquiv_apply_val]
    push_cast
    field_simp
    ring
  unfold bourgainGenericCurveBlockCoefficients
    bourgainSectionOneLeftTranslateCoefficients
    bourgainGenericExactLocalTranslateCoefficients
  rw [hparameter]
  simp

/-- Restriction of the full right twist equals the local twist at the exact
right block base. -/
theorem bourgainSectionOne_right_blockCoefficients_translate
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ)
    (y : BourgainPhaseSpace) (j : Fin J) :
    bourgainGenericCurveBlockCoefficients J H
        (bourgainSectionOneRightTranslateCoefficients J H q c y) j =
      bourgainGenericExactLocalTranslateCoefficients H
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        (bourgainSectionOneBlockDenominator J H)
        (bourgainSectionOneRightBlockBase J j)
        (bourgainGenericCurveBlockCoefficients J H c j) y := by
  funext n
  have hJ : (J : ℝ) ≠ 0 := by
    exact_mod_cast (Fin.pos_iff_nonempty.mpr ⟨j⟩).ne'
  have hH : (H : ℝ) ≠ 0 := by
    exact_mod_cast (Fin.pos_iff_nonempty.mpr ⟨n⟩).ne'
  have hparameter :
      (1 / 2 : ℝ) +
          (bourgainIndex (finProdFinEquiv (j, n)) : ℝ) /
            bourgainSectionOneBlockDenominator J H =
        bourgainSectionOneRightBlockBase J j +
          (bourgainIndex n : ℝ) /
            bourgainSectionOneBlockDenominator J H := by
    unfold bourgainSectionOneRightBlockBase bourgainIndex
      bourgainSectionOneBlockDenominator
    rw [finProdFinEquiv_apply_val]
    push_cast
    field_simp
    ring
  unfold bourgainGenericCurveBlockCoefficients
    bourgainSectionOneRightTranslateCoefficients
    bourgainGenericExactLocalTranslateCoefficients
  rw [hparameter]

/-- Exact left-block translation identity using one twist of the full vector. -/
theorem bourgainSectionOne_left_block_sum_add
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ)
    (x y : BourgainPhaseSpace) (i : Fin J) :
    bourgainGenericFourCurveExactLocalSum H
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        (bourgainSectionOneBlockDenominator J H)
        (bourgainSectionOneLeftBlockBase J i)
        (bourgainGenericCurveBlockCoefficients J H c i) (x + y) =
      bourgainGenericFourCurveExactLocalSum H
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        (bourgainSectionOneBlockDenominator J H)
        (bourgainSectionOneLeftBlockBase J i)
        (bourgainGenericCurveBlockCoefficients J H
          (bourgainSectionOneLeftTranslateCoefficients J H q c y) i) x := by
  rw [bourgainGenericFourCurveExactLocalSum_add,
    bourgainSectionOne_left_blockCoefficients_translate]

/-- Exact right-block translation identity using an independent twist of the
second full vector. -/
theorem bourgainSectionOne_right_block_sum_add
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ)
    (x y : BourgainPhaseSpace) (j : Fin J) :
    bourgainGenericFourCurveExactLocalSum H
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        (bourgainSectionOneBlockDenominator J H)
        (bourgainSectionOneRightBlockBase J j)
        (bourgainGenericCurveBlockCoefficients J H c j) (x + y) =
      bourgainGenericFourCurveExactLocalSum H
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        (bourgainSectionOneBlockDenominator J H)
        (bourgainSectionOneRightBlockBase J j)
        (bourgainGenericCurveBlockCoefficients J H
          (bourgainSectionOneRightTranslateCoefficients J H q c y) j) x := by
  rw [bourgainGenericFourCurveExactLocalSum_add,
    bourgainSectionOne_right_blockCoefficients_translate]

/-- Independent twists preserve the two global sixth coefficient masses. -/
theorem sum_norm_pow_six_bourgainSectionOne_independentTranslateCoefficients
    (J H : ℕ) (q : ℝ) (c₁ c₂ : Fin (J * H) → ℂ)
    (y₁ y₂ : BourgainPhaseSpace) :
    (∑ n : Fin (J * H),
        ‖bourgainSectionOneLeftTranslateCoefficients J H q c₁ y₁ n‖ ^
          (6 : ℕ)) *
      (∑ n : Fin (J * H),
        ‖bourgainSectionOneRightTranslateCoefficients J H q c₂ y₂ n‖ ^
          (6 : ℕ)) =
      (∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
        (∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ)) := by
  simp

/-- Sum of block-pair moments after translating the two arcs independently,
as in Bourgain's equation (1.20). -/
def bourgainSectionOneIndependentlyTranslatedBlockPairFamilyMoment
    (J H : ℕ) (q : ℝ) (c₁ c₂ : Fin (J * H) → ℂ)
    (y₁ y₂ : BourgainPhaseSpace) : ENNReal :=
  let D := bourgainSectionOneBlockDenominator J H
  let φ₃ := bourgainNormalizedCubicRemainder q
  let φ₄ := bourgainNormalizedQuarticRemainder q
  ∑ i : Fin J, ∑ j : Fin J,
    ∫⁻ x in bourgainSectionOnePhaseBall D,
      ENNReal.ofReal
        (‖bourgainGenericFourCurveExactLocalSum H φ₃ φ₄ D
            (bourgainSectionOneLeftBlockBase J i)
            (bourgainGenericCurveBlockCoefficients J H c₁ i) (x + y₁)‖ ^
              (6 : ℕ) *
          ‖bourgainGenericFourCurveExactLocalSum H φ₃ φ₄ D
            (bourgainSectionOneRightBlockBase J j)
            (bourgainGenericCurveBlockCoefficients J H c₂ j) (x + y₂)‖ ^
              (6 : ℕ))

/-- Independent physical translations are exactly independent twists of the
two full coefficient vectors. -/
theorem bourgainSectionOneIndependentlyTranslatedBlockPairFamilyMoment_eq
    (J H : ℕ) (q : ℝ) (c₁ c₂ : Fin (J * H) → ℂ)
    (y₁ y₂ : BourgainPhaseSpace) :
    bourgainSectionOneIndependentlyTranslatedBlockPairFamilyMoment
        J H q c₁ c₂ y₁ y₂ =
      bourgainSectionOneBlockPairFamilyMoment J H q
        (bourgainSectionOneLeftTranslateCoefficients J H q c₁ y₁)
        (bourgainSectionOneRightTranslateCoefficients J H q c₂ y₂) := by
  unfold bourgainSectionOneIndependentlyTranslatedBlockPairFamilyMoment
    bourgainSectionOneBlockPairFamilyMoment
  dsimp only
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hset :
      bourgainSectionOnePhaseBall
          (bourgainSectionOneBlockDenominator J H) =
        Metric.closedBall 0
          (bourgainSectionOneBlockDenominator J H ^ (2 : ℕ)) := by
    ext x
    simp [bourgainSectionOnePhaseBall, Metric.mem_closedBall,
      dist_zero_right]
  apply MeasureTheory.setLIntegral_congr_fun
    (hset ▸ measurableSet_closedBall)
  intro x hx
  dsimp only
  rw [bourgainSectionOne_left_block_sum_add,
    bourgainSectionOne_right_block_sum_add]

/-- **Independent-translation form of Bourgain (1.25).**

The sharp `D⁸ H^(4+ε)` family bound is uniform in both translation
vectors.  No common-translation hypothesis remains. -/
theorem
    bourgainSectionOneIndependentlyTranslatedBlockPairFamilyMoment_refinement_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J H : ℕ) (_hJ : 0 < J) (_hH : 0 < H)
        (_hscale :
          6 * bourgainSectionOneTaylorConstant *
              (H : ℝ) ^ (2 : ℕ) ≤ J)
        {q : ℝ} (_hq : 0 < q) (_hq1 : q ≤ 1 / 2)
        (c₁ c₂ : Fin (J * H) → ℂ)
        (y₁ y₂ : BourgainPhaseSpace),
        bourgainSectionOneIndependentlyTranslatedBlockPairFamilyMoment
            J H q c₁ c₂ y₁ y₂ ≤
          ENNReal.ofReal
              ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
                bourgainSectionOneBlockDenominator J H ^ (8 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε * (H : ℝ) ^ (4 : ℕ) *
                (∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
                (∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ))) := by
  obtain ⟨C, hC, hfamily⟩ :=
    bourgainSectionOneBlockPairFamilyMoment_refinement_subpower hε
  refine ⟨C, hC, ?_⟩
  intro J H hJ hH hscale q hq hq1 c₁ c₂ y₁ y₂
  rw [bourgainSectionOneIndependentlyTranslatedBlockPairFamilyMoment_eq]
  simpa using
    hfamily J H hJ hH hscale hq hq1
      (bourgainSectionOneLeftTranslateCoefficients J H q c₁ y₁)
      (bourgainSectionOneRightTranslateCoefficients J H q c₂ y₂)

end

end RHTower
