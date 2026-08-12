/-
# One sharp Bourgain Section-1 recurrence step

This module packages exact full-arc and coarse-block moments, identifies the
independently translated aggregate with the block-pair family, and combines
the local decoupling coefficient with the sharp planar refinement.  It is
the formal counterpart of equations (1.18)--(1.26).
-/
import GaloisForLFunctions.RHTower.BourgainSectionOneRecurrenceAveraging

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

@[fun_prop] theorem continuous_bourgainGenericFourCurveExactLocalSum
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) (D a : ℝ)
    (c : Fin H → ℂ) :
    Continuous fun x : BourgainPhaseSpace =>
      bourgainGenericFourCurveExactLocalSum H φ₃ φ₄ D a c x := by
  unfold bourgainGenericFourCurveExactLocalSum bourgainUnitCharacter
    bourgainDot
  fun_prop

/-- Sixth-power mass of all left coarse blocks at one physical point. -/
def bourgainSectionOneLeftBlockSixthAggregate
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ)
    (x : BourgainPhaseSpace) : ENNReal :=
  ∑ i : Fin J,
    ENNReal.ofReal
      (‖bourgainGenericFourCurveExactLocalSum H
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        (bourgainSectionOneBlockDenominator J H)
        (bourgainSectionOneLeftBlockBase J i)
        (bourgainGenericCurveBlockCoefficients J H c i) x‖ ^ (6 : ℕ))

/-- Sixth-power mass of all right coarse blocks at one physical point. -/
def bourgainSectionOneRightBlockSixthAggregate
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ)
    (x : BourgainPhaseSpace) : ENNReal :=
  ∑ j : Fin J,
    ENNReal.ofReal
      (‖bourgainGenericFourCurveExactLocalSum H
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        (bourgainSectionOneBlockDenominator J H)
        (bourgainSectionOneRightBlockBase J j)
        (bourgainGenericCurveBlockCoefficients J H c j) x‖ ^ (6 : ℕ))

theorem measurable_bourgainSectionOneLeftBlockSixthAggregate
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ) :
    Measurable (bourgainSectionOneLeftBlockSixthAggregate J H q c) := by
  unfold bourgainSectionOneLeftBlockSixthAggregate
  fun_prop

theorem measurable_bourgainSectionOneRightBlockSixthAggregate
    (J H : ℕ) (q : ℝ) (c : Fin (J * H) → ℂ) :
    Measurable (bourgainSectionOneRightBlockSixthAggregate J H q c) := by
  unfold bourgainSectionOneRightBlockSixthAggregate
  fun_prop

/-- Exact full separated-arc bilinear twelfth-power integrand. -/
def bourgainSectionOneFullBilinearIntegrand
    (J H : ℕ) (q : ℝ) (c₁ c₂ : Fin (J * H) → ℂ)
    (x : BourgainPhaseSpace) : ENNReal :=
  ENNReal.ofReal
    (‖bourgainGenericFourCurveExactLocalSum (J * H)
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        (bourgainSectionOneBlockDenominator J H) 0 c₁ x‖ ^ (6 : ℕ) *
      ‖bourgainGenericFourCurveExactLocalSum (J * H)
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        (bourgainSectionOneBlockDenominator J H) (1 / 2) c₂ x‖ ^ (6 : ℕ))

theorem measurable_bourgainSectionOneFullBilinearIntegrand
    (J H : ℕ) (q : ℝ) (c₁ c₂ : Fin (J * H) → ℂ) :
    Measurable (bourgainSectionOneFullBilinearIntegrand J H q c₁ c₂) := by
  unfold bourgainSectionOneFullBilinearIntegrand
  fun_prop

/-- The product of independently translated block aggregates integrates to
the exact family moment from equation (1.20). -/
theorem
    setLIntegral_bourgainSectionOne_blockSixthAggregates_independent_eq
    (J H : ℕ) (q : ℝ) (c₁ c₂ : Fin (J * H) → ℂ)
    (y₁ y₂ : BourgainPhaseSpace) :
    (∫⁻ x in bourgainSectionOnePhaseBall
        (bourgainSectionOneBlockDenominator J H),
      bourgainSectionOneLeftBlockSixthAggregate J H q c₁ (x + y₁) *
        bourgainSectionOneRightBlockSixthAggregate J H q c₂ (x + y₂)) =
      bourgainSectionOneIndependentlyTranslatedBlockPairFamilyMoment
        J H q c₁ c₂ y₁ y₂ := by
  unfold bourgainSectionOneLeftBlockSixthAggregate
    bourgainSectionOneRightBlockSixthAggregate
    bourgainSectionOneIndependentlyTranslatedBlockPairFamilyMoment
  dsimp only
  have hset :
      MeasurableSet
        (bourgainSectionOnePhaseBall
          (bourgainSectionOneBlockDenominator J H)) := by
    have heq :
        bourgainSectionOnePhaseBall
            (bourgainSectionOneBlockDenominator J H) =
          Metric.closedBall 0
            (bourgainSectionOneBlockDenominator J H ^ (2 : ℕ)) := by
      ext x
      simp [bourgainSectionOnePhaseBall, Metric.mem_closedBall,
        dist_zero_right]
    exact heq ▸ measurableSet_closedBall
  calc
    (∫⁻ x in bourgainSectionOnePhaseBall
        (bourgainSectionOneBlockDenominator J H),
      (∑ i : Fin J,
        ENNReal.ofReal
          (‖bourgainGenericFourCurveExactLocalSum H
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q)
            (bourgainSectionOneBlockDenominator J H)
            (bourgainSectionOneLeftBlockBase J i)
            (bourgainGenericCurveBlockCoefficients J H c₁ i) (x + y₁)‖ ^
              (6 : ℕ))) *
        ∑ j : Fin J,
          ENNReal.ofReal
            (‖bourgainGenericFourCurveExactLocalSum H
              (bourgainNormalizedCubicRemainder q)
              (bourgainNormalizedQuarticRemainder q)
              (bourgainSectionOneBlockDenominator J H)
              (bourgainSectionOneRightBlockBase J j)
              (bourgainGenericCurveBlockCoefficients J H c₂ j) (x + y₂)‖ ^
                (6 : ℕ))) =
      ∫⁻ x in bourgainSectionOnePhaseBall
          (bourgainSectionOneBlockDenominator J H),
        ∑ i : Fin J, ∑ j : Fin J,
          ENNReal.ofReal
            (‖bourgainGenericFourCurveExactLocalSum H
              (bourgainNormalizedCubicRemainder q)
              (bourgainNormalizedQuarticRemainder q)
              (bourgainSectionOneBlockDenominator J H)
              (bourgainSectionOneLeftBlockBase J i)
              (bourgainGenericCurveBlockCoefficients J H c₁ i) (x + y₁)‖ ^
                (6 : ℕ) *
            ‖bourgainGenericFourCurveExactLocalSum H
              (bourgainNormalizedCubicRemainder q)
              (bourgainNormalizedQuarticRemainder q)
              (bourgainSectionOneBlockDenominator J H)
              (bourgainSectionOneRightBlockBase J j)
              (bourgainGenericCurveBlockCoefficients J H c₂ j) (x + y₂)‖ ^
                (6 : ℕ)) := by
      apply setLIntegral_congr_fun hset
      intro x hx
      dsimp only
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ∑ i : Fin J, ∑ j : Fin J,
        ∫⁻ x in bourgainSectionOnePhaseBall
            (bourgainSectionOneBlockDenominator J H),
          ENNReal.ofReal
            (‖bourgainGenericFourCurveExactLocalSum H
              (bourgainNormalizedCubicRemainder q)
              (bourgainNormalizedQuarticRemainder q)
              (bourgainSectionOneBlockDenominator J H)
              (bourgainSectionOneLeftBlockBase J i)
              (bourgainGenericCurveBlockCoefficients J H c₁ i) (x + y₁)‖ ^
                (6 : ℕ) *
            ‖bourgainGenericFourCurveExactLocalSum H
              (bourgainNormalizedCubicRemainder q)
              (bourgainNormalizedQuarticRemainder q)
              (bourgainSectionOneBlockDenominator J H)
              (bourgainSectionOneRightBlockBase J j)
              (bourgainGenericCurveBlockCoefficients J H c₂ j) (x + y₂)‖ ^
                (6 : ℕ)) := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [lintegral_finsetSum]
        intro j hj
        fun_prop
      · intro i hi
        fun_prop

/-- Local coefficient form of Bourgain's decoupling inequality at the
coarse physical scale `K = (4J)²`.  Multiplication by cube volume avoids
division in `ENNReal`; the factor `R²` is `K^(d/2)` for `d=4`. -/
def BourgainSectionOneLocalDecouplingAt
    (J : ℕ) (b : ℝ) : Prop :=
  ∀ (H : ℕ), 0 < H →
    6 * bourgainSectionOneTaylorConstant * (H : ℝ) ^ (2 : ℕ) ≤ J →
    ∀ {q : ℝ}, 0 < q → q ≤ 1 / 2 →
    ∀ (c₁ c₂ : Fin (J * H) → ℂ) (y : BourgainPhaseSpace),
      let R := bourgainSectionOneCoarsePhysicalRadius J
      let V := ENNReal.ofReal ((2 * R) ^ (4 : ℕ))
      V *
          ∫⁻ x in bourgainTranslatedNormCube y R,
            bourgainSectionOneFullBilinearIntegrand J H q c₁ c₂ x ≤
        ENNReal.ofReal (b ^ (12 : ℕ) * R ^ (2 : ℕ)) *
          (∫⁻ x in bourgainTranslatedNormCube y R,
            bourgainSectionOneLeftBlockSixthAggregate J H q c₁ x) *
          (∫⁻ x in bourgainTranslatedNormCube y R,
            bourgainSectionOneRightBlockSixthAggregate J H q c₂ x)

/-- Independently averaged block aggregates inherit the sharp planar
refinement bound.  The two translation cubes contribute only their exact
volumes; there is no recurrence-grid entropy. -/
theorem
    setLIntegral_bourgainSectionOne_translateAverage_blockAggregates_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J H : ℕ) (_hJ : 0 < J) (_hH : 0 < H)
        (_hscale :
          6 * bourgainSectionOneTaylorConstant *
              (H : ℝ) ^ (2 : ℕ) ≤ J)
        {q : ℝ} (_hq : 0 < q) (_hq1 : q ≤ 1 / 2)
        (c₁ c₂ : Fin (J * H) → ℂ),
        let R := bourgainSectionOneCoarsePhysicalRadius J
        let W := ENNReal.ofReal ((4 * R) ^ (4 : ℕ))
        (∫⁻ x in bourgainSectionOnePhaseBall
            (bourgainSectionOneBlockDenominator J H),
          bourgainTranslateAverage (2 * R)
              (bourgainSectionOneLeftBlockSixthAggregate J H q c₁) x *
            bourgainTranslateAverage (2 * R)
              (bourgainSectionOneRightBlockSixthAggregate J H q c₂) x) ≤
          W ^ (2 : ℕ) *
            (ENNReal.ofReal
                ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
                  bourgainSectionOneBlockDenominator J H ^ (8 : ℕ)) *
              ENNReal.ofReal
                (C * (H : ℝ) ^ ε * (H : ℝ) ^ (4 : ℕ) *
                  (∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
                  (∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ)))) := by
  obtain ⟨C, hC, hfamily⟩ :=
    bourgainSectionOneIndependentlyTranslatedBlockPairFamilyMoment_refinement_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro J H hJ hH hscale q hq hq1 c₁ c₂
  dsimp only
  let R := bourgainSectionOneCoarsePhysicalRadius J
  let B : Set BourgainPhaseSpace := bourgainCenteredNormCube (2 * R)
  let W : ENNReal := ENNReal.ofReal ((4 * R) ^ (4 : ℕ))
  let M : ENNReal :=
    ENNReal.ofReal
        ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
          bourgainSectionOneBlockDenominator J H ^ (8 : ℕ)) *
      ENNReal.ofReal
        (C * (H : ℝ) ^ ε * (H : ℝ) ^ (4 : ℕ) *
          (∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
          (∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ)))
  have hR : 0 < R := by
    dsimp [R]
    unfold bourgainSectionOneCoarsePhysicalRadius
    positivity
  have hA :
      MeasurableSet
        (bourgainSectionOnePhaseBall
          (bourgainSectionOneBlockDenominator J H)) := by
    have heq :
        bourgainSectionOnePhaseBall
            (bourgainSectionOneBlockDenominator J H) =
          Metric.closedBall 0
            (bourgainSectionOneBlockDenominator J H ^ (2 : ℕ)) := by
      ext x
      simp [bourgainSectionOnePhaseBall, Metric.mem_closedBall,
        dist_zero_right]
    exact heq ▸ measurableSet_closedBall
  have htonelli :=
    setLIntegral_translateAverage_mul_eq_independent_translates hA
      (measurable_bourgainSectionOneLeftBlockSixthAggregate J H q c₁)
      (measurable_bourgainSectionOneRightBlockSixthAggregate J H q c₂)
      (R := 2 * R)
  have hpoint (y₁ y₂ : BourgainPhaseSpace) :
      (∫⁻ x in bourgainSectionOnePhaseBall
          (bourgainSectionOneBlockDenominator J H),
        bourgainSectionOneLeftBlockSixthAggregate J H q c₁ (x + y₁) *
          bourgainSectionOneRightBlockSixthAggregate J H q c₂ (x + y₂)) ≤
        M := by
    rw [setLIntegral_bourgainSectionOne_blockSixthAggregates_independent_eq]
    simpa [M] using
      hfamily J H hJ hH hscale hq hq1 c₁ c₂ y₁ y₂
  have hvolume : volume B = W := by
    dsimp [B, W]
    simpa [bourgainCenteredNormCube, show 2 * (2 * R) = 4 * R by ring]
      using volume_fin_four_normCube (show 0 ≤ 2 * R by positivity)
  calc
    (∫⁻ x in bourgainSectionOnePhaseBall
        (bourgainSectionOneBlockDenominator J H),
      bourgainTranslateAverage (2 * R)
          (bourgainSectionOneLeftBlockSixthAggregate J H q c₁) x *
        bourgainTranslateAverage (2 * R)
          (bourgainSectionOneRightBlockSixthAggregate J H q c₂) x) =
        ∫⁻ y₁ in B, ∫⁻ y₂ in B,
          ∫⁻ x in bourgainSectionOnePhaseBall
              (bourgainSectionOneBlockDenominator J H),
            bourgainSectionOneLeftBlockSixthAggregate J H q c₁ (x + y₁) *
              bourgainSectionOneRightBlockSixthAggregate J H q c₂ (x + y₂) := by
      simpa [B] using htonelli
    _ ≤ ∫⁻ _y₁ in B, ∫⁻ _y₂ in B, M := by
      apply setLIntegral_mono measurable_const
      intro y₁ hy₁
      apply setLIntegral_mono measurable_const
      intro y₂ hy₂
      exact hpoint y₁ y₂
    _ = W ^ (2 : ℕ) * M := by
      rw [setLIntegral_const, setLIntegral_const, hvolume]
      ring
    _ = _ := by rfl

/-- **Bourgain (1.19)--(1.26), exact one-step form before canceling local
cube volume.**  A local decoupling coefficient at scale `(4J)²` controls
the full separated-arc moment at scale `(4JH)²`.  Every geometric and
averaging factor is explicit. -/
theorem bourgainSectionOne_recurrenceStep_volumeForm_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J H : ℕ) (hJ : 0 < J) (hH : 0 < H)
        (hscale :
          6 * bourgainSectionOneTaylorConstant *
              (H : ℝ) ^ (2 : ℕ) ≤ J)
        {q b : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
        (hlocal : BourgainSectionOneLocalDecouplingAt J b)
        (c₁ c₂ : Fin (J * H) → ℂ),
        let R := bourgainSectionOneCoarsePhysicalRadius J
        let V := ENNReal.ofReal ((2 * R) ^ (4 : ℕ))
        let W := ENNReal.ofReal ((4 * R) ^ (4 : ℕ))
        V ^ (2 : ℕ) *
            (∫⁻ x in bourgainSectionOnePhaseBall
                (bourgainSectionOneBlockDenominator J H),
              bourgainSectionOneFullBilinearIntegrand J H q c₁ c₂ x) ≤
          ENNReal.ofReal (b ^ (12 : ℕ) * R ^ (2 : ℕ)) *
            W ^ (2 : ℕ) *
            (ENNReal.ofReal
                ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
                  bourgainSectionOneBlockDenominator J H ^ (8 : ℕ)) *
              ENNReal.ofReal
                (C * (H : ℝ) ^ ε * (H : ℝ) ^ (4 : ℕ) *
                  (∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
                  (∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ)))) := by
  obtain ⟨C, hC, havg⟩ :=
    setLIntegral_bourgainSectionOne_translateAverage_blockAggregates_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro J H hJ hH hscale q b hq hq1 hlocal c₁ c₂
  dsimp only
  let R := bourgainSectionOneCoarsePhysicalRadius J
  let V := ENNReal.ofReal ((2 * R) ^ (4 : ℕ))
  let W := ENNReal.ofReal ((4 * R) ^ (4 : ℕ))
  let A := ENNReal.ofReal (b ^ (12 : ℕ) * R ^ (2 : ℕ))
  let F := bourgainSectionOneLeftBlockSixthAggregate J H q c₁
  let G := bourgainSectionOneRightBlockSixthAggregate J H q c₂
  let Q := bourgainSectionOneFullBilinearIntegrand J H q c₁ c₂
  let M : ENNReal :=
    ENNReal.ofReal
        ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
          bourgainSectionOneBlockDenominator J H ^ (8 : ℕ)) *
      ENNReal.ofReal
        (C * (H : ℝ) ^ ε * (H : ℝ) ^ (4 : ℕ) *
          (∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
          (∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ)))
  have hloc (k : Fin 4 → Fin (H ^ (2 : ℕ))) :
      V *
          (∫⁻ x in bourgainTranslatedNormCube
              (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, Q x) ≤
        A *
          (∫⁻ x in bourgainTranslatedNormCube
              (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, F x) *
          (∫⁻ x in bourgainTranslatedNormCube
              (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, G x) := by
    simpa [R, V, A, F, G, Q] using
      hlocal H hH hscale hq hq1 c₁ c₂
        (bourgainGridCenter (H ^ (2 : ℕ)) R k)
  have hsumlocal :
      ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
          V *
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, Q x) ≤
        A *
          ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, F x) *
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, G x) := by
    calc
      ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
          V *
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, Q x) ≤
        ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
          A *
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, F x) *
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, G x) :=
          Finset.sum_le_sum fun k hk => hloc k
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have haverage :
      V *
          ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, F x) *
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, G x) ≤
        ∫⁻ x in bourgainSectionOnePhaseBall
            (bourgainSectionOneBlockDenominator J H),
          bourgainTranslateAverage (2 * R) F x *
            bourgainTranslateAverage (2 * R) G x := by
    simpa [R, V, F, G] using
      volume_mul_sum_coarseGrid_localMassProduct_le_translateAverage
        J H hJ hH
        (measurable_bourgainSectionOneLeftBlockSixthAggregate J H q c₁)
        (measurable_bourgainSectionOneRightBlockSixthAggregate J H q c₂)
  have havg' :
      (∫⁻ x in bourgainSectionOnePhaseBall
          (bourgainSectionOneBlockDenominator J H),
        bourgainTranslateAverage (2 * R) F x *
          bourgainTranslateAverage (2 * R) G x) ≤
        W ^ (2 : ℕ) * M := by
    simpa [R, W, F, G, M] using
      havg J H hJ hH hscale hq hq1 c₁ c₂
  have hpartition :=
    sum_setLIntegral_bourgainSectionOne_coarseGrid_eq_finePhaseBall
      J H hJ hH Q
  calc
    V ^ (2 : ℕ) *
        (∫⁻ x in bourgainSectionOnePhaseBall
            (bourgainSectionOneBlockDenominator J H), Q x) =
      V *
        ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
          V *
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, Q x) := by
      rw [← hpartition, Finset.mul_sum]
      ring
    _ ≤ V *
        (A *
          ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, F x) *
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, G x)) :=
      mul_le_mul_right hsumlocal V
    _ = A *
        (V *
          ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, F x) *
            (∫⁻ x in bourgainTranslatedNormCube
                (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, G x)) := by ring
    _ ≤ A *
        (∫⁻ x in bourgainSectionOnePhaseBall
            (bourgainSectionOneBlockDenominator J H),
          bourgainTranslateAverage (2 * R) F x *
            bourgainTranslateAverage (2 * R) G x) :=
      mul_le_mul_right haverage A
    _ ≤ A * (W ^ (2 : ℕ) * M) :=
      mul_le_mul_right havg' A
    _ = _ := by rfl

/-- **Volume-canceled sharp recurrence.**  The radius-doubling averaging
box has volume exactly `16` times one coarse cube, so after cancellation
the entire physical localization costs only the absolute factor `256`.
No power of `H` or `J` is lost. -/
theorem bourgainSectionOne_recurrenceStep_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J H : ℕ) (hJ : 0 < J) (hH : 0 < H)
        (hscale :
          6 * bourgainSectionOneTaylorConstant *
              (H : ℝ) ^ (2 : ℕ) ≤ J)
        {q b : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
        (hlocal : BourgainSectionOneLocalDecouplingAt J b)
        (c₁ c₂ : Fin (J * H) → ℂ),
        (∫⁻ x in bourgainSectionOnePhaseBall
            (bourgainSectionOneBlockDenominator J H),
          bourgainSectionOneFullBilinearIntegrand J H q c₁ c₂ x) ≤
          (256 : ENNReal) *
            ENNReal.ofReal
              (b ^ (12 : ℕ) *
                bourgainSectionOneCoarsePhysicalRadius J ^ (2 : ℕ)) *
            (ENNReal.ofReal
                ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
                  bourgainSectionOneBlockDenominator J H ^ (8 : ℕ)) *
              ENNReal.ofReal
                (C * (H : ℝ) ^ ε * (H : ℝ) ^ (4 : ℕ) *
                  (∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
                  (∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ)))) := by
  obtain ⟨C, hC, hraw⟩ :=
    bourgainSectionOne_recurrenceStep_volumeForm_subpower hε
  refine ⟨C, hC, ?_⟩
  intro J H hJ hH hscale q b hq hq1 hlocal c₁ c₂
  let R := bourgainSectionOneCoarsePhysicalRadius J
  let V := ENNReal.ofReal ((2 * R) ^ (4 : ℕ))
  let W := ENNReal.ofReal ((4 * R) ^ (4 : ℕ))
  let A := ENNReal.ofReal (b ^ (12 : ℕ) * R ^ (2 : ℕ))
  let I := ∫⁻ x in bourgainSectionOnePhaseBall
      (bourgainSectionOneBlockDenominator J H),
    bourgainSectionOneFullBilinearIntegrand J H q c₁ c₂ x
  let M : ENNReal :=
    ENNReal.ofReal
        ((26001 ^ (2 : ℕ) * (131072 / 3 : ℝ)) *
          bourgainSectionOneBlockDenominator J H ^ (8 : ℕ)) *
      ENNReal.ofReal
        (C * (H : ℝ) ^ ε * (H : ℝ) ^ (4 : ℕ) *
          (∑ n : Fin (J * H), ‖c₁ n‖ ^ (6 : ℕ)) *
          (∑ n : Fin (J * H), ‖c₂ n‖ ^ (6 : ℕ)))
  have hR : 0 < R := by
    dsimp [R]
    unfold bourgainSectionOneCoarsePhysicalRadius
    positivity
  have hV0 : V ≠ 0 := by
    dsimp [V]
    rw [ENNReal.ofReal_ne_zero]
    positivity
  have hVtop : V ≠ ∞ := by
    dsimp [V]
    exact ENNReal.ofReal_ne_top
  have hV20 : V ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hV0
  have hV2top : V ^ (2 : ℕ) ≠ ∞ := by
    finiteness
  have hWV : W = 16 * V := by
    dsimp [W, V]
    rw [show (4 * R) ^ (4 : ℕ) = 16 * (2 * R) ^ (4 : ℕ) by ring]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have hstep : V ^ (2 : ℕ) * I ≤
      A * W ^ (2 : ℕ) * M := by
    simpa [R, V, W, A, I, M] using
      hraw J H hJ hH hscale hq hq1 hlocal c₁ c₂
  have hcanceled : I ≤ (256 : ENNReal) * A * M := by
    apply (ENNReal.mul_le_mul_iff_right hV20 hV2top).mp
    calc
      V ^ (2 : ℕ) * I ≤ A * W ^ (2 : ℕ) * M := hstep
      _ = V ^ (2 : ℕ) * ((256 : ENNReal) * A * M) := by
        rw [hWV]
        ring
  simpa [R, A, I, M] using hcanceled

end

end RHTower
