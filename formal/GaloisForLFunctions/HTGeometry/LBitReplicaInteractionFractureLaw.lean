import GaloisForLFunctions.HTGeometry.LBitTemporalDimensionLaw
import GaloisForLFunctions.HTGeometry.ResolvedRecurrenceRelationCompletenessLaw

/-!
# Replica depth of localized interaction fracture

For a finite nonempty packet of localized binary modes, the alternating
character on the complete Boolean configuration cube is a balanced
integer spectral character. Its exact minimum replica height is
`2^(N-1)`, and its detuning against an l-bit Hamiltonian is exactly
`2^N` times the coefficient coupling all `N` modes.

Consequently, the complete-cube recurrence relation survives exactly when
the top-order l-bit interaction is absent, and its fracture is witnessed
at the exact replica height `2^(N-1)`.
-/

open Set Filter NormedSpace Topology MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance lbitReplicaFractureFintypeForallBool
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

/-- Integer sign carried by one l-bit configuration coordinate. -/
def lbitIntegerSign (b : Bool) : ℤ :=
  if b then -1 else 1

/-- Alternating integer character on the complete Boolean configuration
cube. -/
def lbitFullCubeCharacter
    {I : Type*} [Fintype I] (x : I → Bool) : ℤ :=
  ∏ i : I, lbitIntegerSign (x i)

theorem lbitIntegerSign_cast_rat (b : Bool) :
    ((lbitIntegerSign b : ℤ) : ℚ) = lbitSign b := by
  cases b <;> norm_num [lbitIntegerSign, lbitSign]

/-- The integer full-cube character is the full-support Walsh character. -/
theorem lbitFullCubeCharacter_cast_rat
    {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → Bool) :
    ((lbitFullCubeCharacter x : ℤ) : ℚ) =
      lbitWalshCharacter (Finset.univ : Finset I) x := by
  simp [lbitFullCubeCharacter, lbitWalshCharacter,
    lbitIntegerSign_cast_rat]

theorem lbitFullCubeCharacter_cast_real
    {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → Bool) :
    ((lbitFullCubeCharacter x : ℤ) : ℝ) =
      (lbitWalshCharacter (Finset.univ : Finset I) x : ℚ) := by
  exact_mod_cast lbitFullCubeCharacter_cast_rat x

/-- On every nonempty Boolean cube, the alternating character is
projective. -/
theorem lbitFullCubeCharacter_balanced
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] :
    SpectralCharacterBalanced
      (lbitFullCubeCharacter : (I → Bool) → ℤ) := by
  have huniv :
      (Finset.univ : Finset I).Nonempty :=
    Finset.univ_nonempty
  have h :=
    sum_lbitWalshCharacter_eq_zero
      (S := (Finset.univ : Finset I)) huniv
  unfold SpectralCharacterBalanced
  have hcast :
      (∑ x : I → Bool,
        ((lbitFullCubeCharacter x : ℤ) : ℚ)) = 0 := by
    simpa [lbitFullCubeCharacter_cast_rat] using h
  exact_mod_cast hcast

theorem lbitFullCubeCharacter_one_or_neg_one
    {I : Type*} [Fintype I] (x : I → Bool) :
    lbitFullCubeCharacter x = 1 ∨
      lbitFullCubeCharacter x = -1 := by
  classical
  unfold lbitFullCubeCharacter
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have haSign :
          lbitIntegerSign (x a) = 1 ∨
            lbitIntegerSign (x a) = -1 := by
        cases x a <;> simp [lbitIntegerSign]
      rcases ih with ih | ih <;>
        rcases haSign with haSign | haSign <;>
        simp [ih, haSign]

theorem lbitFullCubeCharacter_toNat_add_neg_toNat
    {I : Type*} [Fintype I] (x : I → Bool) :
    (lbitFullCubeCharacter x).toNat +
        (-lbitFullCubeCharacter x).toNat = 1 := by
  rcases lbitFullCubeCharacter_one_or_neg_one x with h | h <;>
    simp [h]

/-- An `N`-cube alternating character has exactly `2^(N-1)` positive
terms. This is its exact minimum fidelity-replica order. -/
theorem lbitFullCubeCharacter_positiveMass
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] :
    spectralCharacterPositiveMass
        (lbitFullCubeCharacter : (I → Bool) → ℤ) =
      2 ^ (Fintype.card I - 1) := by
  let k : (I → Bool) → ℤ :=
    lbitFullCubeCharacter
  have hbalanced :
      SpectralCharacterBalanced k :=
    lbitFullCubeCharacter_balanced
  have hequal :=
    sum_toNat_eq_sum_neg_toNat_of_spectralCharacterBalanced hbalanced
  have htotal :
      (∑ x : I → Bool, (k x).toNat) +
          (∑ x : I → Bool, (-k x).toNat) =
        2 ^ Fintype.card I := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x : I → Bool,
          ((k x).toNat + (-k x).toNat)) =
          ∑ _x : I → Bool, 1 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact lbitFullCubeCharacter_toNat_add_neg_toNat x
      _ = 2 ^ Fintype.card I := by
        simp only [Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]
        rw [Fintype.card_eq_nat_card, Nat.card_fun]
        norm_num [Nat.card_eq_fintype_card]
  have hdouble :
      2 * spectralCharacterPositiveMass k =
        2 ^ Fintype.card I := by
    unfold spectralCharacterPositiveMass
    omega
  obtain ⟨n, hn⟩ :
      ∃ n, Fintype.card I = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  rw [hn, pow_succ] at hdouble
  rw [hn]
  simp only [Nat.add_sub_cancel]
  change spectralCharacterPositiveMass k = 2 ^ n
  omega

/-- The full Boolean-cube detuning extracts exactly the interaction
coefficient coupling every mode. -/
theorem lbitFullCubeCharacter_detuning
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    finiteTorusCharacterDetuning
        (lbitFullCubeCharacter : (I → Bool) → ℤ)
        (lbitEnergy J) =
      ((2 : ℚ) ^ Fintype.card I) •
        J (Finset.univ : Finset I) := by
  have h :=
    lbitEnergy_walshCoefficient J
      (Finset.univ : Finset I)
  unfold finiteTorusCharacterDetuning
  simpa [lbitFullCubeCharacter_cast_real, Rat.smul_def] using h

theorem lbitFullCubeCharacter_detuning_eq_zero_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    finiteTorusCharacterDetuning
        (lbitFullCubeCharacter : (I → Bool) → ℤ)
        (lbitEnergy J) = 0 ↔
      J (Finset.univ : Finset I) = 0 := by
  rw [lbitFullCubeCharacter_detuning]
  simp [Rat.smul_def]

/-- The alternating full-cube character is realizable at replica height
`2^(N-1)` and at no lower height. -/
theorem lbitFullCubeCharacter_minimumReplica
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] :
    SpectralCharacterReplicaRealizes
        (2 ^ (Fintype.card I - 1))
        (lbitFullCubeCharacter : (I → Bool) → ℤ) ∧
      ∀ n,
        SpectralCharacterReplicaRealizes n
            (lbitFullCubeCharacter : (I → Bool) → ℤ) →
          2 ^ (Fintype.card I - 1) ≤ n := by
  simpa [lbitFullCubeCharacter_positiveMass] using
    spectralCharacterPositiveMass_eq_minimumReplica
      (lbitFullCubeCharacter_balanced (I := I))

/-- **Localized interaction-relation law.** The exact recurrence relation
around the complete `N`-mode configuration cube survives at its minimum
replica height exactly when the `N`-body interaction is absent. -/
theorem lbitTopInteraction_relation_iff
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (J : Finset I → ℝ) :
    ResolvedReplicaDetects
        (lbitEnergy J)
        (2 ^ (Fintype.card I - 1))
        (lbitFullCubeCharacter : (I → Bool) → ℤ) ↔
      J (Finset.univ : Finset I) = 0 := by
  unfold ResolvedReplicaDetects
  rw [lbitFullCubeCharacter_detuning_eq_zero_iff]
  exact and_iff_right lbitFullCubeCharacter_minimumReplica.1

/-- Equivalently, a nonzero top-order localized interaction fractures the
complete-cube recurrence relation. -/
theorem lbitTopInteraction_fracture_iff
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (J : Finset I → ℝ) :
    ¬ ResolvedReplicaDetects
        (lbitEnergy J)
        (2 ^ (Fintype.card I - 1))
        (lbitFullCubeCharacter : (I → Bool) → ℤ) ↔
      J (Finset.univ : Finset I) ≠ 0 := by
  rw [lbitTopInteraction_relation_iff]

/-- A noninteracting localized-mode Hamiltonian has at most one temporal
direction per localized mode. -/
theorem lbitNoninteracting_temporalRank_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hJ : ∀ S, 1 < S.card → J S = 0) :
    lbitTemporalRank J ≤ Fintype.card I := by
  have h := lbitTemporalRank_le_order J 1 hJ
  convert h using 1
  norm_num [Finset.sum_range_succ]

/-- Every two-mode noninteracting localized fixed point retains its
second-replica rectangle relation. -/
theorem lbitTwoMode_noninteracting_rectangleRelation
    (J : Finset (Fin 2) → ℝ)
    (hJ : ∀ S, 1 < S.card → J S = 0) :
    ResolvedReplicaDetects
      (lbitEnergy J) 2
      (lbitFullCubeCharacter :
        ((Fin 2 → Bool) → ℤ)) := by
  have hzero : J Finset.univ = 0 :=
    hJ Finset.univ (by simp)
  simpa using
    (lbitTopInteraction_relation_iff J).2 hzero

/-- A two-mode interaction fractures the noninteracting rectangle relation
exactly when its pair coefficient is nonzero. -/
theorem lbitTwoMode_interaction_fractures_rectangle
    (J : Finset (Fin 2) → ℝ) :
    ¬ ResolvedReplicaDetects
        (lbitEnergy J) 2
        (lbitFullCubeCharacter :
          ((Fin 2 → Bool) → ℤ)) ↔
      J Finset.univ ≠ 0 := by
  simpa using lbitTopInteraction_fracture_iff J

/-- Exact finite-time phase response of the complete Boolean-cube
character. It is the sinc of the isolated top-order interaction
coefficient. -/
theorem lbitFullCube_finitePhaseResponse
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (A : ℝ) :
    (∫ x,
      UnitAddTorus.mFourier
        (lbitFullCubeCharacter : (I → Bool) → ℤ) x
      ∂(finiteTorusPhaseProbabilityMeasure (lbitEnergy J) A :
        Measure (UnitAddTorus (I → Bool)))) =
      Real.sinc
        (A * (((2 : ℚ) ^ Fintype.card I) •
          J (Finset.univ : Finset I))) := by
  rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
    lbitFullCubeCharacter_detuning]

/-- At every nonzero finite observation horizon, the complete-cube phase
response remains exactly one if and only if the top-order interaction is
absent. -/
theorem lbitFullCube_finitePhaseResponse_eq_one_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) {A : ℝ} (hA : A ≠ 0) :
    (∫ x,
      UnitAddTorus.mFourier
        (lbitFullCubeCharacter : (I → Bool) → ℤ) x
      ∂(finiteTorusPhaseProbabilityMeasure (lbitEnergy J) A :
        Measure (UnitAddTorus (I → Bool)))) = 1 ↔
      J (Finset.univ : Finset I) = 0 := by
  rw [lbitFullCube_finitePhaseResponse]
  constructor
  · intro hresponse
    by_contra hJ
    have hscaledJ :
        (((2 : ℚ) ^ Fintype.card I) •
          J (Finset.univ : Finset I)) ≠ 0 := by
      simp [Rat.smul_def, hJ]
    have harg :
        A * (((2 : ℚ) ^ Fintype.card I) •
          J (Finset.univ : Finset I)) ≠ 0 := by
      exact mul_ne_zero hA hscaledJ
    have hsinc :
        Real.sinc
          (A * (((2 : ℚ) ^ Fintype.card I) •
            J (Finset.univ : Finset I))) = 1 := by
      exact_mod_cast hresponse
    exact (real_sinc_ne_one_of_ne_zero harg) hsinc
  · intro hJ
    simp [hJ]

/-- For two localized modes, the finite-time rectangle response is
`sinc(4 A J₁₂)`. -/
theorem lbitTwoMode_finitePhaseResponse
    (J : Finset (Fin 2) → ℝ) (A : ℝ) :
    (∫ x,
      UnitAddTorus.mFourier
        (lbitFullCubeCharacter :
          (Fin 2 → Bool) → ℤ) x
      ∂(finiteTorusPhaseProbabilityMeasure (lbitEnergy J) A :
        Measure (UnitAddTorus (Fin 2 → Bool)))) =
      Real.sinc (4 * A * J Finset.univ) := by
  rw [lbitFullCube_finitePhaseResponse]
  congr 2
  norm_num [Rat.smul_def]
  ring

/-- Calibrating the averaging horizon to `π / |x|` makes every nonzero
detuning's sinc response vanish, independently of its sign. -/
theorem real_sinc_pi_div_abs_mul
    (x : ℝ) (hx : x ≠ 0) :
    Real.sinc (Real.pi / |x| * x) = 0 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have habs : |x| = -x := abs_of_neg hxneg
    have harg : Real.pi / |x| * x = -Real.pi := by
      rw [habs]
      field_simp
    rw [harg, Real.sinc_neg]
    simp [Real.sinc_of_ne_zero Real.pi_ne_zero]
  · have habs : |x| = x := abs_of_pos hxpos
    have harg : Real.pi / |x| * x = Real.pi := by
      rw [habs]
      field_simp
    rw [harg]
    simp [Real.sinc_of_ne_zero Real.pi_ne_zero]

/-- Every nonzero top-order localized interaction has a finite positive
calibrated horizon at which its complete-cube phase response is exactly
zero. The horizon is the inverse magnitude of the amplified detuning
`2^N J_[N]`. -/
theorem lbitFullCube_calibratedPhaseResponse
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hJ : J (Finset.univ : Finset I) ≠ 0) :
    0 <
        Real.pi /
          |(((2 : ℚ) ^ Fintype.card I) •
            J (Finset.univ : Finset I))| ∧
    (∫ x,
      UnitAddTorus.mFourier
        (lbitFullCubeCharacter : (I → Bool) → ℤ) x
      ∂(finiteTorusPhaseProbabilityMeasure
        (lbitEnergy J)
        (Real.pi /
          |(((2 : ℚ) ^ Fintype.card I) •
            J (Finset.univ : Finset I))|) :
        Measure (UnitAddTorus (I → Bool)))) = 0 := by
  have hscaledJ :
      (((2 : ℚ) ^ Fintype.card I) •
        J (Finset.univ : Finset I)) ≠ 0 := by
    simp [Rat.smul_def, hJ]
  constructor
  · exact div_pos Real.pi_pos (abs_pos.mpr hscaledJ)
  · calc
      (∫ x,
        UnitAddTorus.mFourier
          (lbitFullCubeCharacter : (I → Bool) → ℤ) x
        ∂(finiteTorusPhaseProbabilityMeasure
          (lbitEnergy J)
          (Real.pi /
            |(((2 : ℚ) ^ Fintype.card I) •
              J (Finset.univ : Finset I))|) :
          Measure (UnitAddTorus (I → Bool)))) =
          Real.sinc
            ((Real.pi /
                |(((2 : ℚ) ^ Fintype.card I) •
                  J (Finset.univ : Finset I))|) *
              (((2 : ℚ) ^ Fintype.card I) •
                J (Finset.univ : Finset I))) :=
        lbitFullCube_finitePhaseResponse _ _
      _ = 0 := by
        exact_mod_cast real_sinc_pi_div_abs_mul _ hscaledJ

/-- A lower bound `δ` on the amplified complete-cube detuning gives the
explicit detection-horizon guarantee `A ≤ π / δ`. -/
theorem lbitFullCube_calibratedHorizon_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) {δ : ℝ}
    (hδ : 0 < δ)
    (hdetuning :
      δ ≤
        |(((2 : ℚ) ^ Fintype.card I) •
          J (Finset.univ : Finset I))|) :
    Real.pi /
        |(((2 : ℚ) ^ Fintype.card I) •
          J (Finset.univ : Finset I))| ≤
      Real.pi / δ := by
  have hdetuningPos :
      0 <
        |(((2 : ℚ) ^ Fintype.card I) •
          J (Finset.univ : Finset I))| :=
    hδ.trans_le hdetuning
  rw [div_le_div_iff₀ hdetuningPos hδ]
  exact mul_le_mul_of_nonneg_left hdetuning Real.pi_pos.le

/-- Complex measurements lying within error `< 1/2` of the unit-separated
responses zero and one cannot coincide. -/
theorem complex_measurements_separated_of_error_lt_half
    {z₀ z₁ : ℂ} {ε : ℝ}
    (hε : ε < (1 : ℝ) / 2)
    (h₀ : dist z₀ 0 ≤ ε)
    (h₁ : dist z₁ 1 ≤ ε) :
    z₀ ≠ z₁ := by
  intro h
  subst z₁
  have htriangle :
      dist (0 : ℂ) 1 ≤ dist 0 z₀ + dist z₀ 1 :=
    dist_triangle _ _ _
  have hbound : dist (0 : ℂ) 1 ≤ ε + ε :=
    htriangle.trans (add_le_add (by simpa [dist_comm] using h₀) h₁)
  have hdistance : dist (0 : ℂ) 1 = 1 := by
    norm_num [dist_eq_norm]
  rw [hdistance] at hbound
  linarith

/-- Robust finite-resolution separation of an absent top interaction from
a nonzero one. At the interacting system's calibrated horizon the exact
responses are zero and one, so any two measurements with error `< 1/2`
are necessarily distinct. -/
theorem lbitFullCube_measurementsSeparated
    {I : Type*} [Fintype I] [DecidableEq I]
    (J₀ J₁ : Finset I → ℝ)
    (hJ₀ : J₀ (Finset.univ : Finset I) = 0)
    (hJ₁ : J₁ (Finset.univ : Finset I) ≠ 0)
    {ε : ℝ} (hε : ε < (1 : ℝ) / 2)
    {z₀ z₁ : ℂ}
    (hmeasurement₀ :
      dist z₀
        (∫ x,
          UnitAddTorus.mFourier
            (lbitFullCubeCharacter : (I → Bool) → ℤ) x
          ∂(finiteTorusPhaseProbabilityMeasure
            (lbitEnergy J₁)
            (Real.pi /
              |(((2 : ℚ) ^ Fintype.card I) •
                J₁ (Finset.univ : Finset I))|) :
            Measure (UnitAddTorus (I → Bool)))) ≤ ε)
    (hmeasurement₁ :
      dist z₁
        (∫ x,
          UnitAddTorus.mFourier
            (lbitFullCubeCharacter : (I → Bool) → ℤ) x
          ∂(finiteTorusPhaseProbabilityMeasure
            (lbitEnergy J₀)
            (Real.pi /
              |(((2 : ℚ) ^ Fintype.card I) •
                J₁ (Finset.univ : Finset I))|) :
            Measure (UnitAddTorus (I → Bool)))) ≤ ε) :
    z₀ ≠ z₁ := by
  have hzeroResponse :
      (∫ x,
        UnitAddTorus.mFourier
          (lbitFullCubeCharacter : (I → Bool) → ℤ) x
        ∂(finiteTorusPhaseProbabilityMeasure
          (lbitEnergy J₁)
          (Real.pi /
            |(((2 : ℚ) ^ Fintype.card I) •
              J₁ (Finset.univ : Finset I))|) :
          Measure (UnitAddTorus (I → Bool)))) = 0 :=
    (lbitFullCube_calibratedPhaseResponse J₁ hJ₁).2
  have honeResponse :
      (∫ x,
        UnitAddTorus.mFourier
          (lbitFullCubeCharacter : (I → Bool) → ℤ) x
        ∂(finiteTorusPhaseProbabilityMeasure
          (lbitEnergy J₀)
          (Real.pi /
            |(((2 : ℚ) ^ Fintype.card I) •
              J₁ (Finset.univ : Finset I))|) :
          Measure (UnitAddTorus (I → Bool)))) = 1 := by
    rw [lbitFullCube_finitePhaseResponse]
    simp [hJ₀]
  rw [hzeroResponse] at hmeasurement₀
  rw [honeResponse] at hmeasurement₁
  exact
    complex_measurements_separated_of_error_lt_half
      hε hmeasurement₀ hmeasurement₁

end

end GaloisForLFunctions.HTGeometry
