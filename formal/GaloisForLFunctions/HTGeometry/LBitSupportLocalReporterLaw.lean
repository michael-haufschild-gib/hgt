import GaloisForLFunctions.HTGeometry.LBitReplicaInteractionFractureLaw

/-!
# Support-local reporters for diagonal l-bit energies

Split a finite l-bit system into a target block `L` and an outside block
`O`.  Holding one outside configuration fixed and varying only `L` gives a
slice of exactly `2 ^ card L` configurations.

The full Walsh contrast on that slice does not isolate the bare coefficient
on `L`.  It exactly extracts the coefficient dressed by every interaction
whose outside support is compatible with the fixed background.  The
difference from the bare coefficient is bounded by the strict `ℓ¹`
interaction tail.  Thus the reporter cost depends on target support size,
not ambient system size, while its unavoidable environmental contamination
is explicit.
-/

open MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance lbitSupportLocalReporterFintypeForallBool
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

/-- Real form of one finite Boolean Walsh character. -/
def lbitWalshCharacterReal
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (x : I → Bool) : ℝ :=
  (lbitWalshCharacter S x : ℚ)

/-- Orthogonality of the real-valued Walsh characters. -/
theorem sum_lbitWalshCharacterReal_mul
    {I : Type*} [Fintype I] [DecidableEq I]
    (S T : Finset I) :
    (∑ x : I → Bool,
      lbitWalshCharacterReal S x *
        lbitWalshCharacterReal T x) =
      if S = T then (2 : ℝ) ^ Fintype.card I else 0 := by
  have h := congrArg (fun q : ℚ => (q : ℝ))
    (sum_lbitWalshCharacter_mul S T)
  by_cases hST : S = T
  · simpa [lbitWalshCharacterReal, hST] using h
  · simpa [lbitWalshCharacterReal, hST] using h

/-- Configuration obtained by varying the target block and holding the
outside block fixed. -/
def lbitSupportSliceConfiguration
    {L O : Type*}
    (u : L → Bool) (η : O → Bool) : Sum L O → Bool :=
  Sum.elim u η

/-- A target block with `card L` l-bits has exactly `2 ^ card L`
fixed-background slice configurations. -/
theorem card_lbitSupportSliceConfigurations
    (L : Type*) [Fintype L] :
    Fintype.card (L → Bool) = 2 ^ Fintype.card L := by
  rw [Fintype.card_eq_nat_card, Nat.card_fun]
  norm_num [Nat.card_eq_fintype_card]

/-- Complete diagonal l-bit energy in coordinates adapted to a target block
and its outside complement.  `J A B` is the coefficient supported on target
sites `A` and outside sites `B`. -/
def lbitBipartiteEnergy
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (x : Sum L O → Bool) : ℝ :=
  ∑ A : Finset L, ∑ B : Finset O,
    lbitWalshCharacterReal A (fun i => x (Sum.inl i)) *
      lbitWalshCharacterReal B (fun j => x (Sum.inr j)) *
        J A B

/-- Canonical decomposition of a support in `L ⊕ O` into its target and
outside parts. -/
def lbitSupportSumEquiv
    (L O : Type*) [Fintype L] [Fintype O]
    [DecidableEq L] [DecidableEq O] :
    Finset (Sum L O) ≃ Finset L × Finset O where
  toFun S := (S.toLeft, S.toRight)
  invFun p := p.1.disjSum p.2
  left_inv S := by
    exact Finset.toLeft_disjSum_toRight
  right_inv p := by
    ext <;> simp

/-- A Walsh character on a bipartite support factors into the target and
outside Walsh characters. -/
theorem lbitWalshCharacter_disjSum
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (A : Finset L) (B : Finset O)
    (x : Sum L O → Bool) :
    lbitWalshCharacter (A.disjSum B) x =
      lbitWalshCharacter A (fun i => x (Sum.inl i)) *
        lbitWalshCharacter B (fun j => x (Sum.inr j)) := by
  classical
  simp [lbitWalshCharacter]

/-- Standard single-support coefficients expressed in target/outside
coordinates. -/
def lbitBipartiteCoefficientOf
    {L O : Type*}
    (J : Finset (Sum L O) → ℝ)
    (A : Finset L) (B : Finset O) : ℝ :=
  J (A.disjSum B)

/-- The bipartite energy is not a restricted model: after canonical support
decomposition it is exactly the standard finite l-bit energy. -/
theorem lbitBipartiteEnergy_coefficientOf_eq_lbitEnergy
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset (Sum L O) → ℝ)
    (x : Sum L O → Bool) :
    lbitBipartiteEnergy (lbitBipartiteCoefficientOf J) x =
      lbitEnergy J x := by
  classical
  unfold lbitBipartiteEnergy lbitEnergy lbitBipartiteCoefficientOf
  simp only [lbitWalshCharacterReal, Rat.smul_def]
  rw [show
      (∑ S : Finset (Sum L O),
        (lbitWalshCharacter S x : ℝ) * J S) =
        ∑ p : Finset L × Finset O,
          (lbitWalshCharacter (p.1.disjSum p.2) x : ℝ) *
            J (p.1.disjSum p.2) by
    exact (Equiv.sum_comp
      (lbitSupportSumEquiv L O).symm
      (fun S : Finset (Sum L O) =>
        (lbitWalshCharacter S x : ℝ) * J S)).symm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  rw [lbitWalshCharacter_disjSum]
  push_cast
  ring

/-- Energy restricted to one outside configuration. -/
def lbitSupportSliceEnergy
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool) (u : L → Bool) : ℝ :=
  lbitBipartiteEnergy J (lbitSupportSliceConfiguration u η)

/-- Dressed coefficient seen by the target-block reporter in outside
configuration `η`.  The empty outside support is the bare target coefficient;
all nonempty outside supports form the dressing tail. -/
def lbitDressedConditionalCoefficient
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool) : ℝ :=
  J Finset.univ ∅ +
    ∑ B ∈ (Finset.univ.erase (∅ : Finset O)),
      lbitWalshCharacterReal B η * J Finset.univ B

/-- Full Walsh detuning on a fixed-background target slice. -/
def lbitSupportSliceDetuning
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool) : ℝ :=
  ∑ u : L → Bool,
    lbitWalshCharacterReal (Finset.univ : Finset L) u *
      lbitSupportSliceEnergy J η u

/-- The strict outside-support `ℓ¹` mass dressing the bare target
coefficient. -/
def lbitStrictDressingMass
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ) : ℝ :=
  ∑ B ∈ (Finset.univ.erase (∅ : Finset O)),
    |J Finset.univ B|

private theorem sum_outsideWalsh_eq_dressed
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool) :
    (∑ B : Finset O,
      lbitWalshCharacterReal B η * J Finset.univ B) =
      lbitDressedConditionalCoefficient J η := by
  classical
  calc
    (∑ B : Finset O,
        lbitWalshCharacterReal B η * J Finset.univ B) =
        (∑ B ∈ (Finset.univ.erase (∅ : Finset O)),
          lbitWalshCharacterReal B η * J Finset.univ B) +
          lbitWalshCharacterReal ∅ η * J Finset.univ ∅ := by
      exact (Finset.sum_erase_add Finset.univ
        (fun B : Finset O =>
          lbitWalshCharacterReal B η * J Finset.univ B)
        (Finset.mem_univ ∅)).symm
    _ = lbitDressedConditionalCoefficient J η := by
      simp [lbitDressedConditionalCoefficient, add_comm,
        lbitWalshCharacterReal, lbitWalshCharacter]

/-- **Exact support-local reporter law.**  The alternating contrast of the
`2 ^ card L` energies in one fixed-background slice is exactly `2 ^ card L`
times the environmentally dressed target coefficient. -/
theorem lbitSupportSliceDetuning_eq
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool) :
    lbitSupportSliceDetuning J η =
      (2 : ℝ) ^ Fintype.card L *
        lbitDressedConditionalCoefficient J η := by
  classical
  unfold lbitSupportSliceDetuning lbitSupportSliceEnergy
    lbitBipartiteEnergy
  simp only [lbitSupportSliceConfiguration, Sum.elim_inl, Sum.elim_inr]
  calc
    (∑ u : L → Bool,
        lbitWalshCharacterReal (Finset.univ : Finset L) u *
          ∑ A : Finset L, ∑ B : Finset O,
            lbitWalshCharacterReal A u *
              lbitWalshCharacterReal B η * J A B) =
        ∑ A : Finset L, ∑ B : Finset O,
          (∑ u : L → Bool,
            lbitWalshCharacterReal (Finset.univ : Finset L) u *
              lbitWalshCharacterReal A u) *
            (lbitWalshCharacterReal B η * J A B) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ = ∑ A : Finset L, ∑ B : Finset O,
          (if (Finset.univ : Finset L) = A
            then (2 : ℝ) ^ Fintype.card L else 0) *
            (lbitWalshCharacterReal B η * J A B) := by
      simp_rw [sum_lbitWalshCharacterReal_mul]
    _ = (2 : ℝ) ^ Fintype.card L *
          (∑ B : Finset O,
            lbitWalshCharacterReal B η * J Finset.univ B) := by
      rw [Finset.sum_eq_single Finset.univ]
      · simp only [ite_true]
        rw [Finset.mul_sum]
      · intro A hA hAne
        simp [Ne.symm hAne]
      · simp
    _ = (2 : ℝ) ^ Fintype.card L *
          lbitDressedConditionalCoefficient J η := by
      rw [sum_outsideWalsh_eq_dressed]

/-- Centered finite-time phase response of the support-local character. -/
def lbitSupportLocalFinitePhaseResponse
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool) (A : ℝ) : ℂ :=
  ∫ x,
    UnitAddTorus.mFourier
      (lbitFullCubeCharacter : (L → Bool) → ℤ) x
    ∂(finiteTorusPhaseProbabilityMeasure
      (lbitSupportSliceEnergy J η) A :
      Measure (UnitAddTorus (L → Bool)))

private theorem finiteTorusCharacterDetuning_lbitFullCube_sliceEnergy_eq
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool) :
    finiteTorusCharacterDetuning
        (lbitFullCubeCharacter : (L → Bool) → ℤ)
        (lbitSupportSliceEnergy J η) =
      lbitSupportSliceDetuning J η := by
  unfold finiteTorusCharacterDetuning lbitSupportSliceDetuning
  apply Finset.sum_congr rfl
  intro u hu
  rw [lbitFullCubeCharacter_cast_real]
  rfl

/-- Exact finite-time sinc law for the support-local reporter. -/
theorem lbitSupportLocalFinitePhaseResponse_eq_sinc
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool) (A : ℝ) :
    lbitSupportLocalFinitePhaseResponse J η A =
      Real.sinc
        (A * ((2 : ℝ) ^ Fintype.card L *
          lbitDressedConditionalCoefficient J η)) := by
  rw [lbitSupportLocalFinitePhaseResponse,
    finiteTorusPhaseProbabilityMeasure_mFourier_integral,
    finiteTorusCharacterDetuning_lbitFullCube_sliceEnergy_eq,
    lbitSupportSliceDetuning_eq]

/-- Every nonzero dressed coefficient has a finite positive calibrated
horizon at which its support-local phase response vanishes exactly. -/
theorem lbitSupportLocal_calibratedPhaseResponse
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool)
    (hJ : lbitDressedConditionalCoefficient J η ≠ 0) :
    let detuning :=
      (2 : ℝ) ^ Fintype.card L *
        lbitDressedConditionalCoefficient J η
    0 < Real.pi / |detuning| ∧
      lbitSupportLocalFinitePhaseResponse J η
        (Real.pi / |detuning|) = 0 := by
  dsimp only
  have hdetuning :
      (2 : ℝ) ^ Fintype.card L *
          lbitDressedConditionalCoefficient J η ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hJ
  constructor
  · exact div_pos Real.pi_pos (abs_pos.mpr hdetuning)
  · rw [lbitSupportLocalFinitePhaseResponse_eq_sinc]
    exact_mod_cast
      real_sinc_pi_div_abs_mul
        ((2 : ℝ) ^ Fintype.card L *
          lbitDressedConditionalCoefficient J η)
        hdetuning

/-- Deterministic complex errors below one half cannot confuse the zero
and nonzero dressed-coefficient responses at the nonzero system's
calibrated finite horizon. -/
theorem lbitSupportLocal_measurementsSeparated
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J₀ J₁ : Finset L → Finset O → ℝ)
    (η : O → Bool)
    (hJ₀ : lbitDressedConditionalCoefficient J₀ η = 0)
    (hJ₁ : lbitDressedConditionalCoefficient J₁ η ≠ 0)
    {ε : ℝ} (hε : ε < (1 : ℝ) / 2)
    {z₀ z₁ : ℂ}
    (hmeasurement₀ :
      dist z₀
        (lbitSupportLocalFinitePhaseResponse J₁ η
          (Real.pi /
            |((2 : ℝ) ^ Fintype.card L *
              lbitDressedConditionalCoefficient J₁ η)|)) ≤ ε)
    (hmeasurement₁ :
      dist z₁
        (lbitSupportLocalFinitePhaseResponse J₀ η
          (Real.pi /
            |((2 : ℝ) ^ Fintype.card L *
              lbitDressedConditionalCoefficient J₁ η)|)) ≤ ε) :
    z₀ ≠ z₁ := by
  have hzeroResponse :
      lbitSupportLocalFinitePhaseResponse J₁ η
          (Real.pi /
            |((2 : ℝ) ^ Fintype.card L *
              lbitDressedConditionalCoefficient J₁ η)|) = 0 :=
    (lbitSupportLocal_calibratedPhaseResponse J₁ η hJ₁).2
  have honeResponse :
      lbitSupportLocalFinitePhaseResponse J₀ η
          (Real.pi /
            |((2 : ℝ) ^ Fintype.card L *
              lbitDressedConditionalCoefficient J₁ η)|) = 1 := by
    rw [lbitSupportLocalFinitePhaseResponse_eq_sinc, hJ₀]
    norm_num
  rw [hzeroResponse] at hmeasurement₀
  rw [honeResponse] at hmeasurement₁
  exact complex_measurements_separated_of_error_lt_half
    hε hmeasurement₀ hmeasurement₁

/-- **Finite strict-tail contamination bound.**  Uniformly in the fixed
outside configuration, the dressed coefficient differs from the bare
target coefficient by at most the strict outside-support `ℓ¹` mass. -/
theorem abs_lbitDressedConditionalCoefficient_sub_bare_le
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool) :
    |lbitDressedConditionalCoefficient J η -
        J Finset.univ ∅| ≤
      lbitStrictDressingMass J := by
  classical
  rw [lbitDressedConditionalCoefficient]
  ring_nf
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro B hB
  rw [abs_mul]
  have hWalsh :
      |lbitWalshCharacterReal B η| = 1 := by
    simpa [lbitWalshCharacterReal] using
      abs_lbitWalshCharacter B η
  rw [hWalsh, one_mul]

/-- The raw support-local detuning differs from the amplified bare target
coefficient by at most the same amplified strict dressing mass. -/
theorem abs_lbitSupportSliceDetuning_sub_bare_le
    {L O : Type*}
    [Fintype L] [DecidableEq L]
    [Fintype O] [DecidableEq O]
    (J : Finset L → Finset O → ℝ)
    (η : O → Bool) :
    |lbitSupportSliceDetuning J η -
        (2 : ℝ) ^ Fintype.card L * J Finset.univ ∅| ≤
      (2 : ℝ) ^ Fintype.card L * lbitStrictDressingMass J := by
  rw [lbitSupportSliceDetuning_eq]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (abs_lbitDressedConditionalCoefficient_sub_bare_le J η)
    (by positivity)

end

end GaloisForLFunctions.HTGeometry
