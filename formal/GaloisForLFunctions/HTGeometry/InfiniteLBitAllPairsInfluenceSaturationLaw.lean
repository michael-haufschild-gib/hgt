import GaloisForLFunctions.HTGeometry.InfiniteLBitRecurrenceLocalitySeparationLaw

/-!
# All-pairs influence saturation for the infinite l-bit field

Every nonempty interaction coefficient in the fixed infinite l-bit field is
strictly positive.  At the all-false configuration this prevents cancellation
in every two-site double energy difference.  For each pair of distinct sites,
the positive double difference supplies an explicit time at which the
Heisenberg flip commutator attains the universal two-unit norm ceiling on the
constant unit amplitude.
-/

open Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every nonempty interaction coefficient in the fixed quasi-local field is
strictly positive. -/
theorem quasiLocalInfiniteLBitCoefficient_pos
    (S : Finset ℕ) (hS : S.Nonempty) :
    0 < quasiLocalInfiniteLBitCoefficient S := by
  let p : Nat.Primes :=
    nonemptyFiniteSupportPrimeEmbedding ⟨S, hS⟩
  have hscaleQ :
      (0 : ℚ) < quasiLocalLBitRationalScale ⟨S, hS⟩ := by
    change
      (0 : ℚ) <
        1 /
          (((p : ℕ) : ℚ) *
            2 ^ quasiLocalLBitSupportComplexity S)
    exact one_div_pos.mpr
      (mul_pos
        (by exact_mod_cast p.2.pos)
        (pow_pos (by norm_num) _))
  rw [quasiLocalInfiniteLBitCoefficient, dif_pos hS]
  change
    0 <
      (quasiLocalLBitRationalScale ⟨S, hS⟩ : ℝ) *
        primeLogSupport p
  exact mul_pos
    (by exact_mod_cast hscaleQ)
    (primeLogSupport_pos p)

/-- Every interaction coefficient is nonnegative, including the zero
coefficient on the empty support. -/
theorem quasiLocalInfiniteLBitCoefficient_nonneg
    (S : Finset ℕ) :
    0 ≤ quasiLocalInfiniteLBitCoefficient S := by
  by_cases hS : S.Nonempty
  · exact (quasiLocalInfiniteLBitCoefficient_pos S hS).le
  · simp [quasiLocalInfiniteLBitCoefficient, hS]

/-- The coefficient field itself is summable because it is nonnegative and
its absolute-value field is summable. -/
theorem summable_quasiLocalInfiniteLBitCoefficient :
    Summable quasiLocalInfiniteLBitCoefficient := by
  have heq :
      (fun S : Finset ℕ =>
        |quasiLocalInfiniteLBitCoefficient S|) =
        quasiLocalInfiniteLBitCoefficient := by
    funext S
    rw [abs_of_nonneg
      (quasiLocalInfiniteLBitCoefficient_nonneg S)]
  rw [← heq]
  exact summable_abs_quasiLocalInfiniteLBitCoefficient

/-- The configuration with every l-bit equal to false. -/
def infiniteLBitAllFalse : InfiniteLBitConfiguration :=
  fun _ => false

@[simp]
theorem infiniteLBitCharacter_allFalse
    (S : Finset ℕ) :
    infiniteLBitCharacter S infiniteLBitAllFalse = 1 := by
  simp [infiniteLBitCharacter, infiniteLBitAllFalse]

/-- Flipping a site contained in a Walsh support reverses its character. -/
theorem infiniteLBitCharacter_flip_of_mem
    (S : Finset ℕ) {i : ℕ} (hi : i ∈ S)
    (σ : InfiniteLBitConfiguration) :
    infiniteLBitCharacter S (infiniteLBitFlip i σ) =
      -infiniteLBitCharacter S σ := by
  classical
  have hie : i ∉ S.erase i := by simp
  have hrest :
      infiniteLBitCharacter (S.erase i)
          (infiniteLBitFlip i σ) =
        infiniteLBitCharacter (S.erase i) σ :=
    infiniteLBitCharacter_flip_of_not_mem
      (S.erase i) hie σ
  calc
    infiniteLBitCharacter S (infiniteLBitFlip i σ) =
        (if infiniteLBitFlip i σ i then (-1 : ℝ) else 1) *
          infiniteLBitCharacter (S.erase i)
            (infiniteLBitFlip i σ) := by
              rw [← Finset.insert_erase hi]
              simp [infiniteLBitCharacter, hie]
    _ =
        -((if σ i then (-1 : ℝ) else 1) *
          infiniteLBitCharacter (S.erase i) σ) := by
            rw [hrest, infiniteLBitFlip_apply_self]
            cases hσ : σ i <;> simp
    _ = -infiniteLBitCharacter S σ := by
      rw [← Finset.insert_erase hi]
      simp [infiniteLBitCharacter, hie]

/-- At the all-false configuration, one interaction contributes four times
its coefficient to a double flip exactly when it contains both sites. -/
theorem infiniteLBitEnergyTermDoubleFlip_allFalse
    (S : Finset ℕ) (x y : ℕ) :
    infiniteLBitEnergyTermDoubleFlip
        S x y infiniteLBitAllFalse =
      if x ∈ S ∧ y ∈ S then
        4 * quasiLocalInfiniteLBitCoefficient S
      else 0 := by
  classical
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · rw [if_pos ⟨hx, hy⟩]
      have hxchar :
          infiniteLBitCharacter S
              (infiniteLBitFlip x infiniteLBitAllFalse) =
            -infiniteLBitCharacter S infiniteLBitAllFalse :=
        infiniteLBitCharacter_flip_of_mem
          S hx infiniteLBitAllFalse
      have hychar :
          infiniteLBitCharacter S
              (infiniteLBitFlip y infiniteLBitAllFalse) =
            -infiniteLBitCharacter S infiniteLBitAllFalse :=
        infiniteLBitCharacter_flip_of_mem
          S hy infiniteLBitAllFalse
      have hdouble :
          infiniteLBitCharacter S
              (infiniteLBitFlip x
                (infiniteLBitFlip y infiniteLBitAllFalse)) =
            infiniteLBitCharacter S infiniteLBitAllFalse := by
        rw [infiniteLBitCharacter_flip_of_mem S hx,
          infiniteLBitCharacter_flip_of_mem S hy]
        ring
      unfold infiniteLBitEnergyTermDoubleFlip
      unfold quasiLocalInfiniteLBitEnergyTerm
      rw [hdouble, hxchar, hychar,
        infiniteLBitCharacter_allFalse]
      ring
    · rw [if_neg (by simp [hy])]
      have hdouble :
          infiniteLBitCharacter S
              (infiniteLBitFlip x
                (infiniteLBitFlip y infiniteLBitAllFalse)) =
            infiniteLBitCharacter S
              (infiniteLBitFlip x infiniteLBitAllFalse) := by
        calc
          infiniteLBitCharacter S
              (infiniteLBitFlip x
                (infiniteLBitFlip y infiniteLBitAllFalse)) =
            infiniteLBitCharacter S
              (infiniteLBitFlip y
                (infiniteLBitFlip x infiniteLBitAllFalse)) := by
                  rw [infiniteLBitFlip_commute]
          _ =
            infiniteLBitCharacter S
              (infiniteLBitFlip x infiniteLBitAllFalse) :=
                infiniteLBitCharacter_flip_of_not_mem
                  S hy
                  (infiniteLBitFlip x infiniteLBitAllFalse)
      have hychar :
          infiniteLBitCharacter S
              (infiniteLBitFlip y infiniteLBitAllFalse) =
            infiniteLBitCharacter S infiniteLBitAllFalse :=
        infiniteLBitCharacter_flip_of_not_mem
          S hy infiniteLBitAllFalse
      unfold infiniteLBitEnergyTermDoubleFlip
      unfold quasiLocalInfiniteLBitEnergyTerm
      rw [hdouble, hychar]
      ring
  · rw [if_neg (by simp [hx])]
    have hdouble :
        infiniteLBitCharacter S
            (infiniteLBitFlip x
              (infiniteLBitFlip y infiniteLBitAllFalse)) =
          infiniteLBitCharacter S
            (infiniteLBitFlip y infiniteLBitAllFalse) :=
      infiniteLBitCharacter_flip_of_not_mem
        S hx (infiniteLBitFlip y infiniteLBitAllFalse)
    have hxchar :
        infiniteLBitCharacter S
            (infiniteLBitFlip x infiniteLBitAllFalse) =
          infiniteLBitCharacter S infiniteLBitAllFalse :=
      infiniteLBitCharacter_flip_of_not_mem
        S hx infiniteLBitAllFalse
    unfold infiniteLBitEnergyTermDoubleFlip
    unfold quasiLocalInfiniteLBitEnergyTerm
    rw [hdouble, hxchar]
    ring

/-- Total positive interaction mass incident on a pair of sites. -/
def quasiLocalInfiniteLBitPairInteractionMass
    (x y : ℕ) : ℝ :=
  ∑' S : Finset ℕ,
    if x ∈ S ∧ y ∈ S then
      quasiLocalInfiniteLBitCoefficient S
    else 0

theorem summable_quasiLocalInfiniteLBitPairInteractionCoefficient
    (x y : ℕ) :
    Summable
      (fun S : Finset ℕ =>
        if x ∈ S ∧ y ∈ S then
          quasiLocalInfiniteLBitCoefficient S
        else 0) := by
  apply Summable.of_nonneg_of_le
    (fun S => by
      by_cases hS : x ∈ S ∧ y ∈ S
      · simp [hS, quasiLocalInfiniteLBitCoefficient_nonneg S]
      · simp [hS])
    (fun S => by
      by_cases hS : x ∈ S ∧ y ∈ S
      · simp [hS,
          abs_of_nonneg
            (quasiLocalInfiniteLBitCoefficient_nonneg S)]
      · simp [hS])
    summable_abs_quasiLocalInfiniteLBitCoefficient

theorem quasiLocalInfiniteLBitPairInteractionMass_pos
    (x y : ℕ) :
    0 < quasiLocalInfiniteLBitPairInteractionMass x y := by
  unfold quasiLocalInfiniteLBitPairInteractionMass
  refine
    (summable_quasiLocalInfiniteLBitPairInteractionCoefficient x y).tsum_pos
      (fun S => ?_) {x, y} ?_
  · split_ifs
    · exact quasiLocalInfiniteLBitCoefficient_nonneg S
    · exact le_rfl
  · rw [if_pos (by simp)]
    exact quasiLocalInfiniteLBitCoefficient_pos
      {x, y} (by simp)

/-- Exact no-cancellation formula for the pair double energy at the
all-false configuration. -/
theorem infiniteLBitEnergyDoubleFlip_allFalse_eq
    (x y : ℕ) :
    infiniteLBitEnergyDoubleFlip x y infiniteLBitAllFalse =
      4 * quasiLocalInfiniteLBitPairInteractionMass x y := by
  rw [infiniteLBitEnergyDoubleFlip_eq_tsum]
  calc
    (∑' S : Finset ℕ,
        infiniteLBitEnergyTermDoubleFlip
          S x y infiniteLBitAllFalse) =
      ∑' S : Finset ℕ,
        if x ∈ S ∧ y ∈ S then
          4 * quasiLocalInfiniteLBitCoefficient S
        else 0 := by
          apply tsum_congr
          intro S
          exact infiniteLBitEnergyTermDoubleFlip_allFalse S x y
    _ =
      ∑' S : Finset ℕ,
        4 *
          (if x ∈ S ∧ y ∈ S then
            quasiLocalInfiniteLBitCoefficient S
          else 0) := by
            apply tsum_congr
            intro S
            split_ifs <;> ring
    _ =
      4 * quasiLocalInfiniteLBitPairInteractionMass x y := by
        rw [quasiLocalInfiniteLBitPairInteractionMass, tsum_mul_left]

/-- Every pair has a strictly positive double energy at the all-false
configuration. -/
theorem infiniteLBitEnergyDoubleFlip_allFalse_pos
    (x y : ℕ) :
    0 <
      infiniteLBitEnergyDoubleFlip
        x y infiniteLBitAllFalse := by
  rw [infiniteLBitEnergyDoubleFlip_allFalse_eq]
  exact mul_pos (by norm_num)
    (quasiLocalInfiniteLBitPairInteractionMass_pos x y)

/-- Explicit saturation time for one pair. -/
noncomputable def quasiLocalInfiniteLBitPairSaturationTime
    (x y : ℕ) : ℝ :=
  Real.pi /
    infiniteLBitEnergyDoubleFlip x y infiniteLBitAllFalse

theorem quasiLocalInfiniteLBitPairSaturationTime_pos
    (x y : ℕ) :
    0 < quasiLocalInfiniteLBitPairSaturationTime x y := by
  exact div_pos Real.pi_pos
    (infiniteLBitEnergyDoubleFlip_allFalse_pos x y)

theorem quasiLocalInfiniteLBitPairSaturationTime_mul_doubleFlip
    (x y : ℕ) :
    quasiLocalInfiniteLBitPairSaturationTime x y *
        infiniteLBitEnergyDoubleFlip
          x y infiniteLBitAllFalse =
      Real.pi := by
  unfold quasiLocalInfiniteLBitPairSaturationTime
  exact div_mul_cancel₀ Real.pi
    (ne_of_gt
      (infiniteLBitEnergyDoubleFlip_allFalse_pos x y))

/-- A phase difference of `pi` makes the two Heisenberg flip phases
antipodal. -/
theorem quasiLocalInfiniteLBitHeisenbergFlipPhase_flip_eq_neg
    (t : ℝ) (x y : ℕ) (σ : InfiniteLBitConfiguration)
    (hphase :
      t * infiniteLBitEnergyDoubleFlip x y σ = Real.pi) :
    quasiLocalInfiniteLBitHeisenbergFlipPhase t x
        (infiniteLBitFlip y σ) =
      -quasiLocalInfiniteLBitHeisenbergFlipPhase t x σ := by
  let a : ℝ :=
    quasiLocalInfiniteLBitEnergy
        (infiniteLBitFlip x (infiniteLBitFlip y σ)) -
      quasiLocalInfiniteLBitEnergy (infiniteLBitFlip y σ)
  let b : ℝ :=
    quasiLocalInfiniteLBitEnergy (infiniteLBitFlip x σ) -
      quasiLocalInfiniteLBitEnergy σ
  have hab :
      t * a = t * b + Real.pi := by
    rw [← hphase]
    simp only [a, b, infiniteLBitEnergyDoubleFlip]
    ring
  have harg :
      t • (Complex.I * (a : ℂ)) =
        t • (Complex.I * (b : ℂ)) +
          (Real.pi : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [RCLike.real_smul_eq_coe_mul]
    · simpa [RCLike.real_smul_eq_coe_mul] using hab
  rw [quasiLocalInfiniteLBitHeisenbergFlipPhase,
    quasiLocalInfiniteLBitHeisenbergFlipPhase]
  change
    Complex.exp (t • (Complex.I * (a : ℂ))) =
      -Complex.exp (t • (Complex.I * (b : ℂ)))
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- Constant normalized amplitude used to witness operator-norm
saturation. -/
noncomputable def quasiLocalInfiniteLBitUnitAmplitude :
    ContinuousInfiniteLBitAmplitude :=
  ContinuousMap.const InfiniteLBitConfiguration 1

@[simp]
theorem quasiLocalInfiniteLBitUnitAmplitude_apply
    (σ : InfiniteLBitConfiguration) :
    quasiLocalInfiniteLBitUnitAmplitude σ = 1 :=
  rfl

@[simp]
theorem norm_quasiLocalInfiniteLBitUnitAmplitude :
    ‖quasiLocalInfiniteLBitUnitAmplitude‖ = 1 := by
  apply le_antisymm
  · rw [ContinuousMap.norm_le _ (by norm_num)]
    intro σ
    simp
  · simpa using
      (ContinuousMap.norm_coe_le_norm
        quasiLocalInfiniteLBitUnitAmplitude infiniteLBitAllFalse)

/-- Every pair of distinct sites attains the universal two-unit
commutator ceiling at its explicit positive saturation time. -/
theorem norm_quasiLocalInfiniteLBitFlipCommutator_pairSaturationTime
    (x y : ℕ) :
    ‖quasiLocalInfiniteLBitFlipCommutator
        (quasiLocalInfiniteLBitPairSaturationTime x y)
        x y quasiLocalInfiniteLBitUnitAmplitude‖ = 2 := by
  let t := quasiLocalInfiniteLBitPairSaturationTime x y
  let C :=
    quasiLocalInfiniteLBitFlipCommutator
      t x y quasiLocalInfiniteLBitUnitAmplitude
  have hphase :
      quasiLocalInfiniteLBitHeisenbergFlipPhase t x
          (infiniteLBitFlip y infiniteLBitAllFalse) =
        -quasiLocalInfiniteLBitHeisenbergFlipPhase
          t x infiniteLBitAllFalse := by
    exact
      quasiLocalInfiniteLBitHeisenbergFlipPhase_flip_eq_neg
        t x y infiniteLBitAllFalse
        (quasiLocalInfiniteLBitPairSaturationTime_mul_doubleFlip
          x y)
  have heval :
      ‖C infiniteLBitAllFalse‖ = 2 := by
    rw [show C infiniteLBitAllFalse =
        (quasiLocalInfiniteLBitHeisenbergFlipPhase
              t x infiniteLBitAllFalse -
            quasiLocalInfiniteLBitHeisenbergFlipPhase t x
              (infiniteLBitFlip y infiniteLBitAllFalse)) *
          quasiLocalInfiniteLBitUnitAmplitude
            (infiniteLBitFlip y
              (infiniteLBitFlip x infiniteLBitAllFalse)) by
          exact quasiLocalInfiniteLBitFlipCommutator_apply
            t x y quasiLocalInfiniteLBitUnitAmplitude
              infiniteLBitAllFalse]
    rw [quasiLocalInfiniteLBitUnitAmplitude_apply, mul_one,
      hphase]
    calc
      ‖quasiLocalInfiniteLBitHeisenbergFlipPhase
            t x infiniteLBitAllFalse -
          -quasiLocalInfiniteLBitHeisenbergFlipPhase
            t x infiniteLBitAllFalse‖ =
        ‖(2 : ℂ) *
          quasiLocalInfiniteLBitHeisenbergFlipPhase
            t x infiniteLBitAllFalse‖ := by
              congr 1
              ring
      _ = 2 := by
        rw [norm_mul,
          norm_quasiLocalInfiniteLBitHeisenbergFlipPhase]
        norm_num
  apply le_antisymm
  · simpa [C, t] using
      norm_quasiLocalInfiniteLBitFlipCommutator_le_two
        t x y quasiLocalInfiniteLBitUnitAmplitude
  · exact heval.symm.trans_le
      (ContinuousMap.norm_coe_le_norm C infiniteLBitAllFalse)

/-- The same fixed-time locality bound that permits all-pairs saturation
forces its explicit witness time to pay an exponentially growing
distance-dependent delay.  The division-free form avoids imposing any
separate positivity hypothesis on the global weighted mass. -/
theorem two_le_pairSaturationTime_mul_weightedInfluenceRate
    (x y : ℕ) :
    2 ≤
      quasiLocalInfiniteLBitPairSaturationTime x y *
        (4 * ((1 : ℝ) / 2) ^ Nat.dist x y *
          quasiLocalInfiniteLBitWeightedMass) := by
  have h :=
    norm_quasiLocalInfiniteLBitFlipCommutator_le
      (quasiLocalInfiniteLBitPairSaturationTime x y)
      x y quasiLocalInfiniteLBitUnitAmplitude
  rw [
    norm_quasiLocalInfiniteLBitFlipCommutator_pairSaturationTime,
    norm_quasiLocalInfiniteLBitUnitAmplitude,
    mul_one,
    abs_of_pos (quasiLocalInfiniteLBitPairSaturationTime_pos x y)
  ] at h
  exact h

/-- All-pairs saturation in existential form, including positive time and a
normalized amplitude. -/
theorem exists_quasiLocalInfiniteLBit_allPairsInfluenceSaturation
    (x y : ℕ) (_hxy : x ≠ y) :
    ∃ t : ℝ, ∃ ψ : ContinuousInfiniteLBitAmplitude,
      0 < t ∧ ‖ψ‖ = 1 ∧
        ‖quasiLocalInfiniteLBitFlipCommutator t x y ψ‖ = 2 := by
  exact
    ⟨quasiLocalInfiniteLBitPairSaturationTime x y,
      quasiLocalInfiniteLBitUnitAmplitude,
      quasiLocalInfiniteLBitPairSaturationTime_pos x y,
      norm_quasiLocalInfiniteLBitUnitAmplitude,
      norm_quasiLocalInfiniteLBitFlipCommutator_pairSaturationTime
        x y⟩

end

end GaloisForLFunctions.HTGeometry
