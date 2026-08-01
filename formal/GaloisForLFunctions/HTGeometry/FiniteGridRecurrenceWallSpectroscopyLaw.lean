import GaloisForLFunctions.HTGeometry.ReplicaPhaseCyclingRecurrenceWallLaw
import Mathlib.Analysis.Fourier.ZMod

/-!
# Finite-grid recurrence-wall spectroscopy

Continuous Haar phase cycling is unnecessary for exact character recovery.
An `M`-point phase grid returns exactly the sum of all replica coefficients
whose integer characters agree modulo `M`. At replica order `n`, the grid
`M = 2n+1` is alias-free for every character in the full replica band, and
this grid size is worst-case sharp. Thus one recurrence wall of minimum
replica height `n` has an exact scalar readout using precisely
`(2n+1)^|I|` phase settings, with the same inverse-time sinc profile.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite-grid Fourier phase of one integer spectral character. -/
def finiteGridReplicaPhase
    {I : Type*} [Fintype I] (M : ℕ) [NeZero M]
    (k : I → ℤ) (x : I → ZMod M) : ℂ :=
  ∏ i, ZMod.stdAddChar ((k i : ZMod M) * x i)

theorem finiteGridReplicaPhase_add
    {I : Type*} [Fintype I] (M : ℕ) [NeZero M]
    (a b : I → ℤ) (x : I → ZMod M) :
    finiteGridReplicaPhase M (a + b) x =
      finiteGridReplicaPhase M a x * finiteGridReplicaPhase M b x := by
  unfold finiteGridReplicaPhase
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Pi.add_apply, Int.cast_add, add_mul, AddChar.map_add_eq_mul]

theorem finiteGridReplicaPhase_neg
    {I : Type*} [Fintype I] (M : ℕ) [NeZero M]
    (a : I → ℤ) (x : I → ZMod M) :
    finiteGridReplicaPhase M (-a) x =
      (finiteGridReplicaPhase M a x)⁻¹ := by
  simp only [finiteGridReplicaPhase, Pi.neg_apply, Int.cast_neg,
    neg_mul, AddChar.map_neg_eq_inv, Finset.prod_inv_distrib]

theorem replicaPhaseProduct_eq_finiteGridReplicaPhase
    {I : Type*} [Fintype I] (M : ℕ) [NeZero M]
    (p q : I → ℕ) (x : I → ZMod M) :
    (∏ i, ZMod.stdAddChar (x i) ^ p i) *
        (∏ i, ZMod.stdAddChar (-x i) ^ q i) =
      finiteGridReplicaPhase M (replicaMultiplicityCharacter p q) x := by
  rw [← Finset.prod_mul_distrib]
  unfold finiteGridReplicaPhase replicaMultiplicityCharacter
  apply Finset.prod_congr rfl
  intro i hi
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow,
    ← AddChar.map_add_eq_mul]
  congr 2
  push_cast
  simp only [nsmul_eq_mul, mul_neg]
  ring

/-- Product-grid Fourier orthogonality. -/
theorem finiteGridReplicaPhase_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (a : I → ℤ) :
    (∑ x : I → ZMod M, finiteGridReplicaPhase M a x) =
      if (∀ i, (a i : ZMod M) = 0) then
        (M : ℂ) ^ Fintype.card I else 0 := by
  classical
  unfold finiteGridReplicaPhase
  rw [show (∑ x : I → ZMod M,
      ∏ i, ZMod.stdAddChar ((a i : ZMod M) * x i)) =
      ∏ i, ∑ z : ZMod M, ZMod.stdAddChar ((a i : ZMod M) * z) by
        simpa using Finset.sum_prod_piFinset
          (Finset.univ : Finset (ZMod M))
          (fun i z => ZMod.stdAddChar ((a i : ZMod M) * z))]
  by_cases h : ∀ i, (a i : ZMod M) = 0
  · rw [if_pos h]
    simp_rw [h]
    simp
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact AddChar.sum_eq_zero_of_ne_one
      (ZMod.isPrimitive_stdAddChar M hi)

/-- Survival-fidelity replica on an exact finite spectral phase grid. -/
def finiteGridSurvivalFidelityReplica
    {I : Type*} [Fintype I] (M : ℕ) [NeZero M]
    (weight : I → ℝ) (n : ℕ) (x : I → ZMod M) : ℂ :=
  ((∑ i, (weight i : ℂ) * ZMod.stdAddChar (x i)) ^ n) *
    ((∑ i, (weight i : ℂ) * ZMod.stdAddChar (-x i)) ^ n)

theorem finiteGridSurvivalFidelityReplica_eq_characterExpansion
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (weight : I → ℝ) (n : ℕ)
    (x : I → ZMod M) :
    finiteGridSurvivalFidelityReplica M weight n x =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            finiteGridReplicaPhase M (replicaMultiplicityCharacter p q) x := by
  rw [finiteGridSurvivalFidelityReplica,
    complexFidelityReplicaMultiplicityExpansion]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [mul_assoc, replicaPhaseProduct_eq_finiteGridReplicaPhase]

/-- Exact alias-class coefficient selected by an `M`-point phase grid. -/
def finiteGridReplicaCharacterCoefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (weight : I → ℝ) (n : ℕ) (k : I → ℤ) : ℝ :=
  ∑ p ∈ Finset.univ.piAntidiag n,
    ∑ q ∈ Finset.univ.piAntidiag n,
      if ∀ i, (replicaMultiplicityCharacter p q i : ZMod M) = (k i : ZMod M)
      then fidelityReplicaMultiplicityWeight weight p q else 0

/-- Normalized exact finite-grid demodulation of one replica character. -/
def finiteGridReplicaCharacterReadout
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (weight : I → ℝ) (n : ℕ) (k : I → ℤ) : ℂ :=
  ((M : ℂ) ^ Fintype.card I)⁻¹ *
    ∑ x : I → ZMod M,
      finiteGridSurvivalFidelityReplica M weight n x *
        finiteGridReplicaPhase M (-k) x

/-- Every finite grid returns exactly its modular alias class. -/
theorem finiteGridReplicaCharacterReadout_eq_aliasCoefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (weight : I → ℝ) (n : ℕ) (k : I → ℤ) :
    finiteGridReplicaCharacterReadout M weight n k =
      finiteGridReplicaCharacterCoefficient M weight n k := by
  classical
  unfold finiteGridReplicaCharacterReadout
    finiteGridReplicaCharacterCoefficient
  simp_rw [finiteGridSurvivalFidelityReplica_eq_characterExpansion]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp_rw [mul_assoc, ← finiteGridReplicaPhase_add]
  rw [← Finset.mul_sum, finiteGridReplicaPhase_sum]
  by_cases hchar : ∀ i,
      (replicaMultiplicityCharacter p q i : ZMod M) = (k i : ZMod M)
  · rw [if_pos hchar]
    have hzero : ∀ i,
        (((replicaMultiplicityCharacter p q + -k) i : ℤ) : ZMod M) = 0 := by
      intro i
      simp only [Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg]
      rw [hchar i]
      exact add_neg_cancel _
    rw [if_pos hzero]
    have hM : (M : ℂ) ^ Fintype.card I ≠ 0 := by
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne M))
    field_simp
  · rw [if_neg hchar]
    have hnotzero : ¬ ∀ i,
        (((replicaMultiplicityCharacter p q + -k) i : ℤ) : ZMod M) = 0 := by
      intro hzero
      apply hchar
      intro i
      have hi := hzero i
      simp only [Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg] at hi
      exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hi)
    rw [if_neg hnotzero]
    simp

theorem abs_replicaMultiplicityCharacter_le_of_piAntidiag
    {I : Type*} [Fintype I] [DecidableEq I]
    {n : ℕ} {p q : I → ℕ}
    (hp : p ∈ Finset.univ.piAntidiag n)
    (hq : q ∈ Finset.univ.piAntidiag n) (i : I) :
    |replicaMultiplicityCharacter p q i| ≤ (n : ℤ) := by
  have hpSum := (Finset.mem_piAntidiag.mp hp).1
  have hqSum := (Finset.mem_piAntidiag.mp hq).1
  have hpi : p i ≤ n := by
    rw [← hpSum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hqi : q i ≤ n := by
    rw [← hqSum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold replicaMultiplicityCharacter
  rw [abs_le]
  constructor <;> omega

/-- Reduction modulo `2n+1` is injective on the full replica band. -/
theorem zmod_cast_injective_on_replica_band
    (n : ℕ) {a b : ℤ} (ha : |a| ≤ (n : ℤ)) (hb : |b| ≤ (n : ℤ))
    (hcast : (a : ZMod (2 * n + 1)) = (b : ZMod (2 * n + 1))) :
    a = b := by
  have hdiv : ((2 * n + 1 : ℕ) : ℤ) ∣ b - a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a b (2 * n + 1)).mp hcast
  have habs_le : |b - a| ≤ (2 * n : ℕ) := by
    have ha' := (abs_le.mp ha)
    have hb' := (abs_le.mp hb)
    rw [abs_sub_le_iff]
    constructor <;> norm_num <;> omega
  have habs_lt : |b - a| < ((2 * n + 1 : ℕ) : ℤ) := by
    calc
      |b - a| ≤ (2 * n : ℕ) := habs_le
      _ < ((2 * n + 1 : ℕ) : ℤ) := by omega
  have hzero : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hdiv habs_lt
  omega

theorem finiteGridReplicaCharacterCoefficient_eq_coefficient_of_bandlimited
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) (k : I → ℤ)
    (hk : ∀ i, |k i| ≤ (n : ℤ)) :
    finiteGridReplicaCharacterCoefficient (2 * n + 1) weight n k =
      fidelityReplicaCharacterCoefficient weight n k := by
  unfold finiteGridReplicaCharacterCoefficient
    fidelityReplicaCharacterCoefficient
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply propext
  constructor
  · intro hmod
    funext i
    exact zmod_cast_injective_on_replica_band n
      (abs_replicaMultiplicityCharacter_le_of_piAntidiag hp hq i)
      (hk i) (hmod i)
  · intro heq i
    rw [congrFun heq i]

instance phaseGridNeZero (n : ℕ) : NeZero (2 * n + 1) :=
  ⟨by omega⟩

/-- `2n+1` phase values recover every bandlimited order-`n` coefficient. -/
theorem finiteGridReplicaCharacterReadout_eq_coefficient_of_bandlimited
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) (k : I → ℤ)
    (hk : ∀ i, |k i| ≤ (n : ℤ)) :
    finiteGridReplicaCharacterReadout (2 * n + 1) weight n k =
      fidelityReplicaCharacterCoefficient weight n k := by
  rw [finiteGridReplicaCharacterReadout_eq_aliasCoefficient,
    finiteGridReplicaCharacterCoefficient_eq_coefficient_of_bandlimited weight n k hk]

theorem abs_character_le_of_replicaRealizes
    {I : Type*} [Fintype I] [DecidableEq I]
    {n : ℕ} {k : I → ℤ} (hreal : SpectralCharacterReplicaRealizes n k) :
    ∀ i, |k i| ≤ (n : ℤ) := by
  rcases hreal with ⟨p, q, hp, hq, hk⟩
  intro i
  have hpi : p i ≤ n := by
    rw [← hp]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hqi : q i ≤ n := by
    rw [← hq]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hk i, abs_le]
  constructor <;> omega

/-- Every projective character has an exact finite-grid readout at its
minimum replica height. -/
theorem finiteGridProjectiveCharacterReadout_at_exactHeight
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (k : ProjectiveCharacter I) :
    finiteGridReplicaCharacterReadout
        (2 * projectiveCharacterReplicaHeight k + 1) weight
        (projectiveCharacterReplicaHeight k)
        (finiteCharacterOfProjective k) =
      fidelityReplicaCharacterCoefficient weight
        (projectiveCharacterReplicaHeight k)
        (finiteCharacterOfProjective k) := by
  apply finiteGridReplicaCharacterReadout_eq_coefficient_of_bandlimited
  exact abs_character_le_of_replicaRealizes
    (spectralCharacterReplicaRealizes_positiveMass_of_balanced
      (projectiveCharacter_spectralCharacterBalanced k))

/-- Exact experimental phase-setting count. -/
theorem finiteGridSettingCount
    {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) :
    Fintype.card (I → ZMod (2 * n + 1)) =
      (2 * n + 1) ^ Fintype.card I := by
  rw [Fintype.card_fun]
  simp

/-- `2n+1` phase values are worst-case sharp for separating every integer
frequency in the replica band `[-n,n]`. Any smaller nonzero grid aliases two
distinct bandlimited characters. -/
theorem phaseGridNyquistSharp
    (n M : ℕ) [NeZero M] (hM : M ≤ 2 * n) :
    ∃ a b : ℤ,
      a ≠ b ∧ |a| ≤ (n : ℤ) ∧ |b| ≤ (n : ℤ) ∧
        (a : ZMod M) = (b : ZMod M) := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  refine ⟨-(n : ℤ), (M : ℤ) - n, ?_, ?_, ?_, ?_⟩
  · omega
  · simp
  · rw [abs_le]
    constructor <;> omega
  · rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    norm_num

/-- Exact finite-grid readout of one controlled recurrence wall. -/
def finiteGridControlledWallReadout
    {I X : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (weight : I → ℝ) (k : ProjectiveCharacter I)
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (T : ℝ) (x : X) : ℂ :=
  finiteGridReplicaCharacterReadout
      (2 * projectiveCharacterReplicaHeight k + 1) weight
      (projectiveCharacterReplicaHeight k)
      (finiteCharacterOfProjective k) *
    controlledRecurrenceWallReporter k energy response T x

theorem finiteGridControlledWallReadout_eq_resolvedSignal
    {I X : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (weight : I → ℝ) (k : ProjectiveCharacter I)
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (T : ℝ) (x : X) :
    finiteGridControlledWallReadout weight k energy response T x =
      resolvedControlledReplicaWallSignal weight
        (projectiveCharacterReplicaHeight k) k energy response T x := by
  rw [finiteGridControlledWallReadout,
    resolvedControlledReplicaWallSignal,
    finiteGridProjectiveCharacterReadout_at_exactHeight]

/-- Finite-grid wall spectroscopy retains the exact inverse-time sinc
profile and positive first detector coefficient. -/
theorem finiteGridControlledWallReadout_scaled_profile
    {I X : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (x₀ v : X) (T ξ : ℝ)
    (hwall : x₀ ∈ projectiveControlRecurrenceWall energy response k)
    (hT : T ≠ 0) :
    finiteGridControlledWallReadout weight k energy response T
        (x₀ + (ξ / T) • v) =
      (fidelityReplicaCharacterCoefficient weight
          (projectiveCharacterReplicaHeight k)
          (finiteCharacterOfProjective k) : ℂ) *
        Real.sinc (ξ * projectiveControlDetuning k response v) ∧
      0 < fidelityReplicaCharacterCoefficient weight
        (projectiveCharacterReplicaHeight k)
        (finiteCharacterOfProjective k) := by
  rw [finiteGridControlledWallReadout_eq_resolvedSignal]
  exact resolvedControlledReplicaWallSignal_scaled_profile_at_height
    hweight k energy response x₀ v T ξ hwall hT

end

end GaloisForLFunctions.HTGeometry
