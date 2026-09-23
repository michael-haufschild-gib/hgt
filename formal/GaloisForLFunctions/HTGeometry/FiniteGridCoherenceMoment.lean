import GaloisForLFunctions.HTGeometry.FiniteGridRecurrenceWallSpectroscopyLaw

open scoped BigOperators ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem zmod_cast_injective_on_replica_band_of_two_mul_lt
    (n M : ℕ) (hM : 2 * n < M) {a b : ℤ}
    (ha : |a| ≤ (n : ℤ)) (hb : |b| ≤ (n : ℤ))
    (hcast : (a : ZMod M) = (b : ZMod M)) : a = b := by
  have hdiv : (M : ℤ) ∣ b - a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a b M).mp hcast
  have habs_le : |b - a| ≤ (2 * n : ℕ) := by
    have ha' := abs_le.mp ha
    have hb' := abs_le.mp hb
    rw [abs_sub_le_iff]
    constructor <;> norm_num <;> omega
  have habs_lt : |b - a| < (M : ℤ) := by
    exact lt_of_le_of_lt habs_le (by exact_mod_cast hM)
  have hzero : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hdiv habs_lt
  omega

theorem finiteGridReplicaCharacterCoefficient_eq_coefficient_of_two_mul_lt
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (weight : I → ℝ) (n : ℕ) (hM : 2 * n < M)
    (k : I → ℤ) (hk : ∀ i, |k i| ≤ (n : ℤ)) :
    finiteGridReplicaCharacterCoefficient M weight n k =
      fidelityReplicaCharacterCoefficient weight n k := by
  unfold finiteGridReplicaCharacterCoefficient fidelityReplicaCharacterCoefficient
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply propext
  constructor
  · intro hmod
    funext i
    exact zmod_cast_injective_on_replica_band_of_two_mul_lt n M hM
      (abs_replicaMultiplicityCharacter_le_of_piAntidiag hp hq i)
      (hk i) (hmod i)
  · intro heq i
    rw [congrFun heq i]

theorem finiteGridReplicaCharacterReadout_eq_coefficient_of_two_mul_lt
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (weight : I → ℝ) (n : ℕ) (hM : 2 * n < M)
    (k : I → ℤ) (hk : ∀ i, |k i| ≤ (n : ℤ)) :
    finiteGridReplicaCharacterReadout M weight n k =
      fidelityReplicaCharacterCoefficient weight n k := by
  rw [finiteGridReplicaCharacterReadout_eq_aliasCoefficient,
    finiteGridReplicaCharacterCoefficient_eq_coefficient_of_two_mul_lt
      M weight n hM k hk]

theorem replicaMultiplicityCharacter_eq_zero_iff
    {I : Type*} (p q : I → ℕ) :
    replicaMultiplicityCharacter p q = 0 ↔ p = q := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp only [replicaMultiplicityCharacter, Pi.zero_apply, sub_eq_zero] at hi
    exact_mod_cast hi
  · intro h
    subst q
    funext i
    simp [replicaMultiplicityCharacter]

theorem fidelityReplicaCharacterCoefficient_zero_eq_permutationFloor
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) :
    fidelityReplicaCharacterCoefficient weight n (0 : I → ℤ) =
      fidelityReplicaPermutationFloor weight n := by
  unfold fidelityReplicaCharacterCoefficient fidelityReplicaPermutationFloor
  apply Finset.sum_congr rfl
  intro p hp
  simp_rw [replicaMultiplicityCharacter_eq_zero_iff]
  simp [hp]

theorem finiteGridSurvivalFidelityReplica_eq_norm_pow
    {I : Type*} [Fintype I]
    (M : ℕ) [NeZero M] (weight : I → ℝ) (n : ℕ)
    (x : I → ZMod M) :
    finiteGridSurvivalFidelityReplica M weight n x =
      (‖∑ i, (weight i : ℂ) * ZMod.stdAddChar (x i)‖ ^ (2 * n) : ℂ) := by
  unfold finiteGridSurvivalFidelityReplica
  have hconj :
      (∑ i, (weight i : ℂ) * ZMod.stdAddChar (-x i)) =
        starRingEnd ℂ (∑ i, (weight i : ℂ) * ZMod.stdAddChar (x i)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul]
    simp [AddChar.map_neg_eq_conj]
  rw [hconj]
  let z : ℂ := ∑ i, (weight i : ℂ) * ZMod.stdAddChar (x i)
  change z ^ n * (starRingEnd ℂ z) ^ n = (‖z‖ ^ (2 * n) : ℂ)
  rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem finiteGrid_norm_moment_eq_permutationFloor
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (weight : I → ℝ) (n : ℕ) (hM : 2 * n < M) :
    (∑ x : I → ZMod M,
        ‖∑ i, (weight i : ℂ) * ZMod.stdAddChar (x i)‖ ^ (2 * n)) =
      M ^ Fintype.card I * fidelityReplicaPermutationFloor weight n := by
  have hread := finiteGridReplicaCharacterReadout_eq_coefficient_of_two_mul_lt
    M weight n hM (0 : I → ℤ) (by simp)
  rw [finiteGridReplicaCharacterReadout] at hread
  simp only [finiteGridReplicaPhase, Pi.neg_apply, Pi.zero_apply, neg_zero,
    Int.cast_zero, zero_mul] at hread
  have hnat : M ≠ 0 := NeZero.ne M
  have hnonzero : ((M : ℂ) ^ Fintype.card I) ≠ 0 := by
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hnat)
  have hsum :
      ∑ x : I → ZMod M, finiteGridSurvivalFidelityReplica M weight n x =
        ((M : ℂ) ^ Fintype.card I) *
          fidelityReplicaCharacterCoefficient weight n (0 : I → ℤ) := by
    apply (inv_mul_eq_iff_eq_mul₀ hnonzero).mp
    simpa using hread
  rw [fidelityReplicaCharacterCoefficient_zero_eq_permutationFloor] at hsum
  have hsumReal := congrArg Complex.re hsum
  norm_num only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hsumReal
  have hscalarRe : ((M : ℂ) ^ Fintype.card I).re =
      (M : ℝ) ^ Fintype.card I := by
    induction Fintype.card I with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, pow_succ, Complex.mul_re, ih]
        norm_num
  have hscalarIm : ((M : ℂ) ^ Fintype.card I).im = 0 := by
    induction Fintype.card I with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Complex.mul_im, ih]
        norm_num
  rw [hscalarRe, hscalarIm] at hsumReal
  simp only [zero_mul, sub_zero] at hsumReal
  rw [← hsumReal]
  have hsumRe :
      (∑ x : I → ZMod M, finiteGridSurvivalFidelityReplica M weight n x).re =
        ∑ x : I → ZMod M,
          (finiteGridSurvivalFidelityReplica M weight n x).re := by
    simpa only [Complex.reCLM_apply] using
      map_sum (g := Complex.reCLM)
        (f := fun x : I → ZMod M =>
          finiteGridSurvivalFidelityReplica M weight n x)
        (s := Finset.univ)
  rw [hsumRe]
  apply Finset.sum_congr rfl
  intro x _
  have hx := congrArg Complex.re
    (finiteGridSurvivalFidelityReplica_eq_norm_pow M weight n x)
  let z : ℂ := ∑ i, (weight i : ℂ) * ZMod.stdAddChar (x i)
  have hreal : ((‖z‖ : ℂ) ^ (2 * n)).re = ‖z‖ ^ (2 * n) := by
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  exact hreal.symm.trans hx.symm

/-- Phase-grid points whose weighted coherence reaches `threshold`. -/
def finiteGridCoherenceCap
    {I : Type*} [Fintype I] [DecidableEq I] (M : ℕ) [NeZero M]
    (weight : I → ℝ) (threshold : ℝ) : Finset (I → ZMod M) :=
  Finset.univ.filter fun x =>
    threshold ≤ ‖∑ i, (weight i : ℂ) * ZMod.stdAddChar (x i)‖

theorem finiteGridCoherenceCap_card_mul_pow_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (weight : I → ℝ) (n : ℕ) (hM : 2 * n < M)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    ((finiteGridCoherenceCap M weight threshold).card : ℝ) *
        threshold ^ (2 * n) ≤
      (M : ℝ) ^ Fintype.card I *
        fidelityReplicaPermutationFloor weight n := by
  rw [← finiteGrid_norm_moment_eq_permutationFloor M weight n hM]
  calc
    ((finiteGridCoherenceCap M weight threshold).card : ℝ) *
          threshold ^ (2 * n) =
        ∑ _x ∈ finiteGridCoherenceCap M weight threshold,
          threshold ^ (2 * n) := by simp
    _ ≤ ∑ x ∈ finiteGridCoherenceCap M weight threshold,
        ‖∑ i, (weight i : ℂ) * ZMod.stdAddChar (x i)‖ ^ (2 * n) := by
      apply Finset.sum_le_sum
      intro x hx
      exact pow_le_pow_left₀ hthreshold
        (by simpa [finiteGridCoherenceCap] using hx) _
    _ ≤ ∑ x : I → ZMod M,
        ‖∑ i, (weight i : ℂ) * ZMod.stdAddChar (x i)‖ ^ (2 * n) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro x _ _
      positivity

theorem fidelityReplicaPermutationFloor_le_factorial_mul_sqMoment
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 ≤ weight i) (n : ℕ) :
    fidelityReplicaPermutationFloor weight n ≤
      (n.factorial : ℝ) * (∑ i, weight i ^ (2 : ℕ)) ^ n := by
  unfold fidelityReplicaPermutationFloor
  calc
    (∑ p ∈ Finset.univ.piAntidiag n,
        fidelityReplicaMultiplicityWeight weight p p) ≤
      ∑ p ∈ Finset.univ.piAntidiag n,
        (n.factorial : ℝ) * (Nat.multinomial Finset.univ p : ℝ) *
          ∏ i, (weight i ^ (2 : ℕ)) ^ p i := by
      apply Finset.sum_le_sum
      intro p hp
      have hpSum := (Finset.mem_piAntidiag.mp hp).1
      have hmultiNat : Nat.multinomial Finset.univ p ≤ n.factorial := by
        unfold Nat.multinomial
        rw [hpSum]
        exact Nat.div_le_self _ _
      have hmulti : (Nat.multinomial Finset.univ p : ℝ) ≤ n.factorial := by
        exact_mod_cast hmultiNat
      have hMnonneg : 0 ≤ (Nat.multinomial Finset.univ p : ℝ) := by positivity
      have hPnonneg : 0 ≤ ∏ i, weight i ^ p i :=
        Finset.prod_nonneg fun i _ => pow_nonneg (hweight i) _
      unfold fidelityReplicaMultiplicityWeight
      have hMM :
          (Nat.multinomial Finset.univ p : ℝ) *
              (Nat.multinomial Finset.univ p : ℝ) ≤
            (n.factorial : ℝ) *
              (Nat.multinomial Finset.univ p : ℝ) :=
        mul_le_mul_of_nonneg_right hmulti hMnonneg
      calc
        (Nat.multinomial Finset.univ p : ℝ) *
              (∏ i, weight i ^ p i) *
              (Nat.multinomial Finset.univ p : ℝ) *
                (∏ i, weight i ^ p i) =
            ((Nat.multinomial Finset.univ p : ℝ) *
              (Nat.multinomial Finset.univ p : ℝ)) *
              ((∏ i, weight i ^ p i) * (∏ i, weight i ^ p i)) := by ring
        _ ≤ ((n.factorial : ℝ) *
              (Nat.multinomial Finset.univ p : ℝ)) *
              ((∏ i, weight i ^ p i) * (∏ i, weight i ^ p i)) :=
            mul_le_mul_of_nonneg_right hMM (mul_nonneg hPnonneg hPnonneg)
        _ = (n.factorial : ℝ) *
              (Nat.multinomial Finset.univ p : ℝ) *
                ∏ i, (weight i ^ (2 : ℕ)) ^ p i := by
            simp only [pow_two, mul_pow, Finset.prod_mul_distrib]
    _ = (n.factorial : ℝ) *
        ∑ p ∈ Finset.univ.piAntidiag n,
          (Nat.multinomial Finset.univ p : ℝ) *
            ∏ i, (weight i ^ (2 : ℕ)) ^ p i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (n.factorial : ℝ) * (∑ i, weight i ^ (2 : ℕ)) ^ n := by
      rw [Finset.sum_pow_eq_sum_piAntidiag]

theorem finiteGridCoherenceCap_card_mul_pow_le_factorial
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] {weight : I → ℝ} (hweight : ∀ i, 0 ≤ weight i)
    (n : ℕ) (hM : 2 * n < M) (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    ((finiteGridCoherenceCap M weight threshold).card : ℝ) *
        threshold ^ (2 * n) ≤
      (M : ℝ) ^ Fintype.card I * (n.factorial : ℝ) *
        (∑ i, weight i ^ (2 : ℕ)) ^ n := by
  calc
    _ ≤ (M : ℝ) ^ Fintype.card I *
        fidelityReplicaPermutationFloor weight n :=
      finiteGridCoherenceCap_card_mul_pow_le M weight n hM threshold hthreshold
    _ ≤ (M : ℝ) ^ Fintype.card I *
        ((n.factorial : ℝ) * (∑ i, weight i ^ (2 : ℕ)) ^ n) := by
      exact mul_le_mul_of_nonneg_left
        (fidelityReplicaPermutationFloor_le_factorial_mul_sqMoment hweight n)
        (by positivity)
    _ = _ := by ring

/-- Translation by one phase-grid point. -/
def finiteGridTranslationEquiv
    {I : Type*} (M : ℕ) (center : I → ZMod M) :
    (I → ZMod M) ≃ (I → ZMod M) where
  toFun x := x + center
  invFun x := x - center
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

/-- A coherence cap translated to a supplied phase-grid target. -/
def finiteGridTranslatedCoherenceCap
    {I : Type*} [Fintype I] [DecidableEq I] (M : ℕ) [NeZero M]
    (weight : I → ℝ) (threshold : ℝ) (center : I → ZMod M) :
    Finset (I → ZMod M) :=
  (finiteGridCoherenceCap M weight threshold).map
    (finiteGridTranslationEquiv M center).toEmbedding

/-- Membership in a translated cap is exactly large relative phase
coherence with its center. -/
theorem mem_finiteGridTranslatedCoherenceCap_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) [NeZero M] (weight : I → ℝ) (threshold : ℝ)
    (center x : I → ZMod M) :
    x ∈ finiteGridTranslatedCoherenceCap M weight threshold center ↔
      threshold ≤
        ‖∑ i, (weight i : ℂ) * ZMod.stdAddChar (x i - center i)‖ := by
  simp [finiteGridTranslatedCoherenceCap, finiteGridCoherenceCap,
    finiteGridTranslationEquiv]

theorem finiteGridTranslatedCoherenceCap_card
    {I : Type*} [Fintype I] [DecidableEq I] (M : ℕ) [NeZero M]
    (weight : I → ℝ) (threshold : ℝ) (center : I → ZMod M) :
    (finiteGridTranslatedCoherenceCap M weight threshold center).card =
      (finiteGridCoherenceCap M weight threshold).card := by
  exact Finset.card_map _

/-- Union of translated caps captured by a finite phase dictionary. -/
def finiteGridTargetCaptureSet
    {I Y : Type*} [Fintype I] [DecidableEq I] [Fintype Y]
    (M : ℕ) [NeZero M]
    (weight : I → ℝ) (threshold : ℝ) (target : Y → I → ZMod M) :
    Finset (I → ZMod M) :=
  Finset.univ.biUnion fun y =>
    finiteGridTranslatedCoherenceCap M weight threshold (target y)

theorem finiteGridTargetCaptureSet_card_le
    {I Y : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
    (M : ℕ) [NeZero M] (weight : I → ℝ) (threshold : ℝ)
    (target : Y → I → ZMod M) :
    (finiteGridTargetCaptureSet M weight threshold target).card ≤
      Fintype.card Y * (finiteGridCoherenceCap M weight threshold).card := by
  unfold finiteGridTargetCaptureSet
  calc
    _ ≤ ∑ y ∈ Finset.univ,
        (finiteGridTranslatedCoherenceCap M weight threshold (target y)).card :=
      Finset.card_biUnion_le
    _ = ∑ _y ∈ Finset.univ,
        (finiteGridCoherenceCap M weight threshold).card := by
      apply Finset.sum_congr rfl
      intro y _
      exact finiteGridTranslatedCoherenceCap_card M weight threshold (target y)
    _ = Fintype.card Y *
        (finiteGridCoherenceCap M weight threshold).card := by simp

end GaloisForLFunctions.HTGeometry
