import GaloisForLFunctions.ArithmeticDefectRigidity.WhiteNoiseAndAntipodalEscapeData
import GaloisForLFunctions.ArithmeticOrientationTheory.TheObstructionCountIsTheCodimensionOfTheRepairingIdeal

/-!
# Cofactor contraction laws do not select finite Kronecker points

The augmentation character gives a positive rank-one Gram satisfying the
critical radius, all multiplicative packet contractions and numeric diagonal
order. Its Bohr point has a zero coordinate, so is outside every finite
half-plane point. This is an abstract model, with no actual-source realization asserted.
-/

section

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.ArithmeticOrientationTheory

/-- The character supported only at the multiplicative identity. -/
def augmentationBohrPoint : BohrPoint where
  ω n := if n = 1 then 1 else 0
  map_one := by simp
  map_mul m n := by
    have hmul : m * n = 1 ↔ m = 1 ∧ n = 1 := by
      constructor
      · intro h
        have hm : 1 ≤ m := by
          by_contra h'
          have hm0 : m = 0 := by omega
          simp only [hm0, zero_mul, zero_ne_one] at h
        have hn : 1 ≤ n := by
          by_contra h'
          have hn0 : n = 0 := by omega
          simp only [hn0, mul_zero, zero_ne_one] at h
        have hmle := Nat.mul_le_mul_left m hn
        have hnle := Nat.mul_le_mul_right n hm
        simp only [mul_one, one_mul, h] at hmle hnle
        exact ⟨le_antisymm hmle hm, le_antisymm hnle hn⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    by_cases hm : m = 1 <;> by_cases hn : n = 1 <;> simp [hmul, hm, hn]
  norm_le_one n := by split_ifs <;> norm_num

/-- Augmentation is outside every finite half-plane point, since its second coordinate vanishes. -/
theorem augmentationBohrPoint_ne_halfPlanePoint (σ : ℝ) (s : ℂ) (hs : σ ≤ s.re) :
    augmentationBohrPoint ≠ WienerAlgebraAt.halfPlanePoint σ s hs := by
  intro h
  have htwo := congrArg (fun ω : BohrPoint => ω.ω 2) h
  simp only [augmentationBohrPoint, WienerAlgebraAt.halfPlanePoint,
    show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 0 by decide, if_false] at htwo
  have hne : (2 : ℂ) ^ ((σ : ℂ) - s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => (by norm_num : (2 : ℂ) ≠ 0) h.1
  exact hne htwo.symm

/-- The augmentation character has exactly one algebraic quotient coordinate. -/
theorem augmentation_quotient_finrank :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
      RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) augmentationBohrPoint)) = 1 :=
  finrank_quotient_ker_bohrCharacter augmentationBohrPoint

end GaloisForLFunctions.ArithmeticOrientationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A rank-one real cofactor profile supported at the identity. -/
def augmentationCofactor (p : ℕ+) : ℝ := if p = 1 then 1 else 0

def augmentationKernel (j k : ℕ+) : ℝ := augmentationCofactor j * augmentationCofactor k

theorem augmentationCofactor_mul (p q : ℕ+) :
    augmentationCofactor (p * q) = augmentationCofactor p * augmentationCofactor q := by
  have hmul : p * q = 1 ↔ p = 1 ∧ q = 1 := by
    constructor
    · intro h
      have hnat := congrArg (fun n : ℕ+ => (n : ℕ)) h
      change (p : ℕ) * (q : ℕ) = 1 at hnat
      have hp : (p : ℕ) ≤ 1 :=
        (Nat.le_mul_of_pos_right (p : ℕ) q.property).trans_eq hnat
      have hq : (q : ℕ) ≤ 1 :=
        (Nat.le_mul_of_pos_left (q : ℕ) p.property).trans_eq hnat
      exact ⟨Subtype.ext (le_antisymm hp p.property), Subtype.ext (le_antisymm hq q.property)⟩
    · rintro ⟨rfl, rfl⟩
      exact one_mul _
  by_cases hp : p = 1 <;> by_cases hq : q = 1 <;>
    simp [augmentationCofactor, hmul, hp, hq]

theorem augmentationKernel_one_one : augmentationKernel 1 1 = 1 := by
  norm_num [augmentationKernel, augmentationCofactor]

theorem augmentationKernel_symm (j k : ℕ+) : augmentationKernel j k = augmentationKernel k j :=
  mul_comm _ _

theorem augmentationKernel_packet_eq (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * augmentationKernel j k) =
      (∑ j ∈ S, c j * augmentationCofactor j) ^ 2 := by
  rw [pow_two]
  simp only [sum_mul, mul_sum, augmentationKernel]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

theorem augmentationKernel_packet_nonneg (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * augmentationKernel j k := by
  rw [augmentationKernel_packet_eq]
  exact sq_nonneg _

/-- The augmentation Gram is positive and has only one feature coordinate. -/
theorem isPSDKernel_augmentation :
    HTGeometry.IsPSDKernel (fun j k => (augmentationKernel j k : ℂ)) :=
  HTGeometry.isPSDKernel_of_real_packet_nonneg augmentationKernel
    augmentationKernel_symm augmentationKernel_packet_nonneg

theorem abs_augmentationKernel_le (j k : ℕ+) :
    |augmentationKernel j k| ≤ cofactorGramRadius j k := by
  by_cases hj : j = 1 <;> by_cases hk : k = 1
  · subst j
    subst k
    norm_num [augmentationKernel, augmentationCofactor, cofactorGramRadius]
  all_goals
    simp only [augmentationKernel, augmentationCofactor, hj, hk,
      if_false, if_true, mul_zero, zero_mul, abs_zero]
    unfold cofactorGramRadius
    positivity

/-- Every nonidentity dilation kills the augmentation Gram, satisfying critical contraction. -/
theorem augmentationKernel_packet_dilation_le (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * augmentationKernel (p * j) (p * k)) ≤
      (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, c j * c k * augmentationKernel j k) := by
  by_cases hp : p = 1
  · subst p
    norm_num
  · have hzero (j : ℕ+) : augmentationCofactor (p * j) = 0 := by
      rw [augmentationCofactor_mul, augmentationCofactor, if_neg hp, zero_mul]
    have hlhs : (∑ j ∈ S, ∑ k ∈ S, c j * c k * augmentationKernel (p * j) (p * k)) = 0 := by
      simp only [augmentationKernel, hzero, mul_zero, sum_const_zero]
    rw [hlhs]
    exact mul_nonneg (by positivity) (augmentationKernel_packet_nonneg S c)

/-- The actual numeric-order constraint also holds for augmentation. -/
theorem augmentationKernel_scaled_diagonal_antitone :
    Antitone (fun p : ℕ+ => (p : ℝ) * augmentationKernel p p) := by
  intro p q hpq
  by_cases hq : q = 1
  · subst q
    have hp : p = 1 := le_antisymm hpq p.property
    subst p
    exact le_rfl
  · simp only [augmentationKernel, augmentationCofactor, if_neg hq,
      mul_zero]
    positivity

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.augmentationBohrPoint_ne_halfPlanePoint
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.augmentation_quotient_finrank
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.isPSDKernel_augmentation
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.abs_augmentationKernel_le
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.augmentationKernel_packet_dilation_le
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.augmentationKernel_scaled_diagonal_antitone
end
end

noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

/-- Augmentation evaluates a complete critical Wiener kernel at its first coefficient. -/
theorem bohrCharacter_augmentation_eq_coefficient_one (a : WienerAlgebraAt (1 / 2)) :
    WienerAlgebraAt.bohrCharacter (1 / 2) augmentationBohrPoint a = a.toFn 1 := by
  rw [bohrCharacter_apply]
  unfold bohrEval LSeries
  rw [tsum_eq_single 1]
  · simp [augmentationBohrPoint]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | h0
    · simp only [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero h0]
      simp only [augmentationBohrPoint, if_neg hn, mul_zero, zero_div]

/-- The point masses in the augmentation ideal force every nonidentity coordinate to zero. -/
theorem eq_augmentation_of_vanishes_ker (ω : BohrPoint)
    (hω : ∀ a ∈ RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) augmentationBohrPoint),
      bohrEval (1 / 2) a.toFn ω = 0) : ω = augmentationBohrPoint := by
  have hzero {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) : ω.ω n = 0 := by
    have ha : pointMass n ∈ RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) augmentationBohrPoint) := by
      rw [RingHom.mem_ker, bohrCharacter_pointMass _ hn0]
      simp only [augmentationBohrPoint, if_neg hn1, zero_div]
    have hz := hω (pointMass n) ha
    rw [toFn_pointMass, bohrEval_pointMass hn0] at hz
    have hden : (n : ℂ) ^ ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => hn0 (by exact_mod_cast h.1)
    have h := congrArg (fun z : ℂ => z * (n : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) hz
    simpa only [div_mul_cancel₀ _ hden, zero_mul] using h
  have htwo : ω.ω 2 = 0 := hzero (by decide) (by decide)
  have h0 : ω.ω 0 = 0 := by
    have h := ω.map_mul 0 2
    simpa only [zero_mul, htwo, mul_zero] using h
  have hfun : ω.ω = augmentationBohrPoint.ω := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn0
    · simpa only [augmentationBohrPoint, show (0 : ℕ) ≠ 1 by decide, if_false] using h0
    rcases eq_or_ne n 1 with rfl | hn1
    · simpa only [augmentationBohrPoint, if_true] using ω.map_one
    · simpa only [augmentationBohrPoint, if_neg hn1] using hzero hn0 hn1
  rcases ω with ⟨w, hw1, hwm, hwb⟩
  change w = augmentationBohrPoint.ω at hfun
  cases hfun
  rfl

/-- The complete augmentation ideal has precisely its augmentation Bohr point as hull. -/
theorem augmentation_character_hull_eq_singleton :
    {ω : BohrPoint | ∀ a ∈ RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) augmentationBohrPoint),
      bohrEval (1 / 2) a.toFn ω = 0} = {augmentationBohrPoint} := by
  apply Set.Subset.antisymm
  · intro ω hω
    exact Set.mem_singleton_iff.mpr (eq_augmentation_of_vanishes_ker ω hω)
  · intro ω hω
    rcases Set.mem_singleton_iff.mp hω with rfl
    intro a ha
    exact ha

end GaloisForLFunctions.ArithmeticOrientationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity
open ArithmeticOrientationTheory WienerAlgebraAt

/-- The scalar augmentation action has exactly the augmentation cofactor values. -/
theorem augmentationCharacter_pointMass (p : ℕ+) :
    WienerAlgebraAt.bohrCharacter (1 / 2) augmentationBohrPoint (pointMass (p : ℕ)) =
      (augmentationCofactor p : ℂ) := by
  rw [bohrCharacter_augmentation_eq_coefficient_one, toFn_pointMass, pointMassFn_apply]
  by_cases hp : p = 1
  · subst p
    norm_num [augmentationCofactor]
  · have hnat : (p : ℕ) ≠ 1 := fun h => hp (Subtype.ext h)
    simp only [show ¬ ((1 : ℕ) ≠ 0 ∧ 1 = (p : ℕ)) from fun h => hnat h.2.symm,
      if_false, augmentationCofactor, if_neg hp, Complex.ofReal_zero]

/-- The augmentation Gram is the scalar character Gram on the one-dimensional complex space. -/
theorem augmentationKernel_eq_characterGram (j k : ℕ+) :
    (augmentationKernel j k : ℂ) =
      (starRingEnd ℂ (WienerAlgebraAt.bohrCharacter (1 / 2) augmentationBohrPoint (pointMass (k : ℕ)))) *
        WienerAlgebraAt.bohrCharacter (1 / 2) augmentationBohrPoint (pointMass (j : ℕ)) := by
  rw [augmentationCharacter_pointMass, augmentationCharacter_pointMass,
    Complex.conj_ofReal]
  simp only [augmentationKernel, Complex.ofReal_mul]
  exact mul_comm _ _

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.bohrCharacter_augmentation_eq_coefficient_one
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.augmentation_character_hull_eq_singleton
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.augmentationKernel_eq_characterGram
end
