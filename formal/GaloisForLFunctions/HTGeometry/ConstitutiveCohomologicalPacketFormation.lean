import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Cohomological packet formation

This module formalizes a route-independent finite formation mechanism.  A source vector and a
marked unit vector generate their complete oriented pair-difference packet as one central
commutator in a two-step group.  Its positive work is exactly twice a weighted rank-two Gram
determinant; weighted mean plus packet reconstructs the source; reflection reverses the oriented
packet while preserving work.  Every homomorphism to a commutative reporter erases the packet,
which records the exact degree wall between additive reporting and central extension data.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Two-step formation group: horizontal laws together with ordered central pair packets. -/
@[ext]
structure CohomologicalPacketGroup (n : ℕ) where
  horizontal : Fin n → ℝ
  central : Fin n → Fin n → ℝ

namespace CohomologicalPacketGroup

variable {n : ℕ}

instance : Mul (CohomologicalPacketGroup n) where
  mul p q :=
    ⟨p.horizontal + q.horizontal,
      fun i j => p.central i j + q.central i j + p.horizontal i * q.horizontal j⟩

instance : One (CohomologicalPacketGroup n) where
  one := ⟨0, 0⟩

instance : Inv (CohomologicalPacketGroup n) where
  inv p :=
    ⟨-p.horizontal,
      fun i j => -p.central i j + p.horizontal i * p.horizontal j⟩

@[simp] theorem mul_horizontal (p q : CohomologicalPacketGroup n) (i : Fin n) :
    (p * q).horizontal i = p.horizontal i + q.horizontal i := rfl

@[simp] theorem mul_central (p q : CohomologicalPacketGroup n) (i j : Fin n) :
    (p * q).central i j =
      p.central i j + q.central i j + p.horizontal i * q.horizontal j := rfl

@[simp] theorem one_horizontal (i : Fin n) :
    (1 : CohomologicalPacketGroup n).horizontal i = 0 := rfl

@[simp] theorem one_central (i j : Fin n) :
    (1 : CohomologicalPacketGroup n).central i j = 0 := rfl

@[simp] theorem inv_horizontal (p : CohomologicalPacketGroup n) (i : Fin n) :
    p⁻¹.horizontal i = -p.horizontal i := rfl

@[simp] theorem inv_central (p : CohomologicalPacketGroup n) (i j : Fin n) :
    p⁻¹.central i j = -p.central i j + p.horizontal i * p.horizontal j := rfl

/-- Bilinearity of the outer-product carry is exactly associativity. -/
instance : Group (CohomologicalPacketGroup n) where
  mul_assoc p q r := by
    ext i j
    · simp only [mul_horizontal]
      ring
    · simp only [mul_central, mul_horizontal]
      ring
  one_mul p := by
    ext i j <;> simp
  mul_one p := by
    ext i j <;> simp
  inv_mul_cancel p := by
    ext i j
    · simp
    · simp

/-- Group commutator with convention `p q p⁻¹ q⁻¹`. -/
def packetCommutator (p q : CohomologicalPacketGroup n) :
    CohomologicalPacketGroup n :=
  p * q * p⁻¹ * q⁻¹

/-- Pure central packet. -/
def centralElement (z : Fin n → Fin n → ℝ) : CohomologicalPacketGroup n := ⟨0, z⟩

theorem centralElement_comm (z : Fin n → Fin n → ℝ)
    (p : CohomologicalPacketGroup n) :
    centralElement z * p = p * centralElement z := by
  ext i j
  · simp [centralElement]
  · simp [centralElement, add_comm]

@[simp] theorem packetCommutator_horizontal (p q : CohomologicalPacketGroup n)
    (i : Fin n) :
    (packetCommutator p q).horizontal i = 0 := by
  simp [packetCommutator]

@[simp] theorem packetCommutator_central (p q : CohomologicalPacketGroup n)
    (i j : Fin n) :
    (packetCommutator p q).central i j =
      p.horizontal i * q.horizontal j - q.horizontal i * p.horizontal j := by
  simp [packetCommutator]
  ring

/-- Every commutator is the antisymmetric outer-product packet, embedded centrally. -/
theorem packetCommutator_eq_centralElement (p q : CohomologicalPacketGroup n) :
    packetCommutator p q = centralElement fun i j =>
      p.horizontal i * q.horizontal j - q.horizontal i * p.horizontal j := by
  ext i j <;> simp [centralElement]

/-- Every commutative reporter erases the central packet. -/
theorem hom_to_commGroup_erases_packet
    {A : Type*} [CommGroup A] (f : CohomologicalPacketGroup n →* A)
    (p q : CohomologicalPacketGroup n) :
    f (packetCommutator p q) = 1 := by
  simp [packetCommutator, map_mul]

/-- Central coordinate is a degree-two reporter: outer product is its additive defect. -/
theorem central_coordinate_mul_defect (p q : CohomologicalPacketGroup n)
    (i j : Fin n) :
    (p * q).central i j - p.central i j - q.central i j =
      p.horizontal i * q.horizontal j := by
  simp
  ring

/-- Horizontal lift of a source vector. -/
def source (a : Fin n → ℝ) : CohomologicalPacketGroup n := ⟨a, 0⟩

/-- Marked constant-one horizontal lift. -/
def unitSource : CohomologicalPacketGroup n := ⟨1, 0⟩

/-- Complete oriented pair-difference packet. -/
def packetDifference (a : Fin n → ℝ) (i j : Fin n) : ℝ := a i - a j

/-- One commutator with the marked unit source is the complete pair packet. -/
theorem source_unitSource_commutator (a : Fin n → ℝ) (i j : Fin n) :
    (packetCommutator (source a) unitSource).central i j = packetDifference a i j := by
  simp [source, unitSource, packetDifference]

@[simp] theorem pow_horizontal (p : CohomologicalPacketGroup n) (m : ℕ) (i : Fin n) :
    (p ^ m).horizontal i = (m : ℝ) * p.horizontal i := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, mul_horizontal, ih]
      rw [Nat.cast_succ]
      ring

@[simp] theorem zpow_horizontal (p : CohomologicalPacketGroup n) (m : ℤ) (i : Fin n) :
    (p ^ m).horizontal i = (m : ℝ) * p.horizontal i := by
  cases m with
  | ofNat m => exact pow_horizontal p m i
  | negSucc m =>
      simp only [zpow_negSucc, inv_horizontal, pow_horizontal]
      rw [Int.cast_negSucc]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- Natural-power history multiplies central packet charge bilinearly. -/
theorem source_unitSource_pow_commutator
    (a : Fin n → ℝ) (m k : ℕ) (i j : Fin n) :
    (packetCommutator ((source a) ^ m) (unitSource ^ k)).central i j =
      (m : ℝ) * (k : ℝ) * packetDifference a i j := by
  rw [packetCommutator_central]
  simp only [pow_horizontal, source, unitSource, Pi.one_apply]
  unfold packetDifference
  ring

/-- Integer-power history multiplies central packet charge bilinearly. -/
theorem source_unitSource_zpow_commutator
    (a : Fin n → ℝ) (m k : ℤ) (i j : Fin n) :
    (packetCommutator ((source a) ^ m) (unitSource ^ k)).central i j =
      (m : ℝ) * (k : ℝ) * packetDifference a i j := by
  rw [packetCommutator_central]
  simp only [zpow_horizontal, source, unitSource, Pi.one_apply]
  unfold packetDifference
  ring

end CohomologicalPacketGroup

open Finset

/-- Total packet weight. -/
def cohomologicalPacketMass {n : ℕ} (μ : Fin n → ℝ) : ℝ := ∑ i, μ i

/-- Unnormalized weighted mean numerator. -/
def cohomologicalPacketMoment {n : ℕ} (μ a : Fin n → ℝ) : ℝ :=
  ∑ i, μ i * a i

/-- Weighted second moment. -/
def cohomologicalPacketSecondMoment {n : ℕ} (μ a : Fin n → ℝ) : ℝ :=
  ∑ i, μ i * a i ^ 2

/-- Positive work of the complete ordered pair packet. -/
def cohomologicalPacketEnergy {n : ℕ} (μ a : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, μ i * μ j * (a i - a j) ^ 2

theorem cohomologicalPacketEnergy_nonneg
    {n : ℕ} (μ a : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    0 ≤ cohomologicalPacketEnergy μ a := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (hμ i) (hμ j)) (sq_nonneg _)

/-- Under strictly positive weights, zero work is exactly the constant-source sector. -/
theorem cohomologicalPacketEnergy_eq_zero_iff_constant
    {n : ℕ} (μ a : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) :
    cohomologicalPacketEnergy μ a = 0 ↔ ∀ i j, a i = a j := by
  constructor
  · intro hE i j
    have hrow_nonneg : ∀ k ∈ Finset.univ,
        0 ≤ ∑ l, μ k * μ l * (a k - a l) ^ 2 := by
      intro k _
      apply Finset.sum_nonneg
      intro l _
      exact mul_nonneg (mul_nonneg (hμ k).le (hμ l).le) (sq_nonneg _)
    have hrow :=
      (Finset.sum_eq_zero_iff_of_nonneg hrow_nonneg).mp hE i (Finset.mem_univ i)
    have hterm_nonneg : ∀ l ∈ Finset.univ,
        0 ≤ μ i * μ l * (a i - a l) ^ 2 := by
      intro l _
      exact mul_nonneg (mul_nonneg (hμ i).le (hμ l).le) (sq_nonneg _)
    have hterm :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hrow j (Finset.mem_univ j)
    have hweights : μ i * μ j ≠ 0 :=
      mul_ne_zero (ne_of_gt (hμ i)) (ne_of_gt (hμ j))
    have hsquare : (a i - a j) ^ 2 = 0 :=
      (mul_eq_zero.mp hterm).resolve_left hweights
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro hconstant
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    simp [hconstant i j]

/-- Central-work/Plücker conservation: pair work is twice the weighted rank-two Gram determinant. -/
theorem cohomologicalPacketEnergy_eq_two_mul_gram
    {n : ℕ} (μ a : Fin n → ℝ) :
    cohomologicalPacketEnergy μ a =
      2 * (cohomologicalPacketMass μ * cohomologicalPacketSecondMoment μ a -
        cohomologicalPacketMoment μ a ^ 2) := by
  have hleft :
      (∑ i, ∑ j, μ i * μ j * a i ^ 2) =
        cohomologicalPacketSecondMoment μ a * cohomologicalPacketMass μ := by
    simp only [cohomologicalPacketSecondMoment, cohomologicalPacketMass]
    calc
      (∑ i, ∑ j, μ i * μ j * a i ^ 2) =
          ∑ i, (μ i * a i ^ 2) * ∑ j, μ j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ i, μ i * a i ^ 2) * ∑ j, μ j := by
            rw [Finset.sum_mul]
  have hright :
      (∑ i, ∑ j, μ i * μ j * a j ^ 2) =
        cohomologicalPacketMass μ * cohomologicalPacketSecondMoment μ a := by
    simp only [cohomologicalPacketSecondMoment, cohomologicalPacketMass]
    calc
      (∑ i, ∑ j, μ i * μ j * a j ^ 2) =
          ∑ i, μ i * ∑ j, μ j * a j ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ i, μ i) * ∑ j, μ j * a j ^ 2 := by
            rw [Finset.sum_mul]
  have hcross :
      (∑ i, ∑ j, (μ i * a i) * (μ j * a j)) =
        cohomologicalPacketMoment μ a ^ 2 := by
    simp only [cohomologicalPacketMoment, pow_two]
    calc
      (∑ i, ∑ j, (μ i * a i) * (μ j * a j)) =
          ∑ i, (μ i * a i) * ∑ j, μ j * a j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = (∑ i, μ i * a i) * ∑ j, μ j * a j := by
            rw [Finset.sum_mul]
  rw [show cohomologicalPacketEnergy μ a =
      ∑ i, ∑ j,
        (μ i * μ j * a i ^ 2 + μ i * μ j * a j ^ 2 -
          2 * ((μ i * a i) * (μ j * a j))) by
    simp only [cohomologicalPacketEnergy]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [show (∑ i, ∑ j,
      (μ i * μ j * a i ^ 2 + μ i * μ j * a j ^ 2 -
        2 * ((μ i * a i) * (μ j * a j)))) =
      (∑ i, ∑ j, μ i * μ j * a i ^ 2) +
      (∑ i, ∑ j, μ i * μ j * a j ^ 2) -
      2 * (∑ i, ∑ j, (μ i * a i) * (μ j * a j)) by
    simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]]
  rw [hleft, hright, hcross]
  ring

/-- Denominator-free joint reconstruction identity. -/
theorem cohomologicalPacket_reconstruction_numerator
    {n : ℕ} (μ a : Fin n → ℝ) (i : Fin n) :
    cohomologicalPacketMass μ * a i = cohomologicalPacketMoment μ a +
      ∑ j, μ j * (a i - a j) := by
  simp only [cohomologicalPacketMass, cohomologicalPacketMoment]
  calc
    (∑ j, μ j) * a i = ∑ j, μ j * a i := by rw [Finset.sum_mul]
    _ = ∑ j, (μ j * a j + μ j * (a i - a j)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ j, μ j * a j) + ∑ j, μ j * (a i - a j) := by
      rw [Finset.sum_add_distrib]

/-- Weighted mean plus central packet reconstructs every source coordinate. -/
theorem cohomologicalPacket_reconstruction
    {n : ℕ} (μ a : Fin n → ℝ) (i : Fin n) (hM : cohomologicalPacketMass μ ≠ 0) :
    a i = cohomologicalPacketMoment μ a / cohomologicalPacketMass μ +
      (1 / cohomologicalPacketMass μ) * ∑ j, μ j * (a i - a j) := by
  field_simp
  simpa [mul_comm] using cohomologicalPacket_reconstruction_numerator μ a i

/-- Affine reflection of a source vector. -/
def cohomologicalPacketReflect {n : ℕ} (c : ℝ) (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => c - a i

/-- Reflection reverses every oriented central-packet coordinate. -/
theorem cohomologicalPacketDifference_reflect
    {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (i j : Fin n) :
    CohomologicalPacketGroup.packetDifference (cohomologicalPacketReflect c a) i j =
      -CohomologicalPacketGroup.packetDifference a i j := by
  simp [CohomologicalPacketGroup.packetDifference, cohomologicalPacketReflect]

/-- Positive work is information-neutral under affine reflection. -/
theorem cohomologicalPacketEnergy_reflect {n : ℕ} (μ a : Fin n → ℝ) (c : ℝ) :
    cohomologicalPacketEnergy μ (cohomologicalPacketReflect c a) =
      cohomologicalPacketEnergy μ a := by
  simp only [cohomologicalPacketEnergy, cohomologicalPacketReflect]
  congr 1
  funext i
  congr 1
  funext j
  ring

end GaloisForLFunctions.HTGeometry
