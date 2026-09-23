import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Constitutive bi-formation interference

Independent pair formation and reciprocal Hadamard mixing generate an oriented mixed cubic
current. This module proves its exact finite fusion identity, reflection parity, neutral locus,
additive depth conservation, and global depth properness.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι]

/-- Third centered source cumulant in a finite packet. -/
def packetThirdCumulant (w x : ι → ℝ) : ℝ :=
  ∑ i, w i * x i ^ (3 : ℕ)

/-- Mixed cubic current produced by independent pair formation followed by reciprocal Hadamard
mixing. -/
def hadamardMixedThird (w x : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ i, ∑ j, (w i * w j) *
    (a * (x i + x j)) * (a * (x i - x j)) ^ (2 : ℕ)

private lemma sum_sum_scaled_product (c : ℝ) (f g : ι → ℝ) :
    (∑ i, ∑ j, c * f i * g j) = c * (∑ i, f i) * (∑ j, g j) := by
  calc
    (∑ i, ∑ j, c * f i * g j) = ∑ i, (c * f i) * (∑ j, g j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = (∑ i, c * f i) * (∑ j, g j) := by rw [Finset.sum_mul]
    _ = c * (∑ i, f i) * (∑ j, g j) := by
      have hc : (∑ i, c * f i) = c * (∑ i, f i) := by rw [Finset.mul_sum]
      rw [hc]

/-- Exact fusion identity before normalization or centering. -/
theorem hadamardMixedThird_general (w x : ι → ℝ) (a : ℝ) :
    hadamardMixedThird w x a =
      2 * a ^ (3 : ℕ) *
        ((∑ i, w i) * packetThirdCumulant w x -
          (∑ i, w i * x i) * (∑ i, w i * x i ^ (2 : ℕ))) := by
  classical
  unfold hadamardMixedThird packetThirdCumulant
  simp_rw [show ∀ i j, (w i * w j) * (a * (x i + x j)) *
      (a * (x i - x j)) ^ (2 : ℕ) =
      a ^ (3 : ℕ) * (w i * x i ^ (3 : ℕ)) * w j +
      a ^ (3 : ℕ) * w i * (w j * x j ^ (3 : ℕ)) -
      a ^ (3 : ℕ) * (w i * x i ^ (2 : ℕ)) * (w j * x j) -
      a ^ (3 : ℕ) * (w i * x i) * (w j * x j ^ (2 : ℕ)) by
    intro i j
    ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_sum_scaled_product (a ^ (3 : ℕ)) (fun i => w i * x i ^ (3 : ℕ)) w,
    sum_sum_scaled_product (a ^ (3 : ℕ)) w (fun j => w j * x j ^ (3 : ℕ)),
    sum_sum_scaled_product (a ^ (3 : ℕ)) (fun i => w i * x i ^ (2 : ℕ)) (fun j => w j * x j),
    sum_sum_scaled_product (a ^ (3 : ℕ)) (fun i => w i * x i) (fun j => w j * x j ^ (2 : ℕ))]
  ring

/-- For a normalized centered packet, bi-formation interference is exactly twice the scaled third
cumulant. -/
theorem hadamardMixedThird_eq
    (w x : ι → ℝ) (a : ℝ)
    (hmass : ∑ i, w i = 1)
    (hcenter : ∑ i, w i * x i = 0) :
    hadamardMixedThird w x a = 2 * a ^ (3 : ℕ) * packetThirdCumulant w x := by
  rw [hadamardMixedThird_general, hmass, hcenter]
  ring

/-- Reflection reverses the oriented mixed current without any normalization assumptions. -/
theorem hadamardMixedThird_neg (w x : ι → ℝ) (a : ℝ) :
    hadamardMixedThird w x (-a) = -hadamardMixedThird w x a := by
  rw [hadamardMixedThird_general, hadamardMixedThird_general]
  ring

/-- Positive scalarization is phase-blind: the squared current is reflection invariant. -/
theorem hadamardMixedThird_sq_neg (w x : ι → ℝ) (a : ℝ) :
    hadamardMixedThird w x (-a) ^ (2 : ℕ) = hadamardMixedThird w x a ^ (2 : ℕ) := by
  rw [hadamardMixedThird_neg]
  ring

/-- A nonzero source third cumulant makes zero scale the exact neutral locus. -/
theorem hadamardMixedThird_eq_zero_iff
    (w x : ι → ℝ) (a : ℝ)
    (hmass : ∑ i, w i = 1)
    (hcenter : ∑ i, w i * x i = 0)
    (hkappa : packetThirdCumulant w x ≠ 0) :
    hadamardMixedThird w x a = 0 ↔ a = 0 := by
  rw [hadamardMixedThird_eq w x a hmass hcenter]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hleft | hright
    · have ha3 : a ^ (3 : ℕ) = 0 := (mul_eq_zero.mp hleft).resolve_left (by norm_num)
      exact eq_zero_of_pow_eq_zero ha3
    · exact False.elim (hkappa hright)
  · rintro rfl
    norm_num

/-- Independent formation depth adds copies of the same generated current. -/
def hadamardDepthCurrent (w x : ι → ℝ) (a : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * hadamardMixedThird w x a

/-- Fusion conservation: independent depths add exactly. -/
theorem hadamardDepthCurrent_add
    (w x : ι → ℝ) (a : ℝ) (m n : ℕ) :
    hadamardDepthCurrent w x a (m + n) =
      hadamardDepthCurrent w x a m + hadamardDepthCurrent w x a n := by
  simp [hadamardDepthCurrent, Nat.cast_add]
  ring

/-- A scalar response multiplied by all natural depths is uniformly bounded exactly when it
vanishes. -/
theorem natDepth_bounded_iff_zero (c : ℝ) :
    (∃ C : ℝ, ∀ m : ℕ, |(m : ℝ) * c| ≤ C) ↔ c = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hc
    have hpos : 0 < |c| := abs_pos.mpr hc
    obtain ⟨m, hm⟩ := exists_nat_gt (C / |c|)
    have hstrict : C < (m : ℝ) * |c| := (div_lt_iff₀ hpos).mp hm
    have hbound := hC m
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)] at hbound
    exact (not_lt_of_ge hbound) hstrict
  · rintro rfl
    exact ⟨0, by intro m; simp⟩

/-- Exact global properness: if the source third cumulant survives, uniformly bounded formation
depth is equivalent to neutral scale. -/
theorem hadamardDepthCurrent_bounded_iff
    (w x : ι → ℝ) (a : ℝ)
    (hmass : ∑ i, w i = 1)
    (hcenter : ∑ i, w i * x i = 0)
    (hkappa : packetThirdCumulant w x ≠ 0) :
    (∃ C : ℝ, ∀ m : ℕ, |hadamardDepthCurrent w x a m| ≤ C) ↔ a = 0 := by
  rw [show (∃ C : ℝ, ∀ m : ℕ, |hadamardDepthCurrent w x a m| ≤ C) ↔
      hadamardMixedThird w x a = 0 by
    simpa [hadamardDepthCurrent] using natDepth_bounded_iff_zero (hadamardMixedThird w x a)]
  exact hadamardMixedThird_eq_zero_iff w x a hmass hcenter hkappa

/-- Closed finite capstone: fusion, conservation, coorientation loss, neutral-locus reconstruction,
and global formation properness hold simultaneously. -/
theorem biFormationInterference_capstone
    (w x : ι → ℝ) (a : ℝ)
    (hmass : ∑ i, w i = 1)
    (hcenter : ∑ i, w i * x i = 0)
    (hkappa : packetThirdCumulant w x ≠ 0) :
    hadamardMixedThird w x a = 2 * a ^ (3 : ℕ) * packetThirdCumulant w x ∧
      hadamardMixedThird w x (-a) = -hadamardMixedThird w x a ∧
      hadamardMixedThird w x (-a) ^ (2 : ℕ) = hadamardMixedThird w x a ^ (2 : ℕ) ∧
      (hadamardMixedThird w x a = 0 ↔ a = 0) ∧
      ((∃ C : ℝ, ∀ m : ℕ, |hadamardDepthCurrent w x a m| ≤ C) ↔ a = 0) := by
  exact ⟨hadamardMixedThird_eq w x a hmass hcenter,
    hadamardMixedThird_neg w x a,
    hadamardMixedThird_sq_neg w x a,
    hadamardMixedThird_eq_zero_iff w x a hmass hcenter hkappa,
    hadamardDepthCurrent_bounded_iff w x a hmass hcenter hkappa⟩

end GaloisForLFunctions.HTGeometry
