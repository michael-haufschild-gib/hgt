import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Weighted mixed norms on divisor coordinates

On finitely supported real prime coordinates, weights `w p > 0` give the weighted `L¹` and `L²`
norms and their sum.  Coordinate restriction — the divisor residue map on a cofinite arithmetic
open — deletes coordinates, so it decreases every one of them; extension by zero of an already
restricted vector changes nothing, so it preserves them.  Both maps therefore have operator norm
at most one, which is what makes the split divisor row strict in the mixed topology.

* `deningerWeightedL1`, `deningerWeightedL2Sq`, `deningerWeightedMix` are the three quantities.
* `deningerWeightedL1_filter_le`, `deningerWeightedL2Sq_filter_le`,
  `deningerWeightedMix_filter_le` are the contraction estimates.
* `deningerWeighted_filter_of_support` is the isometry of extension by zero.
-/

namespace RHTower

open Finset

section WeightedNorms

variable (w : ℕ → ℝ)

/-- The weighted `L¹` quantity of a finitely supported coordinate vector. -/
noncomputable def deningerWeightedL1 (x : ℕ →₀ ℝ) : ℝ :=
  ∑ p ∈ x.support, w p * |x p|

/-- The weighted `L²` quantity, squared. -/
noncomputable def deningerWeightedL2Sq (x : ℕ →₀ ℝ) : ℝ :=
  ∑ p ∈ x.support, w p * (x p) ^ 2

/-- The mixed weighted quantity `‖x‖₁ + ‖x‖₂`. -/
noncomputable def deningerWeightedMix (x : ℕ →₀ ℝ) : ℝ :=
  deningerWeightedL1 w x + Real.sqrt (deningerWeightedL2Sq w x)

variable {w}

theorem deningerWeightedL1_nonneg (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    0 ≤ deningerWeightedL1 w x :=
  Finset.sum_nonneg fun p _ => mul_nonneg (hw p) (abs_nonneg _)

theorem deningerWeightedL2Sq_nonneg (hw : ∀ p, 0 ≤ w p) (x : ℕ →₀ ℝ) :
    0 ≤ deningerWeightedL2Sq w x :=
  Finset.sum_nonneg fun p _ => mul_nonneg (hw p) (sq_nonneg _)

/-- Coordinate restriction to a set of primes. -/
noncomputable def deningerRestrictCoords (P : ℕ → Prop) [DecidablePred P] (x : ℕ →₀ ℝ) :
    ℕ →₀ ℝ := Finsupp.filter P x

@[simp] theorem deningerRestrictCoords_apply (P : ℕ → Prop) [DecidablePred P] (x : ℕ →₀ ℝ)
    (p : ℕ) : deningerRestrictCoords P x p = if P p then x p else 0 :=
  Finsupp.filter_apply P x p

theorem deningerRestrictCoords_support_subset (P : ℕ → Prop) [DecidablePred P] (x : ℕ →₀ ℝ) :
    (deningerRestrictCoords P x).support ⊆ x.support := by
  intro p hp
  rw [deningerRestrictCoords, Finsupp.support_filter] at hp
  exact (Finset.mem_filter.mp hp).1

/-- **Weighted `L¹` contraction.**  Deleting coordinates decreases the weighted `L¹`
quantity. -/
theorem deningerWeightedL1_filter_le (hw : ∀ p, 0 ≤ w p) (P : ℕ → Prop) [DecidablePred P]
    (x : ℕ →₀ ℝ) :
    deningerWeightedL1 w (deningerRestrictCoords P x) ≤ deningerWeightedL1 w x := by
  classical
  have hsub : (deningerRestrictCoords P x).support ⊆ x.support :=
    deningerRestrictCoords_support_subset P x
  have hterm : ∀ p ∈ (deningerRestrictCoords P x).support,
      w p * |deningerRestrictCoords P x p| = w p * |x p| := by
    intro p hp
    have hP : P p := by
      by_contra hnot
      exact (Finsupp.mem_support_iff.mp hp) (by simp [deningerRestrictCoords_apply, hnot])
    simp [deningerRestrictCoords_apply, hP]
  calc deningerWeightedL1 w (deningerRestrictCoords P x)
      = ∑ p ∈ (deningerRestrictCoords P x).support, w p * |x p| :=
        Finset.sum_congr rfl hterm
    _ ≤ ∑ p ∈ x.support, w p * |x p| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => mul_nonneg (hw p) (abs_nonneg _))
    _ = deningerWeightedL1 w x := rfl

/-- **Weighted `L²` contraction.** -/
theorem deningerWeightedL2Sq_filter_le (hw : ∀ p, 0 ≤ w p) (P : ℕ → Prop) [DecidablePred P]
    (x : ℕ →₀ ℝ) :
    deningerWeightedL2Sq w (deningerRestrictCoords P x) ≤ deningerWeightedL2Sq w x := by
  classical
  have hsub : (deningerRestrictCoords P x).support ⊆ x.support :=
    deningerRestrictCoords_support_subset P x
  have hterm : ∀ p ∈ (deningerRestrictCoords P x).support,
      w p * (deningerRestrictCoords P x p) ^ 2 = w p * (x p) ^ 2 := by
    intro p hp
    have hP : P p := by
      by_contra hnot
      exact (Finsupp.mem_support_iff.mp hp) (by simp [deningerRestrictCoords_apply, hnot])
    simp [deningerRestrictCoords_apply, hP]
  calc deningerWeightedL2Sq w (deningerRestrictCoords P x)
      = ∑ p ∈ (deningerRestrictCoords P x).support, w p * (x p) ^ 2 :=
        Finset.sum_congr rfl hterm
    _ ≤ ∑ p ∈ x.support, w p * (x p) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => mul_nonneg (hw p) (sq_nonneg _))
    _ = deningerWeightedL2Sq w x := rfl

/-- **Mixed contraction.**  The divisor residue map has mixed operator norm at most one. -/
theorem deningerWeightedMix_filter_le (hw : ∀ p, 0 ≤ w p) (P : ℕ → Prop) [DecidablePred P]
    (x : ℕ →₀ ℝ) :
    deningerWeightedMix w (deningerRestrictCoords P x) ≤ deningerWeightedMix w x := by
  refine add_le_add (deningerWeightedL1_filter_le hw P x) ?_
  exact Real.sqrt_le_sqrt (deningerWeightedL2Sq_filter_le hw P x)

/-- **Extension by zero is isometric.**  A vector already supported in `P` is unchanged by
restriction to `P`, so all three quantities agree. -/
theorem deningerWeighted_filter_of_support (P : ℕ → Prop) [DecidablePred P] {x : ℕ →₀ ℝ}
    (hx : ∀ p ∈ x.support, P p) :
    deningerRestrictCoords P x = x := by
  ext p
  by_cases hp : p ∈ x.support
  · simp [deningerRestrictCoords_apply, hx p hp]
  · simp [deningerRestrictCoords_apply, Finsupp.notMem_support_iff.mp hp]

/-- **The bounded splitting.**  Restriction to `P` and to its complement decompose a coordinate
vector, so the divisor row is split by coordinate maps. -/
theorem deningerRestrictCoords_add_compl (P : ℕ → Prop) [DecidablePred P] (x : ℕ →₀ ℝ) :
    deningerRestrictCoords P x + deningerRestrictCoords (fun p => ¬ P p) x = x := by
  ext p
  by_cases hp : P p <;> simp [deningerRestrictCoords_apply, hp]

/-- Restriction to `P` and to its complement are disjointly supported. -/
theorem deningerRestrictCoords_compl_apply_eq_zero (P : ℕ → Prop) [DecidablePred P]
    (x : ℕ →₀ ℝ) {p : ℕ} (hp : P p) :
    deningerRestrictCoords (fun q => ¬ P q) x p = 0 := by
  simp [deningerRestrictCoords_apply, hp]

/-- **Strictness of the splitting.**  Both components of the decomposition have mixed quantity at
most that of the vector, so the splitting maps are bounded by one and the split surjection is
open in the mixed topology. -/
theorem deningerWeightedMix_split_bounded (hw : ∀ p, 0 ≤ w p) (P : ℕ → Prop) [DecidablePred P]
    (x : ℕ →₀ ℝ) :
    deningerWeightedMix w (deningerRestrictCoords P x) ≤ deningerWeightedMix w x ∧
      deningerWeightedMix w (deningerRestrictCoords (fun p => ¬ P p) x)
        ≤ deningerWeightedMix w x :=
  ⟨deningerWeightedMix_filter_le hw P x, deningerWeightedMix_filter_le hw _ x⟩

end WeightedNorms

end RHTower
