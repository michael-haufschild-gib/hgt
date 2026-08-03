import Mathlib

/-!
# Stokes energy from positive rooted cuts

This file proves the algebraic core of the Stokes energy-tree law.  Positive cuts with all pendant
cuts give a squared Euclidean path metric of strict negative type.  A rooted idempotent cut system
defines complementary contacts, and polarization recovers that cut metric exactly.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

variable {n m : ℕ}

/-- Product of two finite sums as a double sum. -/
theorem double_sum_mul {a b : ℕ} (f : Fin a → ℝ) (g : Fin b → ℝ) :
    (∑ i, ∑ j, f i * g j) = (∑ i, f i) * (∑ j, g j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- Pairwise squared-difference identity underlying conditional negative definiteness. -/
theorem pair_square_sum_identity (x s : Fin n → ℝ) :
    (∑ i, ∑ j, x i * x j * (s i - s j) ^ 2) =
      2 * (∑ i, x i) * (∑ i, x i * (s i) ^ 2) -
        2 * (∑ i, x i * s i) ^ 2 := by
  calc
    (∑ i, ∑ j, x i * x j * (s i - s j) ^ 2) =
        ∑ i, ∑ j, (x i * x j * s i ^ 2 -
          2 * (x i * s i) * (x j * s j) + x i * x j * s j ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (∑ i, x i * s i ^ 2) * (∑ j, x j) -
          2 * ((∑ i, x i * s i) * (∑ j, x j * s j)) +
          (∑ i, x i) * (∑ j, x j * s j ^ 2) := by
            simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            have hA : (∑ i, ∑ j, x i * x j * s i ^ 2) =
                (∑ i, x i * s i ^ 2) * (∑ j, x j) := by
              rw [← double_sum_mul (fun i => x i * s i ^ 2) x]
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
            have hB : (∑ i, ∑ j, 2 * (x i * s i) * (x j * s j)) =
                2 * ((∑ i, x i * s i) * (∑ j, x j * s j)) := by
              calc
                (∑ i, ∑ j, 2 * (x i * s i) * (x j * s j)) =
                    (∑ i, 2 * (x i * s i)) * (∑ j, x j * s j) := by
                      exact double_sum_mul (fun i => 2 * (x i * s i))
                        (fun j => x j * s j)
                _ = 2 * ((∑ i, x i * s i) * (∑ j, x j * s j)) := by
                      rw [← Finset.mul_sum]
                      ring
            have hC : (∑ i, ∑ j, x i * x j * s j ^ 2) =
                (∑ i, x i) * (∑ j, x j * s j ^ 2) := by
              rw [← double_sum_mul x (fun j => x j * s j ^ 2)]
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
            rw [hA, hB, hC]
    _ = 2 * (∑ i, x i) * (∑ i, x i * (s i) ^ 2) -
          2 * (∑ i, x i * s i) ^ 2 := by ring

/-- Zero-sum specialization of the pairwise squared-difference identity. -/
theorem pair_square_sum_of_sum_zero (x s : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, ∑ j, x i * x j * (s i - s j) ^ 2) =
      -2 * (∑ i, x i * s i) ^ 2 := by
  rw [pair_square_sum_identity, hx]
  ring

/-- Finite weighted feature cuts. -/
structure CutFamily (n m : ℕ) where
  length : Fin m → ℝ
  side : Fin m → Fin n → ℝ

namespace CutFamily

/-- Squared cut distance. -/
def dist (c : CutFamily n m) (i j : Fin n) : ℝ :=
  ∑ e, c.length e * (c.side e i - c.side e j) ^ 2

/-- Conditional-negative-type quadratic form of a cut distance. -/
def qform (c : CutFamily n m) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * x j * c.dist i j

/-- Reorder the quadratic form edge by edge. -/
theorem qform_eq_edge_sum (c : CutFamily n m) (x : Fin n → ℝ) :
    c.qform x =
      ∑ e, c.length e * (∑ i, ∑ j, x i * x j *
        (c.side e i - c.side e j) ^ 2) := by
  simp only [qform, dist]
  calc
    (∑ i, ∑ j, x i * x j * ∑ e, c.length e *
        (c.side e i - c.side e j) ^ 2) =
      ∑ i, ∑ j, ∑ e, c.length e *
        (x i * x j * (c.side e i - c.side e j) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
    _ = ∑ i, ∑ e, ∑ j, c.length e *
        (x i * x j * (c.side e i - c.side e j) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ e, ∑ i, ∑ j, c.length e *
        (x i * x j * (c.side e i - c.side e j) ^ 2) := by
          rw [Finset.sum_comm]
    _ = ∑ e, c.length e * (∑ i, ∑ j, x i * x j *
        (c.side e i - c.side e j) ^ 2) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]

/-- Exact edge-square expansion of the zero-sum quadratic form. -/
theorem qform_eq_negative_edge_squares (c : CutFamily n m) (x : Fin n → ℝ)
    (hx : ∑ i, x i = 0) :
    c.qform x = -2 * ∑ e, c.length e * (∑ i, x i * c.side e i) ^ 2 := by
  rw [qform_eq_edge_sum]
  have hedge : ∀ e : Fin m,
      (∑ i, ∑ j, x i * x j * (c.side e i - c.side e j) ^ 2) =
        -2 * (∑ i, x i * c.side e i) ^ 2 := by
    intro e
    exact pair_square_sum_of_sum_zero x (c.side e) hx
  simp_rw [hedge]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

end CutFamily

/-- Positive finite cuts containing every pendant singleton cut. -/
structure PositivePendantCutFamily (n m : ℕ) extends CutFamily n m where
  length_pos : ∀ e, 0 < length e
  pendant : Fin n → Fin m
  pendant_side : ∀ i j, side (pendant i) j = if j = i then 1 else 0

namespace PositivePendantCutFamily

/-- Distance inherited from the underlying cut family. -/
def dist (c : PositivePendantCutFamily n m) : Fin n → Fin n → ℝ := c.toCutFamily.dist

/-- Quadratic form inherited from the underlying cut family. -/
def qform (c : PositivePendantCutFamily n m) : (Fin n → ℝ) → ℝ := c.toCutFamily.qform

/-- Explicit Euclidean coordinate map for positive cuts. -/
noncomputable def feature (c : PositivePendantCutFamily n m) (i : Fin n) (e : Fin m) : ℝ :=
  Real.sqrt (c.length e) * c.side e i

/-- Positive cut distances are nonnegative. -/
theorem dist_nonneg (c : PositivePendantCutFamily n m) (i j : Fin n) :
    0 ≤ c.dist i j := by
  simp only [dist, CutFamily.dist]
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (c.length_pos e).le (sq_nonneg _)

@[simp] theorem dist_self (c : PositivePendantCutFamily n m) (i : Fin n) :
    c.dist i i = 0 := by
  simp [dist, CutFamily.dist]

/-- Pendant cuts make distance strictly positive between distinct leaves. -/
theorem dist_pos_of_ne (c : PositivePendantCutFamily n m) {i j : Fin n} (hij : i ≠ j) :
    0 < c.dist i j := by
  simp only [dist, CutFamily.dist]
  apply Finset.sum_pos'
  · intro e _
    exact mul_nonneg (c.length_pos e).le (sq_nonneg _)
  · refine ⟨c.pendant i, Finset.mem_univ _, ?_⟩
    rw [c.pendant_side i i, c.pendant_side i j]
    simp [Ne.symm hij, c.length_pos]

/-- The explicit feature map realizes cut distance as squared Euclidean distance. -/
theorem feature_sqDistance (c : PositivePendantCutFamily n m) (i j : Fin n) :
    (∑ e, (c.feature i e - c.feature j e) ^ 2) = c.dist i j := by
  apply Finset.sum_congr rfl
  intro e _
  rw [show c.feature i e - c.feature j e =
      Real.sqrt (c.length e) * (c.side e i - c.side e j) by
        simp only [feature]
        ring]
  rw [mul_pow, Real.sq_sqrt (c.length_pos e).le]

/-- A pendant cut isolates its corresponding coefficient. -/
theorem pendant_coordinate_sum (c : PositivePendantCutFamily n m) (x : Fin n → ℝ)
    (i : Fin n) :
    (∑ j, x j * c.side (c.pendant i) j) = x i := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [c.pendant_side i i]
    simp
  · intro j _ hji
    rw [c.pendant_side i j]
    simp [hji]
  · simp

/-- Every nonzero coefficient vector has strictly positive edge energy. -/
theorem positive_edge_energy (c : PositivePendantCutFamily n m) {x : Fin n → ℝ}
    (hx : x ≠ 0) :
    0 < ∑ e, c.length e * (∑ i, x i * c.side e i) ^ 2 := by
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro e _
    exact mul_nonneg (c.length_pos e).le (sq_nonneg _)
  · refine ⟨c.pendant i, Finset.mem_univ _, ?_⟩
    rw [c.pendant_coordinate_sum x i]
    exact mul_pos (c.length_pos _) (sq_pos_of_ne_zero hi)

/-- Positive pendant cut metrics have strict negative type. -/
theorem strict_negative_type (c : PositivePendantCutFamily n m) {x : Fin n → ℝ}
    (hsum : ∑ i, x i = 0) (hx : x ≠ 0) : c.qform x < 0 := by
  rw [qform, c.toCutFamily.qform_eq_negative_edge_squares x hsum]
  nlinarith [c.positive_edge_energy hx]

end PositivePendantCutFamily

/-- Rooted positive cuts with idempotent side indicators and a root contact height. -/
structure RootedCutContact (n m : ℕ) extends PositivePendantCutFamily n m where
  root : ℝ
  side_idempotent : ∀ e i, side e i ^ 2 = side e i

namespace RootedCutContact

/-- Complementary contact at the common rooted cuts of two leaves. -/
def contact (c : RootedCutContact n m) (i j : Fin n) : ℝ :=
  c.root - ∑ e, c.length e * (c.side e i * c.side e j)

/-- Polarized Stokes energy of two leaves. -/
def energy (c : RootedCutContact n m) (i j : Fin n) : ℝ :=
  2 * c.contact i j - c.contact i i - c.contact j j

/-- Complementary contact of a rooted cut system is symmetric. -/
theorem contact_symm (c : RootedCutContact n m) (i j : Fin n) :
    c.contact i j = c.contact j i := by
  simp only [contact]
  apply congrArg (fun x : ℝ => c.root - x)
  apply Finset.sum_congr rfl
  intro e _
  rw [mul_comm (c.side e i) (c.side e j)]

/-- Polarized Stokes energy vanishes on the diagonal. -/
@[simp] theorem energy_self (c : RootedCutContact n m) (i : Fin n) :
    c.energy i i = 0 := by
  simp only [energy]
  ring

/-- Polarized Stokes energy is symmetric. -/
theorem energy_symm (c : RootedCutContact n m) (i j : Fin n) :
    c.energy i j = c.energy j i := by
  rw [energy, energy, c.contact_symm i j]
  ring

/-- Polarization of complementary contact is exactly the additive cut distance. -/
theorem energy_eq_dist (c : RootedCutContact n m) (i j : Fin n) :
    c.energy i j = c.toPositivePendantCutFamily.dist i j := by
  simp only [energy, contact, PositivePendantCutFamily.dist, CutFamily.dist]
  have hterm : ∀ e : Fin m,
      c.length e * (c.side e i - c.side e j) ^ 2 =
        c.length e * c.side e i + c.length e * c.side e j -
          2 * (c.length e * (c.side e i * c.side e j)) := by
    intro e
    rw [show (c.side e i - c.side e j) ^ 2 =
      c.side e i ^ 2 + c.side e j ^ 2 - 2 * c.side e i * c.side e j by ring]
    rw [c.side_idempotent, c.side_idempotent]
    ring
  have hside : ∀ (e : Fin m) (k : Fin n), c.side e k * c.side e k = c.side e k := by
    intro e k
    simpa [pow_two] using c.side_idempotent e k
  simp_rw [hside]
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  ring

/-- Stokes energy strictly separates distinct leaves. -/
theorem energy_pos_of_ne (c : RootedCutContact n m) {i j : Fin n} (hij : i ≠ j) :
    0 < c.energy i j := by
  rw [c.energy_eq_dist]
  exact c.toPositivePendantCutFamily.dist_pos_of_ne hij

/-- Stokes energy is nonnegative. -/
theorem energy_nonneg (c : RootedCutContact n m) (i j : Fin n) :
    0 ≤ c.energy i j := by
  rw [c.energy_eq_dist]
  exact c.toPositivePendantCutFamily.dist_nonneg i j

/-- Stokes energy detects equality of labelled leaves. -/
theorem energy_eq_zero_iff (c : RootedCutContact n m) (i j : Fin n) :
    c.energy i j = 0 ↔ i = j := by
  constructor
  · intro hzero
    by_contra hij
    exact (ne_of_gt (c.energy_pos_of_ne hij)) hzero
  · rintro rfl
    exact c.energy_self i

/-- Cut additivity implies the metric triangle inequality for Stokes energy. -/
theorem energy_triangle (c : RootedCutContact n m) (i j k : Fin n) :
    c.energy i k ≤ c.energy i j + c.energy j k := by
  rw [c.energy_eq_dist, c.energy_eq_dist, c.energy_eq_dist]
  simp only [PositivePendantCutFamily.dist, CutFamily.dist,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have hindicator : (c.side e i - c.side e k) ^ 2 ≤
      (c.side e i - c.side e j) ^ 2 + (c.side e j - c.side e k) ^ 2 := by
    nlinarith [c.side_idempotent e i, c.side_idempotent e j,
      c.side_idempotent e k, sq_nonneg (c.side e i - c.side e j),
      sq_nonneg (c.side e j - c.side e k)]
  calc
    c.length e * (c.side e i - c.side e k) ^ 2 ≤
        c.length e * ((c.side e i - c.side e j) ^ 2 +
          (c.side e j - c.side e k) ^ 2) :=
      mul_le_mul_of_nonneg_left hindicator (c.length_pos e).le
    _ = c.length e * (c.side e i - c.side e j) ^ 2 +
        c.length e * (c.side e j - c.side e k) ^ 2 := by ring

/-- Explicit squared-Euclidean realization of Stokes energy. -/
theorem energy_has_explicit_sqEmbedding (c : RootedCutContact n m) (i j : Fin n) :
    (∑ e, (c.toPositivePendantCutFamily.feature i e -
      c.toPositivePendantCutFamily.feature j e) ^ 2) = c.energy i j := by
  rw [c.energy_eq_dist]
  exact c.toPositivePendantCutFamily.feature_sqDistance i j

/-- Stokes energy has strict negative type. -/
theorem energy_strict_negative_type (c : RootedCutContact n m) {x : Fin n → ℝ}
    (hsum : ∑ i, x i = 0) (hx : x ≠ 0) :
    (∑ i, ∑ j, x i * x j * c.energy i j) < 0 := by
  simp_rw [c.energy_eq_dist]
  exact c.toPositivePendantCutFamily.strict_negative_type hsum hx

end RootedCutContact

end IrregularStokes
end GaloisForLFunctions
