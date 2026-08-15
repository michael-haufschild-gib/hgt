import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Degree-one discriminant tail stability

The shifted degree-one determinant is stable under a tail whose absolute
moment error is smaller than the positive bulk margin.  The same algebra
identifies exactly the contribution of one weighted conjugate pair.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The degree-one shifted Hankel determinant of three successive moments. -/
def degreeOneShiftedDet (m1 m2 m3 : ℝ) : ℝ :=
  m1 * m3 - m2 ^ 2

/-- The absolute-error budget for a degree-one shifted determinant. -/
def degreeOneTailError (L1 L2 L3 eta1 eta2 eta3 : ℝ) : ℝ :=
  L1 * eta3 + L3 * eta1 + 2 * L2 * eta2 + eta1 * eta3 + eta2 ^ 2

/-- Exact expansion of the degree-one determinant under a three-moment tail. -/
theorem degreeOneShiftedDet_tail_expansion
    (L1 L2 L3 E1 E2 E3 : ℝ) :
    degreeOneShiftedDet (L1 + E1) (L2 + E2) (L3 + E3) -
      degreeOneShiftedDet L1 L2 L3 =
      L1 * E3 + L3 * E1 - 2 * L2 * E2 + E1 * E3 - E2 ^ 2 := by
  simp only [degreeOneShiftedDet]
  ring

/-- Absolute bound for the exact degree-one tail perturbation. -/
theorem abs_degreeOneShiftedDet_tail_expansion_le
    {L1 L2 L3 E1 E2 E3 eta1 eta2 eta3 : ℝ}
    (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) (hL3 : 0 ≤ L3)
    (hE1 : |E1| ≤ eta1) (hE2 : |E2| ≤ eta2) (hE3 : |E3| ≤ eta3)
    (heta1 : 0 ≤ eta1) :
    |degreeOneShiftedDet (L1 + E1) (L2 + E2) (L3 + E3) -
        degreeOneShiftedDet L1 L2 L3| ≤
      degreeOneTailError L1 L2 L3 eta1 eta2 eta3 := by
  rw [degreeOneShiftedDet_tail_expansion]
  have hsum :
      |L1 * E3 + L3 * E1 - 2 * L2 * E2 + E1 * E3 - E2 ^ 2| ≤
        |L1 * E3| + |L3 * E1| + |2 * L2 * E2| + |E1 * E3| + |E2 ^ 2| := by
    calc
      |L1 * E3 + L3 * E1 - 2 * L2 * E2 + E1 * E3 - E2 ^ 2| =
          |((L1 * E3 + L3 * E1) - 2 * L2 * E2 + E1 * E3) - E2 ^ 2| := by ring
      _ ≤ |(L1 * E3 + L3 * E1) - 2 * L2 * E2 + E1 * E3| + |E2 ^ 2| :=
        abs_sub _ _
      _ ≤ (|(L1 * E3 + L3 * E1) - 2 * L2 * E2| + |E1 * E3|) + |E2 ^ 2| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((|L1 * E3 + L3 * E1| + |2 * L2 * E2|) + |E1 * E3|) + |E2 ^ 2| := by
        gcongr
        exact abs_sub _ _
      _ ≤ (((|L1 * E3| + |L3 * E1|) + |2 * L2 * E2|) + |E1 * E3|) + |E2 ^ 2| := by
        gcongr
        exact abs_add_le _ _
      _ = |L1 * E3| + |L3 * E1| + |2 * L2 * E2| + |E1 * E3| + |E2 ^ 2| := by ring
  have h1 : |L1 * E3| ≤ L1 * eta3 := by
    rw [abs_mul, abs_of_nonneg hL1]
    exact mul_le_mul_of_nonneg_left hE3 hL1
  have h2 : |L3 * E1| ≤ L3 * eta1 := by
    rw [abs_mul, abs_of_nonneg hL3]
    exact mul_le_mul_of_nonneg_left hE1 hL3
  have h3 : |2 * L2 * E2| ≤ 2 * L2 * eta2 := by
    simpa [abs_mul, abs_of_nonneg hL2] using
      mul_le_mul_of_nonneg_left hE2 (by positivity : 0 ≤ 2 * L2)
  have h4 : |E1 * E3| ≤ eta1 * eta3 := by
    rw [abs_mul]
    exact mul_le_mul hE1 hE3 (abs_nonneg E3) heta1
  have h5 : |E2 ^ 2| ≤ eta2 ^ 2 := by
    rw [abs_pow]
    simpa [pow_two] using mul_self_le_mul_self (abs_nonneg E2) hE2
  simp only [degreeOneTailError]
  linarith

/-- A strictly dominant bulk determinant remains positive after the tail. -/
theorem degreeOneShiftedDet_pos_of_tail_margin
    {L1 L2 L3 E1 E2 E3 eta1 eta2 eta3 : ℝ}
    (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) (hL3 : 0 ≤ L3)
    (hE1 : |E1| ≤ eta1) (hE2 : |E2| ≤ eta2) (hE3 : |E3| ≤ eta3)
    (heta1 : 0 ≤ eta1)
    (hmargin : degreeOneTailError L1 L2 L3 eta1 eta2 eta3 <
      degreeOneShiftedDet L1 L2 L3) :
    0 < degreeOneShiftedDet (L1 + E1) (L2 + E2) (L3 + E3) := by
  have hbound := abs_degreeOneShiftedDet_tail_expansion_le
    hL1 hL2 hL3 hE1 hE2 hE3 heta1
  have hlower := neg_abs_le
    (degreeOneShiftedDet (L1 + E1) (L2 + E2) (L3 + E3) -
      degreeOneShiftedDet L1 L2 L3)
  linarith

/-- Moment `k` of a finite real bulk with weights `M`. -/
def degreeOneBulkMoment (B : Finset ℝ) (M : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∑ x ∈ B, M x * x ^ k

/-- Real moment of a conjugate pair, each atom carrying weight `mu`. -/
def degreeOnePairMoment (mu u v : ℝ) (k : ℕ) : ℝ :=
  2 * mu * (((u : ℂ) + v * Complex.I) ^ k).re

/-- Cross term between the real atom `x` and `u + iv`. -/
def degreeOneDiscriminantCross (u v x : ℝ) : ℝ :=
  (((u : ℂ) + v * Complex.I) * (((u : ℂ) + v * Complex.I) - x) ^ 2).re

/-- The isolated degree-one determinant of a weighted conjugate pair. -/
theorem degreeOnePairMoment_det (mu u v : ℝ) :
    degreeOneShiftedDet (degreeOnePairMoment mu u v 1)
      (degreeOnePairMoment mu u v 2) (degreeOnePairMoment mu u v 3) =
      -4 * mu ^ 2 * (u ^ 2 + v ^ 2) * v ^ 2 := by
  simp [degreeOneShiftedDet, degreeOnePairMoment, pow_succ, Complex.mul_re]
  ring

/-- The summed real-bulk cross terms equal the mixed determinant contribution. -/
theorem degreeOneBulkPair_cross_sum
    (B : Finset ℝ) (M : ℝ → ℝ) (mu u v : ℝ) :
    2 * mu * ∑ x ∈ B, M x * x * degreeOneDiscriminantCross u v x =
      degreeOneBulkMoment B M 1 * degreeOnePairMoment mu u v 3 +
        degreeOneBulkMoment B M 3 * degreeOnePairMoment mu u v 1 -
          2 * degreeOneBulkMoment B M 2 * degreeOnePairMoment mu u v 2 := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [degreeOneBulkMoment]
  | insert x B hx ih =>
      simp only [degreeOneBulkMoment, Finset.sum_insert hx] at ih ⊢
      have hlocal :
          2 * mu * M x * x * degreeOneDiscriminantCross u v x =
            M x * x ^ 1 * degreeOnePairMoment mu u v 3 +
              M x * x ^ 3 * degreeOnePairMoment mu u v 1 -
                2 * M x * x ^ 2 * degreeOnePairMoment mu u v 2 := by
        simp [degreeOnePairMoment, degreeOneDiscriminantCross, pow_succ, Complex.mul_re]
        ring
      calc
        2 * mu * (M x * x * degreeOneDiscriminantCross u v x +
            ∑ x ∈ B, M x * x * degreeOneDiscriminantCross u v x) =
            (2 * mu * M x * x * degreeOneDiscriminantCross u v x) +
              (2 * mu * ∑ x ∈ B, M x * x * degreeOneDiscriminantCross u v x) := by ring
        _ =
            (M x * x ^ 1 * degreeOnePairMoment mu u v 3 +
              M x * x ^ 3 * degreeOnePairMoment mu u v 1 -
                2 * M x * x ^ 2 * degreeOnePairMoment mu u v 2) +
              ((∑ x ∈ B, M x * x ^ 1) * degreeOnePairMoment mu u v 3 +
                (∑ x ∈ B, M x * x ^ 3) * degreeOnePairMoment mu u v 1 -
                  (2 * ∑ x ∈ B, M x * x ^ 2) * degreeOnePairMoment mu u v 2) := by
            rw [hlocal, ih]
        _ =
            (M x * x ^ 1 + ∑ x ∈ B, M x * x ^ 1) * degreeOnePairMoment mu u v 3 +
              (M x * x ^ 3 + ∑ x ∈ B, M x * x ^ 3) * degreeOnePairMoment mu u v 1 -
                2 * (M x * x ^ 2 + ∑ x ∈ B, M x * x ^ 2) * degreeOnePairMoment mu u v 2 := by
            ring

/-- Exact degree-one determinant change after adjoining one conjugate pair. -/
theorem degreeOneBulkPair_update
    (B : Finset ℝ) (M : ℝ → ℝ) (mu u v : ℝ) :
    degreeOneShiftedDet
        (degreeOneBulkMoment B M 1 + degreeOnePairMoment mu u v 1)
        (degreeOneBulkMoment B M 2 + degreeOnePairMoment mu u v 2)
        (degreeOneBulkMoment B M 3 + degreeOnePairMoment mu u v 3) -
      degreeOneShiftedDet
        (degreeOneBulkMoment B M 1) (degreeOneBulkMoment B M 2)
        (degreeOneBulkMoment B M 3) =
      2 * mu * ∑ x ∈ B, M x * x * degreeOneDiscriminantCross u v x -
        4 * mu ^ 2 * (u ^ 2 + v ^ 2) * v ^ 2 := by
  rw [degreeOneShiftedDet_tail_expansion,
    ← degreeOneBulkPair_cross_sum]
  have hpair := degreeOnePairMoment_det mu u v
  simp only [degreeOneShiftedDet] at hpair
  calc
    2 * mu * ∑ x ∈ B, M x * x * degreeOneDiscriminantCross u v x +
          degreeOnePairMoment mu u v 1 * degreeOnePairMoment mu u v 3 -
        degreeOnePairMoment mu u v 2 ^ 2 =
        2 * mu * ∑ x ∈ B, M x * x * degreeOneDiscriminantCross u v x +
          (degreeOnePairMoment mu u v 1 * degreeOnePairMoment mu u v 3 -
            degreeOnePairMoment mu u v 2 ^ 2) := by ring
    _ = 2 * mu * ∑ x ∈ B, M x * x * degreeOneDiscriminantCross u v x +
        (-4 * mu ^ 2 * (u ^ 2 + v ^ 2) * v ^ 2) := by rw [hpair]
    _ = 2 * mu * ∑ x ∈ B, M x * x * degreeOneDiscriminantCross u v x -
        4 * mu ^ 2 * (u ^ 2 + v ^ 2) * v ^ 2 := by ring

/-- Moment of a conjugate pair written directly from its complex representative. -/
def degreeOneConjugatePairMoment (mu : ℝ) (y : ℂ) (k : ℕ) : ℝ :=
  2 * mu * (y ^ k).re

/-- Cross term between a real bulk atom and a complex conjugate-pair representative. -/
def degreeOneConjugatePairCross (y : ℂ) (x : ℝ) : ℝ :=
  (y * (y - x) ^ 2).re

/-- The real moment is the sum of the two conjugate weighted moments. -/
theorem degreeOneConjugatePairMoment_eq_pair_sum (mu : ℝ) (y : ℂ) (k : ℕ) :
    degreeOneConjugatePairMoment mu y k =
      (mu * y ^ k + mu * ((starRingEnd ℂ) y) ^ k).re := by
  rw [← map_pow]
  simp [degreeOneConjugatePairMoment, Complex.mul_re]
  ring

/-- The isolated pair determinant is its negative imaginary-defect square. -/
theorem degreeOneConjugatePair_det (mu : ℝ) (y : ℂ) :
    degreeOneShiftedDet (degreeOneConjugatePairMoment mu y 1)
      (degreeOneConjugatePairMoment mu y 2)
      (degreeOneConjugatePairMoment mu y 3) =
      -4 * mu ^ 2 * Complex.normSq y * y.im ^ 2 := by
  rcases y with ⟨u, v⟩
  simpa [degreeOneConjugatePairMoment, Complex.normSq_apply] using
    degreeOnePairMoment_det mu u v

/-- Exact degree-one determinant change after adjoining one complex conjugate pair. -/
theorem degreeOneBulkConjugatePair_update
    (B : Finset ℝ) (M : ℝ → ℝ) (mu : ℝ) (y : ℂ) :
    degreeOneShiftedDet
        (degreeOneBulkMoment B M 1 + degreeOneConjugatePairMoment mu y 1)
        (degreeOneBulkMoment B M 2 + degreeOneConjugatePairMoment mu y 2)
        (degreeOneBulkMoment B M 3 + degreeOneConjugatePairMoment mu y 3) -
      degreeOneShiftedDet
        (degreeOneBulkMoment B M 1) (degreeOneBulkMoment B M 2)
        (degreeOneBulkMoment B M 3) =
      2 * mu * ∑ x ∈ B, M x * x * degreeOneConjugatePairCross y x -
        4 * mu ^ 2 * Complex.normSq y * y.im ^ 2 := by
  rcases y with ⟨u, v⟩
  simpa [degreeOneConjugatePairMoment, degreeOneConjugatePairCross,
    Complex.normSq_apply] using degreeOneBulkPair_update B M mu u v

/-- A genuinely nonreal pair of nonzero weight has strictly negative degree-one determinant. -/
theorem degreeOneConjugatePair_det_neg {mu : ℝ} {y : ℂ}
    (hmu : mu ≠ 0) (hy : y.im ≠ 0) :
    degreeOneShiftedDet (degreeOneConjugatePairMoment mu y 1)
      (degreeOneConjugatePairMoment mu y 2)
      (degreeOneConjugatePairMoment mu y 3) < 0 := by
  rcases y with ⟨u, v⟩
  rw [show degreeOneConjugatePairMoment mu { re := u, im := v } 1 =
      degreeOnePairMoment mu u v 1 by rfl,
    show degreeOneConjugatePairMoment mu { re := u, im := v } 2 =
      degreeOnePairMoment mu u v 2 by rfl,
    show degreeOneConjugatePairMoment mu { re := u, im := v } 3 =
      degreeOnePairMoment mu u v 3 by rfl,
    degreeOnePairMoment_det]
  have hmu2 : 0 < mu ^ 2 := sq_pos_of_ne_zero hmu
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hy
  have hnorm : 0 < u ^ 2 + v ^ 2 := by positivity
  nlinarith [mul_pos hmu2 (mul_pos hnorm hv2)]

/-- Nonnegative real atoms and weights give nonnegative bulk moments. -/
theorem degreeOneBulkMoment_nonneg
    {B : Finset ℝ} {M : ℝ → ℝ} {k : ℕ}
    (hM : ∀ x ∈ B, 0 ≤ M x) (hx : ∀ x ∈ B, 0 ≤ x) :
    0 ≤ degreeOneBulkMoment B M k := by
  unfold degreeOneBulkMoment
  exact Finset.sum_nonneg fun x hxmem =>
    mul_nonneg (hM x hxmem) (pow_nonneg (hx x hxmem) _)

/-- A finite nonnegative real bulk satisfies the degree-one tail-stability criterion. -/
theorem degreeOneFiniteBulk_tail_pos_of_margin
    {B : Finset ℝ} {M : ℝ → ℝ} {E1 E2 E3 eta1 eta2 eta3 : ℝ}
    (hM : ∀ x ∈ B, 0 ≤ M x) (hx : ∀ x ∈ B, 0 ≤ x)
    (hE1 : |E1| ≤ eta1) (hE2 : |E2| ≤ eta2) (hE3 : |E3| ≤ eta3)
    (heta1 : 0 ≤ eta1)
    (hmargin : degreeOneTailError
        (degreeOneBulkMoment B M 1) (degreeOneBulkMoment B M 2)
        (degreeOneBulkMoment B M 3) eta1 eta2 eta3 <
      degreeOneShiftedDet
        (degreeOneBulkMoment B M 1) (degreeOneBulkMoment B M 2)
        (degreeOneBulkMoment B M 3)) :
    0 < degreeOneShiftedDet
      (degreeOneBulkMoment B M 1 + E1) (degreeOneBulkMoment B M 2 + E2)
      (degreeOneBulkMoment B M 3 + E3) := by
  apply degreeOneShiftedDet_pos_of_tail_margin
  · exact degreeOneBulkMoment_nonneg hM hx
  · exact degreeOneBulkMoment_nonneg hM hx
  · exact degreeOneBulkMoment_nonneg hM hx
  · exact hE1
  · exact hE2
  · exact hE3
  · exact heta1
  · exact hmargin

end

end GaloisForLFunctions.HTGeometry
