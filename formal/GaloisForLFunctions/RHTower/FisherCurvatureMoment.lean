import Mathlib.Tactic

/-!
# Moment determinant behind Fisher-surface curvature

For a finite positive weighted spectrum, this file identifies the `2 x 2` Hankel determinant
`M₂ M₄ - M₃²` with an exact pairwise dispersion sum.  It is nonnegative for nonnegative weights and
strictly positive as soon as two positive-weight, nonzero energies differ.

For the Euler prime-power spectrum, this determinant is the numerator of the negative scalar
curvature of the two-dimensional zeta Fisher metric.
-/

noncomputable section

namespace RHTower

/-- The `n`th finite weighted moment of an energy family. -/
def fisherWeightedMoment {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ s, w i * x i ^ n

private theorem double_sum_mul_swap {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, f i * g j) =
      ∑ i ∈ s, ∑ j ∈ s, g i * f j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact pairwise-dispersion formula for the Fisher curvature moment determinant. -/
theorem two_mul_fisherWeightedMoment_det
    {ι : Type*} (s : Finset ι) (w x : ι → ℝ) :
    2 * (fisherWeightedMoment s w x 2 * fisherWeightedMoment s w x 4 -
      fisherWeightedMoment s w x 3 ^ (2 : ℕ)) =
      ∑ i ∈ s, ∑ j ∈ s,
        w i * w j * x i ^ (2 : ℕ) * x j ^ (2 : ℕ) * (x i - x j) ^ (2 : ℕ) := by
  simp only [fisherWeightedMoment]
  rw [show (∑ i ∈ s, w i * x i ^ (3 : ℕ)) ^ (2 : ℕ) =
      (∑ i ∈ s, w i * x i ^ (3 : ℕ)) * (∑ j ∈ s, w j * x j ^ (3 : ℕ)) by ring]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  let A24 := ∑ i ∈ s, ∑ j ∈ s,
    (w i * x i ^ (2 : ℕ)) * (w j * x j ^ (4 : ℕ))
  let A42 := ∑ i ∈ s, ∑ j ∈ s,
    (w i * x i ^ (4 : ℕ)) * (w j * x j ^ (2 : ℕ))
  let A33 := ∑ i ∈ s, ∑ j ∈ s,
    (w i * x i ^ (3 : ℕ)) * (w j * x j ^ (3 : ℕ))
  have hswap : A24 = A42 := double_sum_mul_swap s
    (fun i => w i * x i ^ (2 : ℕ)) (fun i => w i * x i ^ (4 : ℕ))
  change 2 * (A24 - A33) = _
  calc
    2 * (A24 - A33) = A24 + A42 - 2 * A33 := by rw [← hswap]; ring
    _ = ∑ i ∈ s, ∑ j ∈ s,
        ((w i * x i ^ (2 : ℕ)) * (w j * x j ^ (4 : ℕ)) +
         (w i * x i ^ (4 : ℕ)) * (w j * x j ^ (2 : ℕ)) -
         2 * ((w i * x i ^ (3 : ℕ)) * (w j * x j ^ (3 : ℕ)))) := by
      dsimp [A24, A42, A33]
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Nonnegative weights force nonnegative Fisher curvature determinant. -/
theorem fisherWeightedMoment_det_nonneg
    {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ fisherWeightedMoment s w x 2 * fisherWeightedMoment s w x 4 -
      fisherWeightedMoment s w x 3 ^ (2 : ℕ) := by
  have hsum : 0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      w i * w j * x i ^ (2 : ℕ) * x j ^ (2 : ℕ) * (x i - x j) ^ (2 : ℕ) := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    have hwi0 := hw i hi
    have hwj0 := hw j hj
    positivity
  nlinarith [two_mul_fisherWeightedMoment_det s w x]

/-- Two distinct nonzero energies with positive weights force strictly positive curvature
determinant. -/
theorem fisherWeightedMoment_det_pos
    {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hwi : 0 < w i) (hwj : 0 < w j)
    (hxi : x i ≠ 0) (hxj : x j ≠ 0) (hxij : x i ≠ x j) :
    0 < fisherWeightedMoment s w x 2 * fisherWeightedMoment s w x 4 -
      fisherWeightedMoment s w x 3 ^ (2 : ℕ) := by
  have hterm : 0 < w i * w j * x i ^ (2 : ℕ) * x j ^ (2 : ℕ) * (x i - x j) ^ (2 : ℕ) := by
    positivity
  have hinner : 0 < ∑ k ∈ s,
      w i * w k * x i ^ (2 : ℕ) * x k ^ (2 : ℕ) * (x i - x k) ^ (2 : ℕ) := by
    apply Finset.sum_pos'
    · intro k hk
      have hwk0 := hw k hk
      positivity
    · exact ⟨j, hj, by simpa using hterm⟩
  have hsum : 0 < ∑ l ∈ s, ∑ k ∈ s,
      w l * w k * x l ^ (2 : ℕ) * x k ^ (2 : ℕ) * (x l - x k) ^ (2 : ℕ) := by
    apply Finset.sum_pos'
    · intro l hl
      apply Finset.sum_nonneg
      intro k hk
      have hwl0 := hw l hl
      have hwk0 := hw k hk
      positivity
    · exact ⟨i, hi, hinner⟩
  nlinarith [two_mul_fisherWeightedMoment_det s w x]

/-- The `n`th weighted moment of a summable infinite energy family. -/
def fisherWeightedTsumMoment {ι : Type*} (w x : ι → ℝ) (n : ℕ) : ℝ :=
  ∑' i, w i * x i ^ n

/-- Infinite pairwise-dispersion identity. Absolute summability of moments two through four is the
exact analytic input needed to pass the finite curvature formula to a countable spectrum. -/
theorem two_mul_fisherWeightedTsumMoment_det
    {ι : Type*} (w x : ι → ℝ)
    (h2 : Summable fun i => |w i * x i ^ (2 : ℕ)|)
    (h3 : Summable fun i => |w i * x i ^ (3 : ℕ)|)
    (h4 : Summable fun i => |w i * x i ^ (4 : ℕ)|) :
    2 * (fisherWeightedTsumMoment w x 2 * fisherWeightedTsumMoment w x 4 -
      fisherWeightedTsumMoment w x 3 ^ (2 : ℕ)) =
      ∑' z : ι × ι,
        w z.1 * w z.2 * x z.1 ^ (2 : ℕ) * x z.2 ^ (2 : ℕ) * (x z.1 - x z.2) ^ (2 : ℕ) := by
  let a2 : ι → ℝ := fun i => w i * x i ^ (2 : ℕ)
  let a3 : ι → ℝ := fun i => w i * x i ^ (3 : ℕ)
  let a4 : ι → ℝ := fun i => w i * x i ^ (4 : ℕ)
  have h2n : Summable fun i => ‖a2 i‖ := by simpa [a2, Real.norm_eq_abs] using h2
  have h3n : Summable fun i => ‖a3 i‖ := by simpa [a3, Real.norm_eq_abs] using h3
  have h4n : Summable fun i => ‖a4 i‖ := by simpa [a4, Real.norm_eq_abs] using h4
  let P24 : ι × ι → ℝ := fun z => a2 z.1 * a4 z.2
  let P42 : ι × ι → ℝ := fun z => a4 z.1 * a2 z.2
  let P33 : ι × ι → ℝ := fun z => a3 z.1 * a3 z.2
  have hP24 : Summable P24 := by
    exact summable_mul_of_summable_norm h2n h4n
  have hP42 : Summable P42 := by
    exact summable_mul_of_summable_norm h4n h2n
  have hP33 : Summable P33 := by
    exact summable_mul_of_summable_norm h3n h3n
  have hm24 : fisherWeightedTsumMoment w x 2 * fisherWeightedTsumMoment w x 4 =
      ∑' z, P24 z := by
    simpa [fisherWeightedTsumMoment, a2, a4, P24] using
      (tsum_mul_tsum_of_summable_norm h2n h4n)
  have hm42 : fisherWeightedTsumMoment w x 4 * fisherWeightedTsumMoment w x 2 =
      ∑' z, P42 z := by
    simpa [fisherWeightedTsumMoment, a2, a4, P42] using
      (tsum_mul_tsum_of_summable_norm h4n h2n)
  have hm33 : fisherWeightedTsumMoment w x 3 ^ (2 : ℕ) = ∑' z, P33 z := by
    rw [pow_two]
    simpa [fisherWeightedTsumMoment, a3, P33] using
      (tsum_mul_tsum_of_summable_norm h3n h3n)
  let Q : ι × ι → ℝ := fun z => P24 z + P42 z - 2 * P33 z
  have hQ : Summable Q := hP24.add hP42 |>.sub (hP33.mul_left 2)
  calc
    2 * (fisherWeightedTsumMoment w x 2 * fisherWeightedTsumMoment w x 4 -
        fisherWeightedTsumMoment w x 3 ^ (2 : ℕ))
        = fisherWeightedTsumMoment w x 2 * fisherWeightedTsumMoment w x 4 +
          fisherWeightedTsumMoment w x 4 * fisherWeightedTsumMoment w x 2 -
          2 * fisherWeightedTsumMoment w x 3 ^ (2 : ℕ) := by ring
    _ = (∑' z, P24 z) + (∑' z, P42 z) - 2 * (∑' z, P33 z) := by
      rw [hm24, hm42, hm33]
    _ = ∑' z, Q z := by
      rw [← hP33.tsum_mul_left 2, ← hP24.tsum_add hP42,
        ← (hP24.add hP42).tsum_sub (hP33.mul_left 2)]
    _ = _ := by
      apply tsum_congr
      intro z
      dsimp [Q, P24, P42, P33, a2, a3, a4]
      ring

/-- A countable positive spectrum with two distinct nonzero positive-weight energies has strictly
positive Fisher curvature determinant. -/
theorem fisherWeightedTsumMoment_det_pos
    {ι : Type*} (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (h2 : Summable fun i => |w i * x i ^ (2 : ℕ)|)
    (h3 : Summable fun i => |w i * x i ^ (3 : ℕ)|)
    (h4 : Summable fun i => |w i * x i ^ (4 : ℕ)|)
    {i j : ι} (hwi : 0 < w i) (hwj : 0 < w j)
    (hxi : x i ≠ 0) (hxj : x j ≠ 0) (hxij : x i ≠ x j) :
    0 < fisherWeightedTsumMoment w x 2 * fisherWeightedTsumMoment w x 4 -
      fisherWeightedTsumMoment w x 3 ^ (2 : ℕ) := by
  let Q : ι × ι → ℝ := fun z =>
    w z.1 * w z.2 * x z.1 ^ (2 : ℕ) * x z.2 ^ (2 : ℕ) * (x z.1 - x z.2) ^ (2 : ℕ)
  have hQsum : Summable Q := by
    let a2 : ι → ℝ := fun k => w k * x k ^ (2 : ℕ)
    let a3 : ι → ℝ := fun k => w k * x k ^ (3 : ℕ)
    let a4 : ι → ℝ := fun k => w k * x k ^ (4 : ℕ)
    have h2n : Summable fun k => ‖a2 k‖ := by simpa [a2, Real.norm_eq_abs] using h2
    have h3n : Summable fun k => ‖a3 k‖ := by simpa [a3, Real.norm_eq_abs] using h3
    have h4n : Summable fun k => ‖a4 k‖ := by simpa [a4, Real.norm_eq_abs] using h4
    have h24 : Summable (fun z : ι × ι => a2 z.1 * a4 z.2) :=
      summable_mul_of_summable_norm h2n h4n
    have h42 : Summable (fun z : ι × ι => a4 z.1 * a2 z.2) :=
      summable_mul_of_summable_norm h4n h2n
    have h33 : Summable (fun z : ι × ι => a3 z.1 * a3 z.2) :=
      summable_mul_of_summable_norm h3n h3n
    have hcomb := h24.add h42 |>.sub (h33.mul_left 2)
    exact hcomb.congr (fun z => by dsimp [Q, a2, a3, a4]; ring)
  have hQnonneg : ∀ z, 0 ≤ Q z := by
    intro z
    have hw1 := hw z.1
    have hw2 := hw z.2
    dsimp [Q]
    positivity
  have hQpos : 0 < Q (i, j) := by
    dsimp [Q]
    positivity
  have htsumpos : 0 < ∑' z, Q z := hQsum.tsum_pos hQnonneg (i, j) hQpos
  rw [← two_mul_fisherWeightedTsumMoment_det w x h2 h3 h4] at htsumpos
  nlinarith

end RHTower
