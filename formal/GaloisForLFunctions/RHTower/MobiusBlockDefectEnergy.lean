import GaloisForLFunctions.RHTower.MobiusBlockDefectCompression
import Mathlib.Analysis.Real.Sqrt

/-!
# Quadratic cumulative-defect energy for the Möbius block current

The compressed signed block-defect current admits an exact discrete Abel decomposition through
its cumulative defects.  Cauchy--Schwarz then identifies a quadratic `H⁻¹`-type source invariant:
endpoint defect plus cumulative-defect energy paired with the squared gradient of the Gibbs
weight.

At dyadic scale `U`, block width `h`, and Gibbs parameter `x ≍ U⁻¹`, the exponential-gradient
energy is `O(h / U)`.  Thus the natural random-walk-scale condition
`∑_j |∑_{i≤j} d_i|² ≤ U² / h · U^o(1)`, together with a square-root endpoint defect, suffices for
the critical `U^(1/2+o(1))` current bound.  This is a genuinely signed quadratic source; estimates
for `∑ |d_j|` do not imply it.
-/

open scoped BigOperators

namespace RHTower

/-- Exact finite discrete Abel identity in prefix-defect coordinates. -/
theorem sum_range_mul_eq_prefix_last_add_sum_prefix_mul_sub
    (d w : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), d j * w j =
      (∑ i ∈ Finset.range (N + 1), d i) * w N +
        ∑ j ∈ Finset.range N,
          (∑ i ∈ Finset.range (j + 1), d i) * (w j - w (j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Finset.sum_range_succ]
      ring

/-- Cauchy--Schwarz form of discrete Abel summation.  It replaces total variation of individual
defects by quadratic energy of their cumulative current. -/
theorem abs_sum_range_mul_le_endpoint_add_prefixEnergy
    (d w : ℕ → ℝ) (N : ℕ) :
    |∑ j ∈ Finset.range (N + 1), d j * w j| ≤
      |∑ i ∈ Finset.range (N + 1), d i| * |w N| +
        Real.sqrt
          (∑ j ∈ Finset.range N,
            (∑ i ∈ Finset.range (j + 1), d i) ^ 2) *
        Real.sqrt
          (∑ j ∈ Finset.range N, (w j - w (j + 1)) ^ 2) := by
  rw [sum_range_mul_eq_prefix_last_add_sum_prefix_mul_sub]
  calc
    |(∑ i ∈ Finset.range (N + 1), d i) * w N +
        ∑ j ∈ Finset.range N,
          (∑ i ∈ Finset.range (j + 1), d i) * (w j - w (j + 1))|
        ≤ |(∑ i ∈ Finset.range (N + 1), d i) * w N| +
          |∑ j ∈ Finset.range N,
            (∑ i ∈ Finset.range (j + 1), d i) * (w j - w (j + 1))| :=
      abs_add_le _ _
    _ ≤ |∑ i ∈ Finset.range (N + 1), d i| * |w N| +
        ∑ j ∈ Finset.range N,
          |∑ i ∈ Finset.range (j + 1), d i| * |w j - w (j + 1)| := by
      rw [abs_mul]
      gcongr
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun j => (∑ i ∈ Finset.range (j + 1), d i) * (w j - w (j + 1)))
        (Finset.range N)
    _ ≤ |∑ i ∈ Finset.range (N + 1), d i| * |w N| +
        Real.sqrt
          (∑ j ∈ Finset.range N,
            (∑ i ∈ Finset.range (j + 1), d i) ^ 2) *
        Real.sqrt
          (∑ j ∈ Finset.range N, (w j - w (j + 1)) ^ 2) := by
      gcongr
      simpa only [sq_abs] using
        Real.sum_mul_le_sqrt_mul_sqrt (Finset.range N)
          (fun j => |∑ i ∈ Finset.range (j + 1), d i|)
          (fun j => |w j - w (j + 1)|)

/-- When an extended current has zero total coefficient, its cutoff flux is exactly the
cumulative-defect term: no terminal endpoint remains. -/
theorem sum_range_mul_eq_sum_prefix_mul_sub_of_total_eq_zero
    (d w : ℕ → ℝ) (N : ℕ)
    (htotal : ∑ i ∈ Finset.range (N + 1), d i = 0) :
    ∑ j ∈ Finset.range (N + 1), d j * w j =
      ∑ j ∈ Finset.range N,
        (∑ i ∈ Finset.range (j + 1), d i) * (w j - w (j + 1)) := by
  rw [sum_range_mul_eq_prefix_last_add_sum_prefix_mul_sub, htotal, zero_mul, zero_add]

/-- Quadratic cutoff-flux bound for an extended zero-total current. -/
theorem abs_sum_range_mul_le_prefixEnergy_of_total_eq_zero
    (d w : ℕ → ℝ) (N : ℕ)
    (htotal : ∑ i ∈ Finset.range (N + 1), d i = 0) :
    |∑ j ∈ Finset.range (N + 1), d j * w j| ≤
      Real.sqrt
          (∑ j ∈ Finset.range N,
            (∑ i ∈ Finset.range (j + 1), d i) ^ 2) *
        Real.sqrt
          (∑ j ∈ Finset.range N, (w j - w (j + 1)) ^ 2) := by
  simpa [htotal] using abs_sum_range_mul_le_endpoint_add_prefixEnergy d w N

/-- Squared-gradient budget for exponential weights on a monotone block mesh. -/
theorem sum_exp_blockWeightGradient_sq_le
    (representative : ℕ → ℝ) (N : ℕ) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h)
    (hmono : ∀ j < N, representative j ≤ representative (j + 1))
    (hwidth : ∀ j < N, representative (j + 1) - representative j ≤ h) :
    ∑ j ∈ Finset.range N,
        (Real.exp (-(x * representative j)) -
          Real.exp (-(x * representative (j + 1)))) ^ 2 ≤
      ∑ j ∈ Finset.range N,
        (x * h * Real.exp (-(x * representative j))) ^ 2 := by
  apply Finset.sum_le_sum
  intro j hj
  rw [sq_le_sq]
  have hjN : j < N := Finset.mem_range.mp hj
  simpa [abs_sub_comm, abs_of_nonneg hx, abs_of_nonneg hh] using
    abs_exp_neg_mul_sub_blockRepresentative_le
      hx (hmono j hjN) (hwidth j hjN)

/-- Gibbs specialization: endpoint defect plus cumulative-defect energy controls the signed
block current with an explicit exponential-gradient majorant. -/
theorem abs_exp_blockDefectCurrent_le_endpoint_add_prefixEnergy
    (d representative : ℕ → ℝ) (N : ℕ) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h)
    (hmono : ∀ j < N, representative j ≤ representative (j + 1))
    (hwidth : ∀ j < N, representative (j + 1) - representative j ≤ h) :
    |∑ j ∈ Finset.range (N + 1),
        d j * Real.exp (-(x * representative j))| ≤
      |∑ i ∈ Finset.range (N + 1), d i| *
          |Real.exp (-(x * representative N))| +
        Real.sqrt
          (∑ j ∈ Finset.range N,
            (∑ i ∈ Finset.range (j + 1), d i) ^ 2) *
        Real.sqrt
          (∑ j ∈ Finset.range N,
            (x * h * Real.exp (-(x * representative j))) ^ 2) := by
  calc
    |∑ j ∈ Finset.range (N + 1),
        d j * Real.exp (-(x * representative j))|
        ≤ |∑ i ∈ Finset.range (N + 1), d i| *
            |Real.exp (-(x * representative N))| +
          Real.sqrt
            (∑ j ∈ Finset.range N,
              (∑ i ∈ Finset.range (j + 1), d i) ^ 2) *
          Real.sqrt
            (∑ j ∈ Finset.range N,
              (Real.exp (-(x * representative j)) -
                Real.exp (-(x * representative (j + 1)))) ^ 2) :=
      abs_sum_range_mul_le_endpoint_add_prefixEnergy d
        (fun j => Real.exp (-(x * representative j))) N
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_left
      · exact Real.sqrt_le_sqrt
          (sum_exp_blockWeightGradient_sq_le
            representative N hx hh hmono hwidth)
      · exact Real.sqrt_nonneg _

/-- Sector-flux specialization for a zero-total extended rectangle current.  Moving-cutoff
prefixes are the only source terms, paired against the Gibbs gradient. -/
theorem abs_exp_zeroTotalSectorFluxCurrent_le_prefixEnergy
    (d representative : ℕ → ℝ) (N : ℕ) {x h : ℝ}
    (htotal : ∑ i ∈ Finset.range (N + 1), d i = 0)
    (hx : 0 ≤ x) (hh : 0 ≤ h)
    (hmono : ∀ j < N, representative j ≤ representative (j + 1))
    (hwidth : ∀ j < N, representative (j + 1) - representative j ≤ h) :
    |∑ j ∈ Finset.range (N + 1),
        d j * Real.exp (-(x * representative j))| ≤
      Real.sqrt
          (∑ j ∈ Finset.range N,
            (∑ i ∈ Finset.range (j + 1), d i) ^ 2) *
        Real.sqrt
          (∑ j ∈ Finset.range N,
            (x * h * Real.exp (-(x * representative j))) ^ 2) := by
  calc
    |∑ j ∈ Finset.range (N + 1),
        d j * Real.exp (-(x * representative j))|
        ≤ Real.sqrt
            (∑ j ∈ Finset.range N,
              (∑ i ∈ Finset.range (j + 1), d i) ^ 2) *
          Real.sqrt
            (∑ j ∈ Finset.range N,
              (Real.exp (-(x * representative j)) -
                Real.exp (-(x * representative (j + 1)))) ^ 2) :=
      abs_sum_range_mul_le_prefixEnergy_of_total_eq_zero d
        (fun j => Real.exp (-(x * representative j))) N htotal
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.sqrt_le_sqrt
          (sum_exp_blockWeightGradient_sq_le
            representative N hx hh hmono hwidth)
      · exact Real.sqrt_nonneg _

/-- A two-phase defect sequence has zero unweighted total. -/
theorem twoPhase_zeroTotal (A : ℝ) (m : ℕ) :
    (∑ _j ∈ Finset.range m, A) +
      ∑ _j ∈ Finset.range m, -A = 0 := by
  simp

/-- Exact hostile transfer function.  Defects `+A` for `m` blocks followed by `-A` for `m`
blocks have zero total, but their geometric-weight current is
`A * (1 - r^m)^2 / (1 - r)` when `r ≠ 1`.  The denominator-free identity also covers `r = 1`.
-/
theorem twoPhase_geometricCurrent_transfer
    (A r : ℝ) (m : ℕ) :
    ((∑ j ∈ Finset.range m, A * r ^ j) +
        ∑ j ∈ Finset.range m, (-A) * r ^ (m + j)) * (1 - r) =
      A * (1 - r ^ m) ^ 2 := by
  let G := ∑ j ∈ Finset.range m, r ^ j
  have hpos : (∑ j ∈ Finset.range m, A * r ^ j) = A * G := by
    simp [G, Finset.mul_sum]
  have hneg : (∑ j ∈ Finset.range m, (-A) * r ^ (m + j)) =
      (-A * r ^ m) * G := by
    simp_rw [pow_add]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hG : G * (1 - r) = 1 - r ^ m := by
    exact geom_sum_mul_neg r m
  rw [hpos, hneg]
  calc
    (A * G + (-A * r ^ m) * G) * (1 - r) =
        A * (1 - r ^ m) * (G * (1 - r)) := by ring
    _ = A * (1 - r ^ m) ^ 2 := by rw [hG]; ring

/-- A nonconstant root-of-unity defect mode has exactly zero unweighted total. -/
theorem geometricDefectMode_zeroTotal
    {z : ℂ} {N : ℕ} (hz : z ≠ 1) (hroot : z ^ N = 1) :
    ∑ j ∈ Finset.range N, z ^ j = 0 := by
  rw [geom_sum_eq hz, hroot]
  simp

/-- Exact transfer function of one complex defect frequency against a geometric Gibbs mesh.
This is the algebraic core of the spectral square-root-wall countermodel. -/
theorem geometricDefectMode_weighted_transfer
    (A r z : ℂ) (N : ℕ) :
    (∑ j ∈ Finset.range N, A * (r * z) ^ j) * (1 - r * z) =
      A * (1 - (r * z) ^ N) := by
  rw [show (∑ j ∈ Finset.range N, A * (r * z) ^ j) =
      A * ∑ j ∈ Finset.range N, (r * z) ^ j by
        rw [Finset.mul_sum],
    mul_assoc, geom_sum_mul_neg]

end RHTower
