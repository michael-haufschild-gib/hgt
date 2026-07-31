import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Exact Blaschke localized-kernel laws

For `0 < a < 1`, the one-sided coefficient sequence

* `u(0) = -a`,
* `u(n + 1) = (1 - a²) aⁿ`

is the Taylor-coefficient sequence of the elementary Blaschke factor
`(z - a) / (1 - a z)`.

This file proves the geometric-series identities at the kernel core of the
associated bilateral convolution operator:

* exact `ℓ²` normalization;
* exact absolute overlap at every positive displacement;
* exact signed orthogonality at every positive displacement.

No finite-support approximation is used.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

set_option maxHeartbeats 1600000

/-- One-sided real coefficient sequence of the Blaschke factor
`(z - a) / (1 - a z)`. -/
def blaschkeLocalizedKernel (a : ℝ) : ℕ → ℝ
  | 0 => -a
  | n + 1 => (1 - a ^ 2) * a ^ n

/-- The squared Blaschke localized kernel is summable. -/
theorem blaschkeLocalizedKernel_sq_summable
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Summable (fun n : ℕ => blaschkeLocalizedKernel a n ^ 2) := by
  have ha2lt : a ^ 2 < 1 := by nlinarith
  have hs : Summable
      (fun n : ℕ => blaschkeLocalizedKernel a (n + 1) ^ 2) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg a) ha2lt).mul_left
      ((1 - a ^ 2) ^ 2)
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel]
    ring
  exact (summable_nat_add_iff 1).mp hs

/-- The Blaschke localized kernel has exact squared mass one. -/
theorem blaschkeLocalizedKernel_sq_tsum
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∑' n : ℕ, blaschkeLocalizedKernel a n ^ 2 = 1 := by
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have ha2lt : a ^ 2 < 1 := by nlinarith
  have hgeom : ∑' n : ℕ, (a ^ 2) ^ n = (1 - a ^ 2)⁻¹ :=
    tsum_geometric_of_lt_one ha2 ha2lt
  have hs : Summable
      (fun n : ℕ => blaschkeLocalizedKernel a (n + 1) ^ 2) := by
    have hg := (summable_geometric_of_lt_one ha2 ha2lt).mul_left
      ((1 - a ^ 2) ^ 2)
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel]
    ring
  rw [← hs.sum_add_tsum_nat_add']
  simp only [Finset.sum_range_one, blaschkeLocalizedKernel, neg_sq]
  rw [show (∑' n : ℕ, ((1 - a ^ 2) * a ^ n) ^ 2) =
      (1 - a ^ 2) ^ 2 * ∑' n : ℕ, (a ^ 2) ^ n by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [mul_pow]
    congr 1
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]]
  rw [hgeom]
  have hne : 1 - a ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- The absolute overlap of the localized kernel with every positive
translate is summable. -/
theorem blaschkeLocalizedKernel_abs_corr_succ_summable
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (r : ℕ) :
    Summable (fun m : ℕ =>
      |blaschkeLocalizedKernel a m| *
        |blaschkeLocalizedKernel a (m + (r + 1))|) := by
  have ha_nonneg : 0 ≤ a := ha0.le
  have h1ma2 : 0 ≤ 1 - a ^ 2 := by nlinarith
  have ha2lt : a ^ 2 < 1 := by nlinarith
  have hs : Summable (fun m : ℕ =>
      |blaschkeLocalizedKernel a (m + 1)| *
        |blaschkeLocalizedKernel a (m + 1 + (r + 1))|) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg a) ha2lt).mul_left
      ((1 - a ^ 2) ^ 2 * a ^ (r + 1))
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel, abs_of_nonneg
      (mul_nonneg h1ma2 (pow_nonneg ha_nonneg _))]
    rw [show (n + 1).add r = n + r + 1 by
      change n + 1 + r = n + r + 1
      omega]
    rw [show (a ^ 2) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring
  exact (summable_nat_add_iff 1).mp hs

/-- At displacement `r + 1`, the exact absolute overlap of the localized
kernel with its translate is `2 (1 - a²) a^(r + 1)`. -/
theorem blaschkeLocalizedKernel_abs_corr_succ
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (r : ℕ) :
    ∑' m : ℕ,
        |blaschkeLocalizedKernel a m| *
          |blaschkeLocalizedKernel a (m + (r + 1))| =
      2 * (1 - a ^ 2) * a ^ (r + 1) := by
  have ha_nonneg : 0 ≤ a := ha0.le
  have h1ma2 : 0 ≤ 1 - a ^ 2 := by nlinarith
  have ha2lt : a ^ 2 < 1 := by nlinarith
  have hgeom : ∑' n : ℕ, (a ^ 2) ^ n = (1 - a ^ 2)⁻¹ :=
    tsum_geometric_of_lt_one (sq_nonneg a) ha2lt
  have hs : Summable (fun m : ℕ =>
      |blaschkeLocalizedKernel a (m + 1)| *
        |blaschkeLocalizedKernel a (m + 1 + (r + 1))|) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg a) ha2lt).mul_left
      ((1 - a ^ 2) ^ 2 * a ^ (r + 1))
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel, abs_of_nonneg
      (mul_nonneg h1ma2 (pow_nonneg ha_nonneg _))]
    rw [show (n + 1).add r = n + r + 1 by
      change n + 1 + r = n + r + 1
      omega]
    rw [show (a ^ 2) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring
  rw [← hs.sum_add_tsum_nat_add']
  simp only [Finset.sum_range_one, blaschkeLocalizedKernel, abs_neg,
    abs_of_nonneg ha_nonneg]
  rw [abs_of_nonneg (mul_nonneg h1ma2 (pow_nonneg ha_nonneg _))]
  rw [show (∑' n : ℕ,
      |(1 - a ^ 2) * a ^ n| *
        |(1 - a ^ 2) * a ^ ((n + 1).add r)|) =
      ∑' n : ℕ,
        ((1 - a ^ 2) * a ^ n) *
          ((1 - a ^ 2) * a ^ (n + r + 1)) by
    apply tsum_congr
    intro n
    rw [abs_of_nonneg (mul_nonneg h1ma2 (pow_nonneg ha_nonneg _))]
    rw [abs_of_nonneg (mul_nonneg h1ma2 (pow_nonneg ha_nonneg _))]
    congr 2
    have hexp : (n + 1).add r = n + r + 1 := by
      change n + 1 + r = n + r + 1
      omega
    rw [hexp]]
  rw [show (∑' n : ℕ,
      ((1 - a ^ 2) * a ^ n) *
        ((1 - a ^ 2) * a ^ (n + r + 1))) =
      (1 - a ^ 2) ^ 2 * a ^ (r + 1) *
        ∑' n : ℕ, (a ^ 2) ^ n by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [show (a ^ 2) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring]
  rw [hgeom]
  have hne : 1 - a ^ 2 ≠ 0 := by nlinarith
  field_simp
  have hzero : Nat.add 0 r = r := Nat.zero_add r
  rw [hzero, pow_succ]
  ring

/-- Distinct positive translates of the Blaschke localized kernel are exactly
orthogonal. -/
theorem blaschkeLocalizedKernel_signed_corr_succ
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (r : ℕ) :
    ∑' m : ℕ,
        blaschkeLocalizedKernel a m *
          blaschkeLocalizedKernel a (m + (r + 1)) =
      0 := by
  have ha2lt : a ^ 2 < 1 := by nlinarith
  have hgeom : ∑' n : ℕ, (a ^ 2) ^ n = (1 - a ^ 2)⁻¹ :=
    tsum_geometric_of_lt_one (sq_nonneg a) ha2lt
  have hs : Summable (fun m : ℕ =>
      blaschkeLocalizedKernel a (m + 1) *
        blaschkeLocalizedKernel a (m + 1 + (r + 1))) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg a) ha2lt).mul_left
      ((1 - a ^ 2) ^ 2 * a ^ (r + 1))
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel]
    rw [show (n + 1).add r = n + r + 1 by
      change n + 1 + r = n + r + 1
      omega]
    rw [show (a ^ 2) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring
  rw [← hs.sum_add_tsum_nat_add']
  simp only [Finset.sum_range_one, blaschkeLocalizedKernel]
  rw [show (∑' n : ℕ,
      ((1 - a ^ 2) * a ^ n) *
        ((1 - a ^ 2) * a ^ ((n + 1).add r))) =
      ∑' n : ℕ,
        ((1 - a ^ 2) * a ^ n) *
          ((1 - a ^ 2) * a ^ (n + r + 1)) by
    apply tsum_congr
    intro n
    have hexp : (n + 1).add r = n + r + 1 := by
      change n + 1 + r = n + r + 1
      omega
    rw [hexp]]
  rw [show (∑' n : ℕ,
      ((1 - a ^ 2) * a ^ n) *
        ((1 - a ^ 2) * a ^ (n + r + 1))) =
      (1 - a ^ 2) ^ 2 * a ^ (r + 1) *
        ∑' n : ℕ, (a ^ 2) ^ n by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [show (a ^ 2) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring]
  rw [hgeom]
  have hne : 1 - a ^ 2 ≠ 0 := by nlinarith
  field_simp
  have hzero : Nat.add 0 r = r := Nat.zero_add r
  rw [hzero, pow_succ]
  ring

/-- The signed overlap with every positive translate is summable. -/
theorem blaschkeLocalizedKernel_signed_corr_succ_summable
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (r : ℕ) :
    Summable (fun m : ℕ =>
      blaschkeLocalizedKernel a m *
        blaschkeLocalizedKernel a (m + (r + 1))) := by
  have ha2lt : a ^ 2 < 1 := by nlinarith
  have hs : Summable (fun m : ℕ =>
      blaschkeLocalizedKernel a (m + 1) *
        blaschkeLocalizedKernel a (m + 1 + (r + 1))) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg a) ha2lt).mul_left
      ((1 - a ^ 2) ^ 2 * a ^ (r + 1))
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel]
    rw [show (n + 1).add r = n + r + 1 by
      change n + 1 + r = n + r + 1
      omega]
    rw [show (a ^ 2) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring
  exact (summable_nat_add_iff 1).mp hs

/-- Local spectral weight induced by one Blaschke-localized coordinate. -/
def blaschkeLocalizedWeight (a : ℝ) (n : ℕ) : ℝ :=
  blaschkeLocalizedKernel a n ^ 2

/-- The one-coordinate local spectral weights form a probability mass
function. -/
theorem blaschkeLocalizedWeight_tsum
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∑' n : ℕ, blaschkeLocalizedWeight a n = 1 :=
  blaschkeLocalizedKernel_sq_tsum a ha0 ha1

/-- Exact weight at the origin. -/
@[simp] theorem blaschkeLocalizedWeight_zero (a : ℝ) :
    blaschkeLocalizedWeight a 0 = a ^ 2 := by
  simp [blaschkeLocalizedWeight, blaschkeLocalizedKernel]

/-- Exact geometric local-weight tail. -/
theorem blaschkeLocalizedWeight_succ (a : ℝ) (n : ℕ) :
    blaschkeLocalizedWeight a (n + 1) =
      (1 - a ^ 2) ^ 2 * (a ^ 2) ^ n := by
  rw [blaschkeLocalizedWeight, blaschkeLocalizedKernel, mul_pow]
  congr 1
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]

/-- Bilateral Blaschke kernel, extended by zero on the negative integers. -/
def bilateralBlaschkeKernel (a : ℝ) : ℤ → ℝ
  | .ofNat n => blaschkeLocalizedKernel a n
  | .negSucc _ => 0

@[simp] theorem bilateralBlaschkeKernel_ofNat (a : ℝ) (n : ℕ) :
    bilateralBlaschkeKernel a (n : ℤ) =
      blaschkeLocalizedKernel a n := by
  rfl

@[simp] theorem bilateralBlaschkeKernel_negSucc (a : ℝ) (n : ℕ) :
    bilateralBlaschkeKernel a (.negSucc n) = 0 := by
  rfl

@[simp] theorem bilateralBlaschkeKernel_neg_nat_succ
    (a : ℝ) (n : ℕ) :
    bilateralBlaschkeKernel a (-((n : ℤ) + 1)) = 0 := by
  rw [show -((n : ℤ) + 1) = .negSucc n by omega]
  rfl

/-- The bilateral Blaschke kernel has exact squared mass one. -/
theorem bilateralBlaschkeKernel_sq_tsum
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∑' n : ℤ, bilateralBlaschkeKernel a n ^ 2 = 1 := by
  have hpos : Summable
      (fun n : ℕ => bilateralBlaschkeKernel a (n : ℤ) ^ 2) := by
    simpa only [bilateralBlaschkeKernel_ofNat] using
      blaschkeLocalizedKernel_sq_summable a ha0 ha1
  have hneg : Summable
      (fun n : ℕ => bilateralBlaschkeKernel a (-((n : ℤ) + 1)) ^ 2) := by
    have hfun :
        (fun n : ℕ =>
          bilateralBlaschkeKernel a (-((n : ℤ) + 1)) ^ 2) =
          (fun _n : ℕ => (0 : ℝ)) := by
      funext n
      rw [show -((n : ℤ) + 1) = .negSucc n by omega,
        bilateralBlaschkeKernel_negSucc]
      norm_num
    rw [hfun]
    exact summable_zero
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  rw [show (fun n : ℕ =>
      bilateralBlaschkeKernel a (-((n : ℤ) + 1)) ^ 2) =
      (fun _n : ℕ => (0 : ℝ)) by
    funext n
    rw [show -((n : ℤ) + 1) = .negSucc n by omega,
      bilateralBlaschkeKernel_negSucc]
    norm_num]
  simp only [bilateralBlaschkeKernel_ofNat,
    blaschkeLocalizedKernel_sq_tsum a ha0 ha1, tsum_zero, add_zero]

/-- Exact bilateral absolute overlap at every positive displacement. -/
theorem bilateralBlaschkeKernel_abs_corr_succ
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (r : ℕ) :
    ∑' m : ℤ,
        |bilateralBlaschkeKernel a m| *
          |bilateralBlaschkeKernel a (m + (r + 1))| =
      2 * (1 - a ^ 2) * a ^ (r + 1) := by
  let f : ℤ → ℝ := fun m =>
    |bilateralBlaschkeKernel a m| *
      |bilateralBlaschkeKernel a (m + (r + 1))|
  have hposfun :
      (fun m : ℕ => f (m : ℤ)) =
        (fun m : ℕ =>
          |blaschkeLocalizedKernel a m| *
            |blaschkeLocalizedKernel a (m + (r + 1))|) := by
    funext m
    simp only [f]
    rw [show (m : ℤ) + (r + 1) =
        ((m + (r + 1) : ℕ) : ℤ) by omega]
    rfl
  have hpos : Summable (fun m : ℕ => f (m : ℤ)) := by
    rw [hposfun]
    exact blaschkeLocalizedKernel_abs_corr_succ_summable a ha0 ha1 r
  have hnegfun :
      (fun m : ℕ => f (-((m : ℤ) + 1))) =
        (fun _m : ℕ => (0 : ℝ)) := by
    funext m
    simp only [f]
    rw [show -((m : ℤ) + 1) = .negSucc m by omega,
      bilateralBlaschkeKernel_negSucc, abs_zero, zero_mul]
  have hneg : Summable (fun m : ℕ => f (-((m : ℤ) + 1))) := by
    rw [hnegfun]
    exact summable_zero
  change ∑' m : ℤ, f m = _
  rw [tsum_of_nat_of_neg_add_one hpos hneg, hposfun, hnegfun,
    blaschkeLocalizedKernel_abs_corr_succ a ha0 ha1 r, tsum_zero, add_zero]

/-- Exact bilateral signed orthogonality at every positive displacement. -/
theorem bilateralBlaschkeKernel_signed_corr_succ
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (r : ℕ) :
    ∑' m : ℤ,
        bilateralBlaschkeKernel a m *
          bilateralBlaschkeKernel a (m + (r + 1)) =
      0 := by
  let f : ℤ → ℝ := fun m =>
    bilateralBlaschkeKernel a m *
      bilateralBlaschkeKernel a (m + (r + 1))
  have hposfun :
      (fun m : ℕ => f (m : ℤ)) =
        (fun m : ℕ =>
          blaschkeLocalizedKernel a m *
            blaschkeLocalizedKernel a (m + (r + 1))) := by
    funext m
    simp only [f]
    rw [show (m : ℤ) + (r + 1) =
        ((m + (r + 1) : ℕ) : ℤ) by omega]
    rfl
  have hpos : Summable (fun m : ℕ => f (m : ℤ)) := by
    rw [hposfun]
    exact blaschkeLocalizedKernel_signed_corr_succ_summable a ha0 ha1 r
  have hnegfun :
      (fun m : ℕ => f (-((m : ℤ) + 1))) =
        (fun _m : ℕ => (0 : ℝ)) := by
    funext m
    simp only [f]
    rw [show -((m : ℤ) + 1) = .negSucc m by omega,
      bilateralBlaschkeKernel_negSucc, zero_mul]
  have hneg : Summable (fun m : ℕ => f (-((m : ℤ) + 1))) := by
    rw [hnegfun]
    exact summable_zero
  change ∑' m : ℤ, f m = _
  rw [tsum_of_nat_of_neg_add_one hpos hneg, hposfun, hnegfun,
    blaschkeLocalizedKernel_signed_corr_succ a ha0 ha1 r, tsum_zero,
    add_zero]

end RHTower
