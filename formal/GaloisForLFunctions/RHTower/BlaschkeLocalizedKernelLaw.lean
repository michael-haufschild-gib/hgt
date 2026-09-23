import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
  | n + 1 => (1 - a ^ (2 : ℕ)) * a ^ n

/-- The squared Blaschke localized kernel is summable. -/
theorem blaschkeLocalizedKernel_sq_summable
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Summable (fun n : ℕ => blaschkeLocalizedKernel a n ^ (2 : ℕ)) := by
  have ha2lt : a ^ (2 : ℕ) < 1 := by nlinarith
  have hs : Summable
      (fun n : ℕ => blaschkeLocalizedKernel a (n + 1) ^ (2 : ℕ)) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg a) ha2lt).mul_left
      ((1 - a ^ (2 : ℕ)) ^ (2 : ℕ))
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel]
    ring
  exact (summable_nat_add_iff 1).mp hs

/-- The Blaschke localized kernel has exact squared mass one. -/
theorem blaschkeLocalizedKernel_sq_tsum
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∑' n : ℕ, blaschkeLocalizedKernel a n ^ (2 : ℕ) = 1 := by
  have ha2 : 0 ≤ a ^ (2 : ℕ) := sq_nonneg a
  have ha2lt : a ^ (2 : ℕ) < 1 := by nlinarith
  have hgeom : ∑' n : ℕ, (a ^ (2 : ℕ)) ^ n = (1 - a ^ (2 : ℕ))⁻¹ :=
    tsum_geometric_of_lt_one ha2 ha2lt
  have hs : Summable
      (fun n : ℕ => blaschkeLocalizedKernel a (n + 1) ^ (2 : ℕ)) := by
    have hg := (summable_geometric_of_lt_one ha2 ha2lt).mul_left
      ((1 - a ^ (2 : ℕ)) ^ (2 : ℕ))
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel]
    ring
  rw [← hs.sum_add_tsum_nat_add']
  simp only [Finset.sum_range_one, blaschkeLocalizedKernel, neg_sq]
  rw [show (∑' n : ℕ, ((1 - a ^ (2 : ℕ)) * a ^ n) ^ (2 : ℕ)) =
      (1 - a ^ (2 : ℕ)) ^ (2 : ℕ) * ∑' n : ℕ, (a ^ (2 : ℕ)) ^ n by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [mul_pow]
    congr 1
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]]
  rw [hgeom]
  have hne : 1 - a ^ (2 : ℕ) ≠ 0 := by nlinarith
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
  have h1ma2 : 0 ≤ 1 - a ^ (2 : ℕ) := by nlinarith
  have ha2lt : a ^ (2 : ℕ) < 1 := by nlinarith
  have hs : Summable (fun m : ℕ =>
      |blaschkeLocalizedKernel a (m + 1)| *
        |blaschkeLocalizedKernel a (m + 1 + (r + 1))|) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg a) ha2lt).mul_left
      ((1 - a ^ (2 : ℕ)) ^ (2 : ℕ) * a ^ (r + 1))
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel, abs_of_nonneg
      (mul_nonneg h1ma2 (pow_nonneg ha_nonneg _))]
    rw [show (n + 1).add r = n + r + 1 by
      change n + 1 + r = n + r + 1
      omega]
    rw [show (a ^ (2 : ℕ)) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
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
      2 * (1 - a ^ (2 : ℕ)) * a ^ (r + 1) := by
  have ha_nonneg : 0 ≤ a := ha0.le
  have h1ma2 : 0 ≤ 1 - a ^ (2 : ℕ) := by nlinarith
  have ha2lt : a ^ (2 : ℕ) < 1 := by nlinarith
  have hgeom : ∑' n : ℕ, (a ^ (2 : ℕ)) ^ n = (1 - a ^ (2 : ℕ))⁻¹ :=
    tsum_geometric_of_lt_one (sq_nonneg a) ha2lt
  have hs : Summable (fun m : ℕ =>
      |blaschkeLocalizedKernel a (m + 1)| *
        |blaschkeLocalizedKernel a (m + 1 + (r + 1))|) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg a) ha2lt).mul_left
      ((1 - a ^ (2 : ℕ)) ^ (2 : ℕ) * a ^ (r + 1))
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel, abs_of_nonneg
      (mul_nonneg h1ma2 (pow_nonneg ha_nonneg _))]
    rw [show (n + 1).add r = n + r + 1 by
      change n + 1 + r = n + r + 1
      omega]
    rw [show (a ^ (2 : ℕ)) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring
  rw [← hs.sum_add_tsum_nat_add']
  simp only [Finset.sum_range_one, blaschkeLocalizedKernel, abs_neg,
    abs_of_nonneg ha_nonneg]
  rw [abs_of_nonneg (mul_nonneg h1ma2 (pow_nonneg ha_nonneg _))]
  rw [show (∑' n : ℕ,
      |(1 - a ^ (2 : ℕ)) * a ^ n| *
        |(1 - a ^ (2 : ℕ)) * a ^ ((n + 1).add r)|) =
      ∑' n : ℕ,
        ((1 - a ^ (2 : ℕ)) * a ^ n) *
          ((1 - a ^ (2 : ℕ)) * a ^ (n + r + 1)) by
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
      ((1 - a ^ (2 : ℕ)) * a ^ n) *
        ((1 - a ^ (2 : ℕ)) * a ^ (n + r + 1))) =
      (1 - a ^ (2 : ℕ)) ^ (2 : ℕ) * a ^ (r + 1) *
        ∑' n : ℕ, (a ^ (2 : ℕ)) ^ n by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [show (a ^ (2 : ℕ)) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring]
  rw [hgeom]
  have hne : 1 - a ^ (2 : ℕ) ≠ 0 := by nlinarith
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
  have ha2lt : a ^ (2 : ℕ) < 1 := by nlinarith
  have hgeom : ∑' n : ℕ, (a ^ (2 : ℕ)) ^ n = (1 - a ^ (2 : ℕ))⁻¹ :=
    tsum_geometric_of_lt_one (sq_nonneg a) ha2lt
  have hs : Summable (fun m : ℕ =>
      blaschkeLocalizedKernel a (m + 1) *
        blaschkeLocalizedKernel a (m + 1 + (r + 1))) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg a) ha2lt).mul_left
      ((1 - a ^ (2 : ℕ)) ^ (2 : ℕ) * a ^ (r + 1))
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel]
    rw [show (n + 1).add r = n + r + 1 by
      change n + 1 + r = n + r + 1
      omega]
    rw [show (a ^ (2 : ℕ)) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring
  rw [← hs.sum_add_tsum_nat_add']
  simp only [Finset.sum_range_one, blaschkeLocalizedKernel]
  rw [show (∑' n : ℕ,
      ((1 - a ^ (2 : ℕ)) * a ^ n) *
        ((1 - a ^ (2 : ℕ)) * a ^ ((n + 1).add r))) =
      ∑' n : ℕ,
        ((1 - a ^ (2 : ℕ)) * a ^ n) *
          ((1 - a ^ (2 : ℕ)) * a ^ (n + r + 1)) by
    apply tsum_congr
    intro n
    have hexp : (n + 1).add r = n + r + 1 := by
      change n + 1 + r = n + r + 1
      omega
    rw [hexp]]
  rw [show (∑' n : ℕ,
      ((1 - a ^ (2 : ℕ)) * a ^ n) *
        ((1 - a ^ (2 : ℕ)) * a ^ (n + r + 1))) =
      (1 - a ^ (2 : ℕ)) ^ (2 : ℕ) * a ^ (r + 1) *
        ∑' n : ℕ, (a ^ (2 : ℕ)) ^ n by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [show (a ^ (2 : ℕ)) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring]
  rw [hgeom]
  have hne : 1 - a ^ (2 : ℕ) ≠ 0 := by nlinarith
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
  have ha2lt : a ^ (2 : ℕ) < 1 := by nlinarith
  have hs : Summable (fun m : ℕ =>
      blaschkeLocalizedKernel a (m + 1) *
        blaschkeLocalizedKernel a (m + 1 + (r + 1))) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg a) ha2lt).mul_left
      ((1 - a ^ (2 : ℕ)) ^ (2 : ℕ) * a ^ (r + 1))
    refine hg.congr ?_
    intro n
    simp only [blaschkeLocalizedKernel]
    rw [show (n + 1).add r = n + r + 1 by
      change n + 1 + r = n + r + 1
      omega]
    rw [show (a ^ (2 : ℕ)) ^ n = a ^ n * a ^ n by rw [pow_two, mul_pow]]
    rw [pow_add, pow_add]
    ring
  exact (summable_nat_add_iff 1).mp hs

/-- Local spectral weight induced by one Blaschke-localized coordinate. -/
def blaschkeLocalizedWeight (a : ℝ) (n : ℕ) : ℝ :=
  blaschkeLocalizedKernel a n ^ (2 : ℕ)

/-- The one-coordinate local spectral weights form a probability mass
function. -/
theorem blaschkeLocalizedWeight_tsum
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∑' n : ℕ, blaschkeLocalizedWeight a n = 1 :=
  blaschkeLocalizedKernel_sq_tsum a ha0 ha1

/-- Exact weight at the origin. -/
@[simp] theorem blaschkeLocalizedWeight_zero (a : ℝ) :
    blaschkeLocalizedWeight a 0 = a ^ (2 : ℕ) := by
  simp [blaschkeLocalizedWeight, blaschkeLocalizedKernel]

/-- Exact geometric local-weight tail. -/
theorem blaschkeLocalizedWeight_succ (a : ℝ) (n : ℕ) :
    blaschkeLocalizedWeight a (n + 1) =
      (1 - a ^ (2 : ℕ)) ^ (2 : ℕ) * (a ^ (2 : ℕ)) ^ n := by
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
    ∑' n : ℤ, bilateralBlaschkeKernel a n ^ (2 : ℕ) = 1 := by
  have hpos : Summable
      (fun n : ℕ => bilateralBlaschkeKernel a (n : ℤ) ^ (2 : ℕ)) := by
    simpa only [bilateralBlaschkeKernel_ofNat] using
      blaschkeLocalizedKernel_sq_summable a ha0 ha1
  have hneg : Summable
      (fun n : ℕ => bilateralBlaschkeKernel a (-((n : ℤ) + 1)) ^ (2 : ℕ)) := by
    have hfun :
        (fun n : ℕ =>
          bilateralBlaschkeKernel a (-((n : ℤ) + 1)) ^ (2 : ℕ)) =
          (fun _n : ℕ => (0 : ℝ)) := by
      funext n
      rw [show -((n : ℤ) + 1) = .negSucc n by omega,
        bilateralBlaschkeKernel_negSucc]
      norm_num
    rw [hfun]
    exact summable_zero
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  rw [show (fun n : ℕ =>
      bilateralBlaschkeKernel a (-((n : ℤ) + 1)) ^ (2 : ℕ)) =
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
      2 * (1 - a ^ (2 : ℕ)) * a ^ (r + 1) := by
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

/-! ## Exact local spectral depth and tail -/

/-- Positive logarithmic spacing between consecutive nonorigin Blaschke
local spectral weights. -/
def blaschkeSpectralSlope (a : ℝ) : ℝ :=
  -Real.log (a ^ (2 : ℕ))

/-- Logarithmic depth of the first nonorigin Blaschke local spectral
weight. -/
def blaschkeSpectralOffset (a : ℝ) : ℝ :=
  -2 * Real.log (1 - a ^ (2 : ℕ))

/-- Logarithmic depth of the nonorigin local weight indexed by `n`. -/
def blaschkeSpectralDepth (a : ℝ) (n : ℕ) : ℝ :=
  -Real.log (blaschkeLocalizedWeight a (n + 1))

/-- Every nonorigin Blaschke local spectral weight is strictly positive. -/
theorem blaschkeLocalizedWeight_succ_pos
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    0 < blaschkeLocalizedWeight a (n + 1) := by
  rw [blaschkeLocalizedWeight_succ]
  have ha2lt : a ^ (2 : ℕ) < 1 := by nlinarith
  positivity

/-- The logarithmic spacing of the geometric spectral tail is positive. -/
theorem blaschkeSpectralSlope_pos
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < blaschkeSpectralSlope a := by
  rw [blaschkeSpectralSlope]
  have ha2pos : 0 < a ^ (2 : ℕ) := sq_pos_of_pos ha0
  have ha2lt : a ^ (2 : ℕ) < 1 := by nlinarith
  linarith [Real.log_neg ha2pos ha2lt]

/-- The nonorigin local spectral depths form an exact arithmetic
progression. -/
theorem blaschkeSpectralDepth_eq_affine
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    blaschkeSpectralDepth a n =
      blaschkeSpectralOffset a + (n : ℝ) * blaschkeSpectralSlope a := by
  have hbase : 0 < 1 - a ^ (2 : ℕ) := by nlinarith
  rw [blaschkeSpectralDepth, blaschkeLocalizedWeight_succ,
    Real.log_mul (pow_ne_zero 2 hbase.ne')
      (pow_ne_zero n (sq_pos_of_pos ha0).ne'),
    Real.log_pow, Real.log_pow]
  simp only [blaschkeSpectralOffset, blaschkeSpectralSlope]
  push_cast
  ring

/-- Exact probability mass beyond the first `M` nonorigin coordinates. -/
theorem blaschkeLocalizedWeight_tail
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (M : ℕ) :
    ∑' n : ℕ, blaschkeLocalizedWeight a (n + M + 1) =
      (1 - a ^ (2 : ℕ)) * (a ^ (2 : ℕ)) ^ M := by
  have ha2nonneg : 0 ≤ a ^ (2 : ℕ) := sq_nonneg a
  have ha2lt : a ^ (2 : ℕ) < 1 := by nlinarith
  have hfun :
      (fun n : ℕ => blaschkeLocalizedWeight a (n + M + 1)) =
        (fun n : ℕ =>
          ((1 - a ^ (2 : ℕ)) ^ (2 : ℕ) * (a ^ (2 : ℕ)) ^ M) * (a ^ (2 : ℕ)) ^ n) := by
    funext n
    rw [show n + M + 1 = (n + M) + 1 by omega,
      blaschkeLocalizedWeight_succ, pow_add]
    ring
  rw [hfun, tsum_mul_left,
    tsum_geometric_of_lt_one ha2nonneg ha2lt]
  have hne : 1 - a ^ (2 : ℕ) ≠ 0 := ne_of_gt (sub_pos.mpr ha2lt)
  field_simp

/-- Integrated logarithmic depth of the first `M` nonorigin coordinates at
water level `L`. This definition is used only when those coordinates are
known to lie above the water line. -/
def blaschkeFiniteDepthEntropy (a L : ℝ) (M : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ n ∈ Finset.range M,
    (L - blaschkeSpectralDepth a n)

/-- Exact quadratic formula for finite integrated Blaschke spectral
depth. -/
theorem blaschkeFiniteDepthEntropy_eq
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (L : ℝ) (M : ℕ) :
    blaschkeFiniteDepthEntropy a L M =
      (1 / 2 : ℝ) *
        ((M : ℝ) * (L - blaschkeSpectralOffset a) -
          blaschkeSpectralSlope a * ((M : ℝ) * (M - 1) / 2)) := by
  rw [blaschkeFiniteDepthEntropy]
  simp_rw [blaschkeSpectralDepth_eq_affine a ha0 ha1]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  have hsum : ∀ K : ℕ,
      (∑ x ∈ Finset.range K, (x : ℝ)) =
        (K : ℝ) * (K - 1) / 2 := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  rw [hsum M]
  ring

/-- Number of geometric tail steps visible above logarithmic depth `L`.
This is defined only algebraically; the accompanying theorems state the
large-depth hypotheses under which it is the exact active radius. -/
def blaschkeActiveTailRadius (a L : ℝ) : ℕ :=
  ⌊(L - blaschkeSpectralOffset a) / blaschkeSpectralSlope a⌋₊

/-- The active Blaschke tail radius brackets logarithmic depth within one
exact spectral spacing. -/
theorem blaschkeActiveTailRadius_bracket
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {L : ℝ} (hL : blaschkeSpectralOffset a ≤ L) :
    blaschkeSpectralSlope a *
        (blaschkeActiveTailRadius a L : ℝ) ≤
      L - blaschkeSpectralOffset a ∧
    L - blaschkeSpectralOffset a <
      blaschkeSpectralSlope a *
        ((blaschkeActiveTailRadius a L : ℝ) + 1) := by
  have hrho : 0 < blaschkeSpectralSlope a :=
    blaschkeSpectralSlope_pos a ha0 ha1
  have hY : 0 ≤ L - blaschkeSpectralOffset a := sub_nonneg.mpr hL
  have hratio :
      0 ≤ (L - blaschkeSpectralOffset a) / blaschkeSpectralSlope a :=
    div_nonneg hY hrho.le
  have hfloor :
      (blaschkeActiveTailRadius a L : ℝ) ≤
        (L - blaschkeSpectralOffset a) / blaschkeSpectralSlope a := by
    exact Nat.floor_le hratio
  have hfloorUp :
      (L - blaschkeSpectralOffset a) / blaschkeSpectralSlope a <
        (blaschkeActiveTailRadius a L : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  constructor
  · have := (le_div_iff₀ hrho).mp hfloor
    nlinarith
  · have := (div_lt_iff₀ hrho).mp hfloorUp
    nlinarith

/-- A nonorigin Blaschke local mode is visible at logarithmic depth `L`
exactly when its tail index does not exceed the active radius. -/
theorem blaschkeSpectralDepth_le_iff_le_activeTailRadius
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {L : ℝ} (hL : blaschkeSpectralOffset a ≤ L) (n : ℕ) :
    blaschkeSpectralDepth a n ≤ L ↔
      n ≤ blaschkeActiveTailRadius a L := by
  have hrho : 0 < blaschkeSpectralSlope a :=
    blaschkeSpectralSlope_pos a ha0 ha1
  have hY : 0 ≤ L - blaschkeSpectralOffset a := sub_nonneg.mpr hL
  have hratio :
      0 ≤ (L - blaschkeSpectralOffset a) / blaschkeSpectralSlope a :=
    div_nonneg hY hrho.le
  rw [blaschkeSpectralDepth_eq_affine a ha0 ha1]
  constructor
  · intro hn
    apply (Nat.le_floor_iff hratio).mpr
    apply (le_div_iff₀ hrho).2
    nlinarith
  · intro hn
    have hn' :
        (n : ℝ) ≤
          (L - blaschkeSpectralOffset a) / blaschkeSpectralSlope a :=
      (Nat.le_floor_iff hratio).mp hn
    have := (le_div_iff₀ hrho).mp hn'
    nlinarith

/-- Exact integrated depth of the visible Blaschke coordinates. The origin
contributes its exceptional weight `a²`; the visible geometric tail ends at
`blaschkeActiveTailRadius`. -/
def blaschkeDepthWaterEntropy (a L : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (L - blaschkeSpectralSlope a) +
    blaschkeFiniteDepthEntropy a L
      (blaschkeActiveTailRadius a L + 1)

/-- Closed finite formula for integrated visible Blaschke depth. -/
theorem blaschkeDepthWaterEntropy_eq
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (L : ℝ) :
    blaschkeDepthWaterEntropy a L =
      (1 / 2 : ℝ) *
        ((L - blaschkeSpectralSlope a) +
          ((blaschkeActiveTailRadius a L : ℝ) + 1) *
            (L - blaschkeSpectralOffset a) -
          blaschkeSpectralSlope a *
            (((blaschkeActiveTailRadius a L : ℝ) + 1) *
              (blaschkeActiveTailRadius a L : ℝ) / 2)) := by
  rw [blaschkeDepthWaterEntropy,
    blaschkeFiniteDepthEntropy_eq a ha0 ha1]
  push_cast
  ring

/--
The visible-depth entropy has a quadratic leading term. The complete error
is explicit and linear in logarithmic depth; no asymptotic notation is used.
-/
theorem blaschkeDepthWaterEntropy_shifted_quadratic_bounds
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {L : ℝ}
    (hLtail : blaschkeSpectralOffset a ≤ L)
    (hLzero : blaschkeSpectralSlope a ≤ L) :
    (L - blaschkeSpectralOffset a) ^ (2 : ℕ) /
          (4 * blaschkeSpectralSlope a) ≤
        blaschkeDepthWaterEntropy a L ∧
      blaschkeDepthWaterEntropy a L ≤
        (L - blaschkeSpectralOffset a) ^ (2 : ℕ) /
            (4 * blaschkeSpectralSlope a) +
          (L - blaschkeSpectralSlope a) / 2 +
          (L - blaschkeSpectralOffset a) / 2 +
          blaschkeSpectralSlope a / 4 := by
  let rho : ℝ := blaschkeSpectralSlope a
  let c : ℝ := blaschkeSpectralOffset a
  let R : ℝ := (blaschkeActiveTailRadius a L : ℝ)
  let Y : ℝ := L - c
  let delta : ℝ := Y - rho * R
  let S : ℝ := (R + 1) * Y - rho * ((R + 1) * R / 2)
  have hrho : 0 < rho := by
    simpa only [rho] using blaschkeSpectralSlope_pos a ha0 ha1
  have hR : 0 ≤ R := by positivity
  have hY : 0 ≤ Y := by
    simpa only [Y, c] using sub_nonneg.mpr hLtail
  obtain ⟨hfloor, hfloorUp⟩ :=
    blaschkeActiveTailRadius_bracket a ha0 ha1 hLtail
  have hfloor' : rho * R ≤ Y := by
    simpa only [rho, R, Y, c] using hfloor
  have hfloorUp' : Y < rho * (R + 1) := by
    simpa only [rho, R, Y, c] using hfloorUp
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta]
    linarith
  have hdeltarho : delta < rho := by
    dsimp only [delta]
    nlinarith
  have hdeltaProduct : 0 ≤ delta * (2 * rho - delta) :=
    mul_nonneg hdelta0 (by linarith)
  have hRterm : 0 ≤ rho ^ (2 : ℕ) * R :=
    mul_nonneg (sq_nonneg rho) hR
  have hcoreLower : Y ^ (2 : ℕ) ≤ 2 * rho * S := by
    dsimp only [delta, S] at hdeltaProduct ⊢
    nlinarith
  have hcoreUpper :
      2 * rho * S ≤ Y ^ (2 : ℕ) + 2 * rho * Y + rho ^ (2 : ℕ) := by
    have hdeltaSq : 0 ≤ delta ^ (2 : ℕ) := sq_nonneg delta
    dsimp only [delta, S] at hdeltaSq ⊢
    nlinarith
  have hH :
      blaschkeDepthWaterEntropy a L =
        (1 / 2 : ℝ) * ((L - rho) + S) := by
    rw [blaschkeDepthWaterEntropy_eq a ha0 ha1 L]
    dsimp only [rho, c, R, Y, S]
    ring
  have hfourrho : 0 < 4 * rho := by positivity
  have htailLower : Y ^ (2 : ℕ) / (4 * rho) ≤ S / 2 := by
    have hdiv :=
      (div_le_div_iff_of_pos_right hfourrho).2 hcoreLower
    calc
      Y ^ (2 : ℕ) / (4 * rho) ≤ (2 * rho * S) / (4 * rho) := hdiv
      _ = S / 2 := by
        field_simp [hrho.ne']
        ring
  have htailUpper :
      S / 2 ≤ Y ^ (2 : ℕ) / (4 * rho) + Y / 2 + rho / 4 := by
    have hdiv :=
      (div_le_div_iff_of_pos_right hfourrho).2 hcoreUpper
    calc
      S / 2 = (2 * rho * S) / (4 * rho) := by
        field_simp [hrho.ne']
        ring
      _ ≤ (Y ^ (2 : ℕ) + 2 * rho * Y + rho ^ (2 : ℕ)) / (4 * rho) := hdiv
      _ = Y ^ (2 : ℕ) / (4 * rho) + Y / 2 + rho / 4 := by
        field_simp [hrho.ne']
        ring
  constructor
  · rw [hH]
    have horigin : 0 ≤ L - rho := by
      simpa only [rho] using sub_nonneg.mpr hLzero
    nlinarith
  · rw [hH]
    dsimp only [rho, c, Y] at htailUpper ⊢
    nlinarith

end RHTower
