import GaloisForLFunctions.HTGeometry.CountableWeightedDiracLinftyEquiv
import GaloisForLFunctions.HTGeometry.OrderOneEnvelope
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import GaloisForLFunctions.RHTower.CanonicalProductGrowth
import GaloisForLFunctions.RHTower.CanonicalProductPredicateSplit
import GaloisForLFunctions.RHTower.SquarefreeDensityLowerBound
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import Mathlib.NumberTheory.Harmonic.Bounds

open Complex Filter Topology Metric Set
open scoped BigOperators ENNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section
set_option maxHeartbeats 2000000

/-- Bounded moving-zero displacement used by the unit-residue realization. -/
def canonicalZeroDisplacement (t : ℝ) : ℝ := (1 / 4 : ℝ) * Real.tanh t

/-- Strictly positive scalar speed of one moving canonical zero. -/
def canonicalZeroSpeed (t : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (1 / Real.cosh t ^ 2)

theorem canonicalZeroDisplacement_hasDerivAt (t : ℝ) :
    HasDerivAt canonicalZeroDisplacement (canonicalZeroSpeed t) t := by
  change HasDerivAt
    (fun s : ℝ => (1 / 4 : ℝ) * Real.tanh s)
    ((1 / 4 : ℝ) * (1 / Real.cosh t ^ 2)) t
  exact (_root_.HTGeometry.hasDerivAt_tanh t).const_mul (1 / 4 : ℝ)

theorem canonicalZeroSpeed_pos (t : ℝ) :
    0 < canonicalZeroSpeed t := by
  dsimp only [canonicalZeroSpeed]
  positivity

/-- The `n`th positive simple zero in the moving canonical divisor. -/
def movingCanonicalZero (θ : BoundedRealSequence) (n : ℕ) : ℝ :=
  (n : ℝ) + 1 + canonicalZeroDisplacement (θ n)

theorem movingCanonicalZero_coordinate_hasDerivAt
    (n : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (n : ℝ) + 1 + canonicalZeroDisplacement s)
      (canonicalZeroSpeed t) t :=
  (canonicalZeroDisplacement_hasDerivAt t).const_add ((n : ℝ) + 1)

theorem canonicalZeroDisplacement_mem_Ioo (t : ℝ) :
    canonicalZeroDisplacement t ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ) := by
  constructor
  · have h := Real.neg_one_lt_tanh t
    dsimp [canonicalZeroDisplacement]
    linarith
  · have h := Real.tanh_lt_one t
    dsimp [canonicalZeroDisplacement]
    linarith

theorem movingCanonicalZero_lower (θ : BoundedRealSequence) (n : ℕ) :
    (n : ℝ) + 3 / 4 < movingCanonicalZero θ n := by
  have h := (canonicalZeroDisplacement_mem_Ioo (θ n)).1
  rw [movingCanonicalZero]
  linarith

theorem movingCanonicalZero_upper (θ : BoundedRealSequence) (n : ℕ) :
    movingCanonicalZero θ n < (n : ℝ) + 5 / 4 := by
  have h := (canonicalZeroDisplacement_mem_Ioo (θ n)).2
  rw [movingCanonicalZero]
  linarith

theorem movingCanonicalZero_pos (θ : BoundedRealSequence) (n : ℕ) :
    0 < movingCanonicalZero θ n := by
  have h := movingCanonicalZero_lower θ n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem movingCanonicalZero_strictMono (θ : BoundedRealSequence) :
    StrictMono (movingCanonicalZero θ) := by
  intro n m hnm
  have hstep : n + 1 ≤ m := Nat.succ_le_iff.mpr hnm
  have hl := movingCanonicalZero_upper θ n
  have hr := movingCanonicalZero_lower θ m
  have hcast : (n : ℝ) + 5 / 4 ≤ (m : ℝ) + 3 / 4 := by
    have hstep' : ((n + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hstep
    push_cast at hstep'
    linarith
  linarith

theorem movingCanonicalZero_injective (θ : BoundedRealSequence) :
    Function.Injective (movingCanonicalZero θ) :=
  (movingCanonicalZero_strictMono θ).injective

theorem movingCanonicalZero_tendsto_atTop (θ : BoundedRealSequence) :
    Tendsto (movingCanonicalZero θ) atTop atTop := by
  exact Filter.tendsto_atTop_mono
    (fun n => (movingCanonicalZero_lower θ n).le)
    (tendsto_atTop_add_const_right atTop (3 / 4 : ℝ)
      tendsto_natCast_atTop_atTop)

private theorem summable_inv_nat_add_one_sq :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff
    (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hbase
  refine hshift.congr fun n => ?_
  push_cast
  ring

private theorem sum_range_inv_nat_add_one_eq_harmonic (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) =
      (harmonic N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, harmonic_succ]
      push_cast
      rw [ih]
      congr 1
      norm_num [div_eq_mul_inv]

private theorem tsum_inv_nat_add_one_sq_le_inv
    (N : ℕ) (hN : 1 ≤ N) :
    ∑' i : ℕ, (1 : ℝ) / (((i + N : ℕ) : ℝ) + 1) ^ 2 ≤
      1 / (N : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro M
  have h := RHTower.sum_Ico_one_div_sq_le
    (K := N + 1) (M := N + 1 + M) (by omega)
  rw [Finset.sum_Ico_eq_sum_range] at h
  have hsub : N + 1 + M - (N + 1) = M := by omega
  rw [hsub] at h
  simpa [add_assoc, add_comm, add_left_comm] using h

private theorem tsum_inv_nat_add_one_sq_le_two :
    ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 2 := by
  have hsplit := summable_inv_nat_add_one_sq.sum_add_tsum_nat_add 1
  have htail := tsum_inv_nat_add_one_sq_le_inv 1 (by omega)
  norm_num at hsplit htail ⊢
  linarith

private theorem movingCanonicalZero_linear_term_le
    (θ : BoundedRealSequence) (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    2 * r / ‖(movingCanonicalZero θ n : ℂ)‖ ≤
      4 * r / ((n : ℝ) + 1) := by
  have hl : ((n : ℝ) + 1) / 2 ≤
      ‖(movingCanonicalZero θ n : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (movingCanonicalZero_pos θ n)]
    have h := movingCanonicalZero_lower θ n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hden : 0 < ((n : ℝ) + 1) / 2 := by positivity
  have hinv : 1 / ‖(movingCanonicalZero θ n : ℂ)‖ ≤
      1 / (((n : ℝ) + 1) / 2) :=
    one_div_le_one_div_of_le hden hl
  calc
    2 * r / ‖(movingCanonicalZero θ n : ℂ)‖ =
        (2 * r) * (1 / ‖(movingCanonicalZero θ n : ℂ)‖) := by ring
    _ ≤ (2 * r) * (1 / (((n : ℝ) + 1) / 2)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 4 * r / ((n : ℝ) + 1) := by
      field_simp
      ; ring

private theorem movingCanonicalZero_quadratic_term_le
    (θ : BoundedRealSequence) (r : ℝ) (n : ℕ) :
    2 * r ^ 2 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2 ≤
      8 * r ^ 2 / ((n : ℝ) + 1) ^ 2 := by
  have hl : ((n : ℝ) + 1) / 2 ≤
      ‖(movingCanonicalZero θ n : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (movingCanonicalZero_pos θ n)]
    have h := movingCanonicalZero_lower θ n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsq : (((n : ℝ) + 1) / 2) ^ 2 ≤
      ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hl 2
  have hden : 0 < (((n : ℝ) + 1) / 2) ^ 2 := by positivity
  have hinv : 1 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2 ≤
      1 / (((n : ℝ) + 1) / 2) ^ 2 :=
    one_div_le_one_div_of_le hden hsq
  calc
    2 * r ^ 2 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2 =
        (2 * r ^ 2) * (1 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2) := by ring
    _ ≤ (2 * r ^ 2) * (1 / (((n : ℝ) + 1) / 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 8 * r ^ 2 / ((n : ℝ) + 1) ^ 2 := by
      field_simp
      ; ring

theorem movingCanonicalGrowthSeries_le_orderOneWeight
    (θ : BoundedRealSequence) (z : ℂ) :
    ∑' n, min
        (2 * ‖z‖ / ‖(movingCanonicalZero θ n : ℂ)‖)
        (2 * ‖z‖ ^ 2 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2) ≤
      orderOneWeight 32 z := by
  let r : ℝ := ‖z‖
  let u : ℕ → ℝ := fun n => min
    (2 * r / ‖(movingCanonicalZero θ n : ℂ)‖)
    (2 * r ^ 2 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2)
  have hr0 : 0 ≤ r := norm_nonneg z
  have hu : Summable u := by
    have hdom : Summable (fun n =>
        2 * r ^ 2 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2) := by
      have hmajor : Summable (fun n : ℕ =>
          8 * r ^ 2 / ((n : ℝ) + 1) ^ 2) := by
        refine summable_inv_nat_add_one_sq.mul_left (8 * r ^ 2) |>.congr
          (fun n => ?_)
        ring
      exact Summable.of_nonneg_of_le
        (fun n => by positivity)
        (movingCanonicalZero_quadratic_term_le θ r)
        hmajor
    exact Summable.of_nonneg_of_le
      (fun n => le_min (by positivity) (by positivity))
      (fun n => min_le_right _ _) hdom
  change ∑' n, u n ≤ orderOneWeight 32 z
  rw [orderOneWeight]
  by_cases hr : r < 1
  · have hquad : Summable (fun n : ℕ =>
        8 * r ^ 2 / ((n : ℝ) + 1) ^ 2) := by
      refine summable_inv_nat_add_one_sq.mul_left (8 * r ^ 2) |>.congr
        (fun n => ?_)
      ring
    have hle : ∑' n, u n ≤
        ∑' n : ℕ, 8 * r ^ 2 / ((n : ℝ) + 1) ^ 2 :=
      hu.tsum_le_tsum
        (fun n => (min_le_right _ _).trans
          (movingCanonicalZero_quadratic_term_le θ r n))
        hquad
    have hscale : ∑' n : ℕ, 8 * r ^ 2 / ((n : ℝ) + 1) ^ 2 ≤
        16 * r ^ 2 := by
      calc
        ∑' n : ℕ, 8 * r ^ 2 / ((n : ℝ) + 1) ^ 2 =
            8 * r ^ 2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          ring
        _ ≤ 8 * r ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left tsum_inv_nat_add_one_sq_le_two (by positivity)
        _ = 16 * r ^ 2 := by ring
    have hlog : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
      Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
    have hlog2 := Real.log_two_gt_d9
    dsimp [r] at hr hr0 hle hscale
    nlinarith [hle.trans hscale, sq_nonneg ‖z‖]
  · have hr1 : 1 ≤ r := le_of_not_gt hr
    let N : ℕ := ⌈r⌉₊
    have hN : 1 ≤ N := Nat.one_le_ceil_iff.mpr (by linarith)
    have hrN : r ≤ (N : ℝ) := Nat.le_ceil r
    have hNr : (N : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
    have hlog0 : 0 ≤ Real.log (2 + r) :=
      Real.log_nonneg (by linarith)
    have hlog2 : Real.log 2 ≤ Real.log (2 + r) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog2' := Real.log_two_gt_d9
    have hlogN : Real.log N ≤ Real.log (2 + r) := by
      apply Real.log_le_log
      · exact_mod_cast hN
      · linarith
    have hharm : (harmonic N : ℝ) ≤ 4 * Real.log (2 + r) := by
      have hh := harmonic_le_one_add_log N
      nlinarith
    have hhead : ∑ n ∈ Finset.range N, u n ≤
        16 * r * Real.log (2 + r) := by
      calc
        ∑ n ∈ Finset.range N, u n ≤
            ∑ n ∈ Finset.range N, 4 * r / ((n : ℝ) + 1) :=
          Finset.sum_le_sum fun n _ =>
            (min_le_left _ _).trans
              (movingCanonicalZero_linear_term_le θ r hr0 n)
        _ = 4 * r * (harmonic N : ℝ) := by
          rw [← sum_range_inv_nat_add_one_eq_harmonic]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          ring
        _ ≤ 4 * r * (4 * Real.log (2 + r)) :=
          mul_le_mul_of_nonneg_left hharm (by positivity)
        _ = 16 * r * Real.log (2 + r) := by ring
    have hutail : Summable (fun n => u (n + N)) :=
      (summable_nat_add_iff N).mpr hu
    have hqtail : Summable (fun n : ℕ =>
        8 * r ^ 2 / (((n + N : ℕ) : ℝ) + 1) ^ 2) := by
      have hbase : Summable (fun n : ℕ =>
          1 / (((n + N : ℕ) : ℝ) + 1) ^ 2) :=
        (summable_nat_add_iff N).mpr summable_inv_nat_add_one_sq
      refine hbase.mul_left (8 * r ^ 2) |>.congr (fun n => ?_)
      ring
    have htail : ∑' n, u (n + N) ≤ 8 * r := by
      have hcomp : ∑' n, u (n + N) ≤
          ∑' n : ℕ, 8 * r ^ 2 / (((n + N : ℕ) : ℝ) + 1) ^ 2 :=
        hutail.tsum_le_tsum
          (fun n => (min_le_right _ _).trans
            (movingCanonicalZero_quadratic_term_le θ r (n + N)))
          hqtail
      have hbase := tsum_inv_nat_add_one_sq_le_inv N hN
      have hscaled : ∑' n : ℕ,
          8 * r ^ 2 / (((n + N : ℕ) : ℝ) + 1) ^ 2 ≤
          8 * r ^ 2 * (1 / (N : ℝ)) := by
        calc
          ∑' n : ℕ, 8 * r ^ 2 / (((n + N : ℕ) : ℝ) + 1) ^ 2 =
              8 * r ^ 2 * ∑' n : ℕ,
                1 / (((n + N : ℕ) : ℝ) + 1) ^ 2 := by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro n
            ring
          _ ≤ 8 * r ^ 2 * (1 / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hbase (by positivity)
      have hinv : 1 / (N : ℝ) ≤ 1 / r :=
        one_div_le_one_div_of_le (by positivity) hrN
      calc
        ∑' n, u (n + N) ≤
            8 * r ^ 2 * (1 / (N : ℝ)) := hcomp.trans hscaled
        _ ≤ 8 * r ^ 2 * (1 / r) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 8 * r := by field_simp
    have hsplit := hu.sum_add_tsum_nat_add N
    have htotal : ∑' n, u n ≤
        16 * r * Real.log (2 + r) + 8 * r := by
      rw [← hsplit]
      exact add_le_add hhead htail
    dsimp [r] at htotal hr0 hr1 hlog0 hlog2 ⊢
    nlinarith [mul_nonneg (norm_nonneg z) hlog0]

theorem summable_movingCanonicalZero_inv_sq (θ : BoundedRealSequence) :
    Summable (fun n => 1 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2) := by
  have hmajor : Summable (fun n : ℕ => 4 / ((n : ℝ) + 1) ^ 2) :=
    by
      simpa [div_eq_mul_inv] using summable_inv_nat_add_one_sq.mul_left 4
  refine Summable.of_nonneg_of_le
    (fun n => by positivity) (fun n => ?_) hmajor
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (movingCanonicalZero_pos θ n)]
  have hl : ((n : ℝ) + 1) / 2 ≤ movingCanonicalZero θ n := by
    have h := movingCanonicalZero_lower θ n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hnp : 0 < (n : ℝ) + 1 := by positivity
  have hzp := movingCanonicalZero_pos θ n
  have hsq : (((n : ℝ) + 1) / 2) ^ 2 ≤
      (movingCanonicalZero θ n) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hl 2
  rw [div_le_iff₀ (sq_pos_of_pos hzp)]
  field_simp
  nlinarith [hsq]

/-- Exact exponent-one criterion for an enumerated nonzero divisor. -/
def HasExponentOfConvergenceOne (a : ℕ → ℂ) : Prop :=
  (∀ p : ℝ, 1 < p → Summable fun n => 1 / ‖a n‖ ^ p) ∧
    ¬Summable fun n => 1 / ‖a n‖

theorem movingCanonicalZero_hasExponentOfConvergenceOne
    (θ : BoundedRealSequence) :
    HasExponentOfConvergenceOne
      (fun n => (movingCanonicalZero θ n : ℂ)) := by
  constructor
  · intro p hp
    have hbase : Summable (fun n : ℕ =>
        1 / ((n : ℝ) + 1) ^ p) := by
      refine ((Real.summable_one_div_nat_add_rpow 1 p).mpr hp).congr
        (fun n => ?_)
      rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have hmajor : Summable (fun n : ℕ =>
        (2 : ℝ) ^ p / ((n : ℝ) + 1) ^ p) := by
      refine hbase.mul_left ((2 : ℝ) ^ p) |>.congr (fun n => ?_)
      ring
    apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmajor
    have hl : ((n : ℝ) + 1) / 2 ≤
        ‖(movingCanonicalZero θ n : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (movingCanonicalZero_pos θ n)]
      have h := movingCanonicalZero_lower θ n
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hhalf : 0 < ((n : ℝ) + 1) / 2 := by positivity
    have hpow : (((n : ℝ) + 1) / 2) ^ p ≤
        ‖(movingCanonicalZero θ n : ℂ)‖ ^ p :=
      Real.rpow_le_rpow hhalf.le hl (by linarith)
    calc
      1 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ p ≤
          1 / (((n : ℝ) + 1) / 2) ^ p :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hhalf p) hpow
      _ = (2 : ℝ) ^ p / ((n : ℝ) + 1) ^ p := by
        rw [Real.div_rpow (by positivity) (by norm_num)]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2) p)]
  · intro hsum
    have hminor : Summable (fun n : ℕ =>
        1 / (2 * ((n : ℝ) + 1))) := by
      apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
      have hu : ‖(movingCanonicalZero θ n : ℂ)‖ ≤
          2 * ((n : ℝ) + 1) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (movingCanonicalZero_pos θ n)]
        have h := movingCanonicalZero_upper θ n
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      exact one_div_le_one_div_of_le
        (norm_pos_iff.mpr (ofReal_ne_zero.mpr
          (ne_of_gt (movingCanonicalZero_pos θ n)))) hu
    have hharm : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
      refine hminor.mul_left 2 |>.congr (fun n => ?_)
      field_simp
    apply Real.not_summable_one_div_natCast
    exact (summable_nat_add_iff
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) 1).mp
        (by simpa using hharm)

/-- Genus-one canonical product with the exact moving unit-residue divisor. -/
def movingCanonicalProduct (θ : BoundedRealSequence) : ℂ → ℂ :=
  RHTower.canonicalProductE1Indexed
    (fun n => (movingCanonicalZero θ n : ℂ))

theorem movingCanonicalProduct_analytic (θ : BoundedRealSequence) :
    AnalyticOnNhd ℂ (movingCanonicalProduct θ) Set.univ := by
  exact RHTower.canonicalProductE1Indexed_analytic
    (fun n => (movingCanonicalZero θ n : ℂ))
    (fun n => ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos θ n)))
    (summable_movingCanonicalZero_inv_sq θ)

theorem movingCanonicalProduct_orderOneEnvelope (θ : BoundedRealSequence) :
    OrderOneEnvelope (movingCanonicalProduct θ) := by
  refine ⟨32, by norm_num, fun z => ?_⟩
  exact (RHTower.canonicalProductE1Indexed_norm_le_exp_min
    (fun n => (movingCanonicalZero θ n : ℂ))
    (fun n => ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos θ n)))
    (summable_movingCanonicalZero_inv_sq θ) z).trans
      (Real.exp_le_exp.mpr
        (movingCanonicalGrowthSeries_le_orderOneWeight θ z))

theorem movingCanonicalProduct_conj
    (θ : BoundedRealSequence) (z : ℂ) :
    movingCanonicalProduct θ (conj z) =
      conj (movingCanonicalProduct θ z) := by
  have hm : Multipliable (fun n =>
      RHTower.weierstrassE1
        (z / (movingCanonicalZero θ n : ℂ))) :=
    (RHTower.canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      (fun n => (movingCanonicalZero θ n : ℂ))
      (fun n => ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos θ n)))
      (summable_movingCanonicalZero_inv_sq θ)
      |>.multipliableLocallyUniformlyOn).multipliable (Set.mem_univ z)
  change (∏' n, RHTower.weierstrassE1
      (conj z / (movingCanonicalZero θ n : ℂ))) =
    Complex.conjAe (∏' n, RHTower.weierstrassE1
      (z / (movingCanonicalZero θ n : ℂ)))
  calc
    (∏' n, RHTower.weierstrassE1
        (conj z / (movingCanonicalZero θ n : ℂ))) =
        ∏' n, Complex.conjAe.toMonoidHom
          (RHTower.weierstrassE1
            (z / (movingCanonicalZero θ n : ℂ))) := by
      apply tprod_congr
      intro n
      change RHTower.weierstrassE1
          (conj z / (movingCanonicalZero θ n : ℂ)) =
        conj (RHTower.weierstrassE1
          (z / (movingCanonicalZero θ n : ℂ)))
      simp only [RHTower.weierstrassE1, map_mul, map_sub, map_one,
        map_div₀, Complex.conj_ofReal]
      rw [← Complex.exp_conj]
      rw [map_div₀, Complex.conj_ofReal]
    _ = Complex.conjAe.toMonoidHom
        (∏' n, RHTower.weierstrassE1
          (z / (movingCanonicalZero θ n : ℂ))) :=
      (hm.map_tprod Complex.conjAe.toMonoidHom
        Complex.continuous_conj).symm
    _ = _ := rfl

theorem movingCanonicalProduct_eq_zero_iff
    (θ : BoundedRealSequence) (z : ℂ) :
    movingCanonicalProduct θ z = 0 ↔
      ∃ n, z = (movingCanonicalZero θ n : ℂ) := by
  constructor
  · intro hz
    by_contra hnone
    have haway : ∀ n, z ≠ (movingCanonicalZero θ n : ℂ) := by
      intro n hn
      exact hnone ⟨n, hn⟩
    exact (RHTower.canonicalProductE1Indexed_ne_zero
      (fun n => (movingCanonicalZero θ n : ℂ))
      (fun n => ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos θ n)))
      (summable_movingCanonicalZero_inv_sq θ) haway) hz
  · rintro ⟨n, rfl⟩
    rw [movingCanonicalProduct, RHTower.canonicalProductE1Indexed]
    apply tprod_of_exists_eq_zero
    refine ⟨n, ?_⟩
    rw [RHTower.weierstrassE1,
      div_self (ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos θ n)))]
    simp

theorem movingCanonicalProduct_zero_analyticOrderAt
    (θ : BoundedRealSequence) (n : ℕ) :
    analyticOrderAt (movingCanonicalProduct θ)
      (movingCanonicalZero θ n : ℂ) = 1 := by
  let a : ℕ → ℂ := fun j => (movingCanonicalZero θ j : ℂ)
  let p : ℕ → Prop := fun j => j = n
  have ha : ∀ j, a j ≠ 0 :=
    fun j => ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos θ j))
  have hsum : Summable (fun j => 1 / ‖a j‖ ^ 2) :=
    summable_movingCanonicalZero_inv_sq θ
  have hsplit : movingCanonicalProduct θ =
      (fun z => RHTower.weierstrassE1 (z / a n)) *
        RHTower.canonicalProductE1IndexedComplement a p := by
    funext z
    rw [movingCanonicalProduct,
      RHTower.canonicalProductE1Indexed_eq_selected_mul_complement a p ha hsum]
    congr 1
    rw [RHTower.canonicalProductE1IndexedSelected,
      RHTower.canonicalProductE1Indexed]
    let e : Unit ≃ {j // p j} :=
      { toFun := fun _ => ⟨n, by simp [p]⟩
        invFun := fun _ => ()
        left_inv := by intro u; cases u; rfl
        right_inv := by
          intro j
          apply Subtype.ext
          exact j.2.symm }
    rw [← e.tprod_eq]
    simp [e]
  have hbaseAn : AnalyticAt ℂ (fun z => RHTower.weierstrassE1 (z / a n)) (a n) := by
    simp only [RHTower.weierstrassE1]
    fun_prop
  have hcompAn : AnalyticAt ℂ
      (RHTower.canonicalProductE1IndexedComplement a p) (a n) :=
    RHTower.canonicalProductE1IndexedComplement_analytic a p ha hsum
      (a n) (Set.mem_univ _)
  have hcompNe : RHTower.canonicalProductE1IndexedComplement a p (a n) ≠ 0 := by
    apply RHTower.canonicalProductE1IndexedComplement_ne_zero a p ha hsum
    rintro ⟨j, hj⟩ hzero
    apply hj
    dsimp [a] at hzero
    exact movingCanonicalZero_injective θ (ofReal_injective hzero.symm)
  rw [hsplit, analyticOrderAt_mul hbaseAn hcompAn,
    RHTower.weierstrassE1_div_analyticOrderAt (a n) (ha n),
    hcompAn.analyticOrderAt_eq_zero.mpr hcompNe]
  rfl

/-- Normally convergent negative logarithmic-derivative series. -/
def movingCanonicalLogDerivative (θ : BoundedRealSequence) (z : ℂ) : ℂ :=
  ∑' n, (((movingCanonicalZero θ n : ℂ) - z)⁻¹
    - (movingCanonicalZero θ n : ℂ)⁻¹)

theorem summable_movingCanonicalLogDerivative
    (θ : BoundedRealSequence) {z : ℂ}
    (hz : ∀ n, z ≠ (movingCanonicalZero θ n : ℂ)) :
    Summable (fun n => ((movingCanonicalZero θ n : ℂ) - z)⁻¹
      - (movingCanonicalZero θ n : ℂ)⁻¹) := by
  have hbase : Summable (fun n => 1 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2) :=
    summable_movingCanonicalZero_inv_sq θ
  let S : ℝ := 2 * ‖z‖ + 1
  have hS : 0 < S := by positivity
  have hev : ∀ᶠ n in atTop, S ≤ ‖(movingCanonicalZero θ n : ℂ)‖ := by
    have htend := hbase.tendsto_atTop_zero
    have hlt : ∀ᶠ n in atTop,
        1 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2 < 1 / S ^ 2 :=
      htend.eventually_lt_const (by positivity)
    filter_upwards [hlt] with n hn
    have hapos : 0 < ‖(movingCanonicalZero θ n : ℂ)‖ :=
      norm_pos_iff.mpr (ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos θ n)))
    have hsq : S ^ 2 < ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2 :=
      lt_of_one_div_lt_one_div (pow_pos hapos 2) hn
    exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)
  refine (hbase.mul_left (2 * ‖z‖)).of_norm_bounded_eventually ?_
  have hev' : ∀ᶠ n in cofinite, S ≤ ‖(movingCanonicalZero θ n : ℂ)‖ :=
    Nat.cofinite_eq_atTop ▸ hev
  filter_upwards [hev'] with n hn
  let a : ℂ := movingCanonicalZero θ n
  have ha : a ≠ 0 := ofReal_ne_zero.mpr
    (ne_of_gt (movingCanonicalZero_pos θ n))
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz n))
  have hhalf : ‖z‖ ≤ ‖a‖ / 2 := by
    dsimp [S] at hn
    linarith
  have hdiff : ‖a‖ / 2 ≤ ‖a - z‖ := by
    have hrev := norm_sub_norm_le a z
    linarith
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hdpos : 0 < ‖a - z‖ := norm_pos_iff.mpr haz
  rw [show (a - z)⁻¹ - a⁻¹ = z / (a * (a - z)) by field_simp [ha, haz]; ring]
  rw [norm_div, norm_mul]
  change ‖z‖ / (‖a‖ * ‖a - z‖) ≤
    2 * ‖z‖ * (1 / ‖a‖ ^ 2)
  by_cases hz0 : ‖z‖ = 0
  · simp [hz0]
  rw [div_le_iff₀ (mul_pos hapos hdpos)]
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hdiff (norm_nonneg a)]

theorem movingCanonicalLogDerivative_im_nonneg
    (θ : BoundedRealSequence) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (movingCanonicalLogDerivative θ z).im := by
  have hpole : ∀ n, z ≠ (movingCanonicalZero θ n : ℂ) := by
    intro n h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hsum := summable_movingCanonicalLogDerivative θ hpole
  rw [movingCanonicalLogDerivative, Complex.im_tsum hsum]
  apply tsum_nonneg
  intro n
  rw [Complex.sub_im, Complex.inv_im, Complex.inv_im]
  simp only [Complex.sub_im, ofReal_im, zero_sub, neg_neg, neg_zero,
    zero_div, sub_zero]
  exact div_nonneg hz.le (Complex.normSq_nonneg _)

theorem neg_logDeriv_movingCanonicalProduct_eq
    (θ : BoundedRealSequence) {z : ℂ}
    (hz : ∀ n, z ≠ (movingCanonicalZero θ n : ℂ)) :
    -logDeriv (movingCanonicalProduct θ) z =
      movingCanonicalLogDerivative θ z := by
  let a : ℕ → ℂ := fun n => movingCanonicalZero θ n
  have ha : ∀ n, a n ≠ 0 :=
    fun n => ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos θ n))
  have hsum : Summable (fun n => 1 / ‖a n‖ ^ 2) :=
    summable_movingCanonicalZero_inv_sq θ
  have hfac : ∀ n, RHTower.weierstrassE1 (z / a n) ≠ 0 := by
    intro n
    rw [RHTower.weierstrassE1]
    apply mul_ne_zero
    · intro hzero
      have hdiv : z / a n = 1 := (sub_eq_zero.mp hzero).symm
      apply hz n
      calc
        z = z / a n * a n := (div_mul_cancel₀ z (ha n)).symm
        _ = a n := by rw [hdiv, one_mul]
    · exact Complex.exp_ne_zero _
  have hlogs : Summable (fun n =>
      logDeriv (fun w : ℂ => RHTower.weierstrassE1 (w / a n)) z) := by
    apply (summable_movingCanonicalLogDerivative θ hz).neg.congr
    intro n
    have hd : a n - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz n))
    have hinv : (a n - z)⁻¹ - (a n)⁻¹ =
        z / ((a n - z) * a n) := by
      simpa only [sub_sub_cancel] using inv_sub_inv hd (ha n)
    change -((a n - z)⁻¹ - (a n)⁻¹) =
      logDeriv (fun w : ℂ => RHTower.weierstrassE1 (w / a n)) z
    rw [RHTower.logDeriv_weierstrassE1_div (ha n) (hz n)]
    rw [hinv, mul_comm (a n - z) (a n)]
    rw [← neg_div]
  have hprod : movingCanonicalProduct θ z ≠ 0 :=
    RHTower.canonicalProductE1Indexed_ne_zero a ha hsum hz
  have hlog := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
    hfac (by intro n; simp only [RHTower.weierstrassE1]; fun_prop)
    hlogs
    (RHTower.canonicalProductE1Indexed_hasProdLocallyUniformlyOn a ha hsum
      |>.multipliableLocallyUniformlyOn) hprod
  have hlog' : logDeriv (movingCanonicalProduct θ) z =
      ∑' n, logDeriv (fun w : ℂ =>
        RHTower.weierstrassE1 (w / a n)) z := by
    change logDeriv (fun w => ∏' n,
      RHTower.weierstrassE1 (w / (movingCanonicalZero θ n : ℂ))) z =
        ∑' n, logDeriv (fun w : ℂ =>
          RHTower.weierstrassE1 (w / a n)) z
    simpa [a] using hlog
  rw [hlog', movingCanonicalLogDerivative, ← tsum_neg]
  apply tsum_congr
  intro n
  have hd : a n - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz n))
  have hinv : (a n - z)⁻¹ - (a n)⁻¹ =
      z / ((a n - z) * a n) := by
    simpa only [sub_sub_cancel] using inv_sub_inv hd (ha n)
  change -logDeriv (fun w : ℂ => RHTower.weierstrassE1 (w / a n)) z =
    (a n - z)⁻¹ - (a n)⁻¹
  rw [RHTower.logDeriv_weierstrassE1_div (ha n) (hz n)]
  rw [hinv, mul_comm (a n - z) (a n)]
  rw [neg_div, neg_neg]

end

end GaloisForLFunctions.HTGeometry
