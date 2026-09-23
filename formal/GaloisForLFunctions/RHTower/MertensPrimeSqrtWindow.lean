import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence
import GaloisForLFunctions.RHTower.WeightedEulerCoefficientSpaces

/-!
# Mertens mass in a square-root prime window

The explicit Mertens error bound forces at least half a logarithm of
prime-log mass between `sqrt N` and `N`, up to a fixed error.  This is the
finite lower-window infrastructure used by left-of-critical-line Euler
coefficient obstructions.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology

/-- Prime-log mass in the finite interval from `sqrt N` to `N`, written as a
difference of cumulative Mertens masses. -/
def mertensPrimeSqrtWindow (N : ℕ) : ℝ :=
  mertensPrimeWeightSum N - mertensPrimeWeightSum ⌊Real.sqrt (N : ℝ)⌋₊

/-- The square-root prime window has half the ambient logarithmic mass, up to
the explicit two-sided Mertens error. -/
theorem le_mertensPrimeSqrtWindow (N : ℕ) (hN : 4 ≤ N) :
    Real.log N / 2 - (2 * mertensPrimeWindowBound + 1) ≤ mertensPrimeSqrtWindow N := by
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      (by exact_mod_cast Nat.zero_le N)).2
    norm_num
    exact hN
  have hlow := (abs_le.mp (abs_mertensPrimeWeightSum_sub_log_le N (by omega))).1
  have hupp := (abs_le.mp (abs_mertensPrimeWeightSum_floor_sub_log_le hsqrt)).2
  rw [Real.log_sqrt (by exact_mod_cast Nat.zero_le N)] at hupp
  unfold mertensPrimeSqrtWindow
  linarith

/-- A nonnegative prime power dominates the square-root-window mass by its
value at the lower endpoint. -/
theorem primeLogMass_rpow_lower_mertensPrimeSqrtWindow {δ : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ) (hN : 4 ≤ N) :
    (Real.sqrt (N : ℝ)) ^ δ * mertensPrimeSqrtWindow N ≤
      primeLogMass_weightedEulerCoefficientSpaces (fun n => (n : ℝ) ^ δ) N := by
  set Q : ℕ := ⌊Real.sqrt (N : ℝ)⌋₊ with hQ
  have hN1 : 1 ≤ N := by omega
  have hsqrtle : Real.sqrt (N : ℝ) ≤ N := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact_mod_cast Nat.zero_le N
    · have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      nlinarith
  have hQN : Q ≤ N := by
    have hQNreal : (Q : ℝ) ≤ N := by
      rw [hQ]
      exact le_trans (Nat.floor_le (Real.sqrt_nonneg _)) hsqrtle
    exact_mod_cast hQNreal
  have hwindow :
      mertensPrimeSqrtWindow N = primeLogMass_weightedEulerCoefficientSpaces (primeCoefficientTail (fun _ => (1 : ℝ)) Q) N := by
    change mertensPrimeWeightSum N - mertensPrimeWeightSum Q = _
    rw [primeLogMass_tail_eq_sub _ hQN, primeLogMass_unit N, primeLogMass_unit Q,
      ← mertensPrimeWeightSum_eq N, ← mertensPrimeWeightSum_eq Q]
  rw [hwindow, primeLogMass_tail, primeLogMass_weightedEulerCoefficientSpaces, Finset.mul_sum]
  calc
    ∑ n ∈ Finset.Icc 1 N with (n.Prime ∧ Q < n),
        (Real.sqrt (N : ℝ)) ^ δ * (Real.log n / n * |(1 : ℝ)|)
      ≤ ∑ n ∈ Finset.Icc 1 N with (n.Prime ∧ Q < n),
          Real.log n / n * |(n : ℝ) ^ δ| := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_filter] at hn
        have hnroot : Real.sqrt (N : ℝ) < n := by
          exact (Nat.floor_lt (Real.sqrt_nonneg _)).mp hn.2.2
        have hpow : (Real.sqrt (N : ℝ)) ^ δ ≤ (n : ℝ) ^ δ :=
          Real.rpow_le_rpow (Real.sqrt_nonneg _) hnroot.le hδ
        have hweight : 0 ≤ Real.log n / n :=
          div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
        rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
        simp only [abs_one]
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_right hpow hweight
    _ ≤ ∑ n ∈ Finset.Icc 1 N with n.Prime, Real.log n / n * |(n : ℝ) ^ δ| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_filter] at hn ⊢
          exact ⟨hn.1, hn.2.1⟩
        · intro n _ _
          exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n))
            (abs_nonneg _)

/-- The square-root window differs from half a logarithm by a fixed explicit
error. -/
theorem abs_mertensPrimeSqrtWindow_sub_half_log_le (N : ℕ) (hN : 4 ≤ N) :
    |mertensPrimeSqrtWindow N - Real.log N / 2| ≤ 2 * mertensPrimeWindowBound + 1 := by
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      (by exact_mod_cast Nat.zero_le N)).2
    norm_num
    exact hN
  have hNerr := abs_mertensPrimeWeightSum_sub_log_le N (by omega)
  have hQerr := abs_mertensPrimeWeightSum_floor_sub_log_le hsqrt
  rw [Real.log_sqrt (by exact_mod_cast Nat.zero_le N)] at hQerr
  calc
    |mertensPrimeSqrtWindow N - Real.log N / 2| =
        |(mertensPrimeWeightSum N - Real.log N) -
          (mertensPrimeWeightSum ⌊Real.sqrt (N : ℝ)⌋₊ - Real.log N / 2)| := by
            unfold mertensPrimeSqrtWindow
            ring_nf
    _ ≤ |mertensPrimeWeightSum N - Real.log N| +
          |mertensPrimeWeightSum ⌊Real.sqrt (N : ℝ)⌋₊ - Real.log N / 2| := abs_sub _ _
    _ ≤ mertensPrimeWindowBound + (mertensPrimeWindowBound + 1) :=
      add_le_add hNerr hQerr
    _ = 2 * mertensPrimeWindowBound + 1 := by ring

/-- The normalized square-root prime window converges to its Lebesgue mass
`1 / 2`. -/
theorem tendsto_mertensPrimeSqrtWindow_div_log :
    Tendsto (fun N : ℕ => mertensPrimeSqrtWindow N / Real.log N) atTop (nhds (1 / 2)) := by
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun N : ℕ => (2 * mertensPrimeWindowBound + 1) / Real.log N)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogtop
  have hzero : Tendsto (fun N : ℕ =>
      (mertensPrimeSqrtWindow N - Real.log N / 2) / Real.log N) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [Filter.eventually_ge_atTop 4] with N hN
    have hlog : 0 < Real.log N := log_cutoff_pos (by omega)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right
      (abs_mertensPrimeSqrtWindow_sub_half_log_le N hN) hlog.le
  have hsum := hzero.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2)))
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  have hlog : Real.log N ≠ 0 := (log_cutoff_pos hN).ne'
  field_simp
  ring

/-- Positive prime-power coefficient fields escape every logarithmic
Marcinkiewicz bound. -/
theorem tendsto_marcinkiewiczLogQuotient_rpow_atTop {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => marcinkiewiczLogQuotient (fun n => (n : ℝ) ^ δ) N) atTop atTop := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hrpow : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ)) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp hsqrt
  have hbase : Tendsto (fun N : ℕ => (1 / 4 : ℝ) * (Real.sqrt (N : ℝ)) ^ δ)
      atTop atTop := hrpow.const_mul_atTop (by norm_num)
  refine Filter.tendsto_atTop_mono' atTop ?_ hbase
  have hwindow : ∀ᶠ N : ℕ in atTop,
      (1 / 4 : ℝ) ≤ mertensPrimeSqrtWindow N / Real.log N :=
    tendsto_mertensPrimeSqrtWindow_div_log.eventually
      (eventually_ge_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))
  filter_upwards [Filter.eventually_ge_atTop 4, hwindow] with N hN hwindow
  have hlog : 0 < Real.log N := log_cutoff_pos (by omega)
  have hmass := primeLogMass_rpow_lower_mertensPrimeSqrtWindow hδ.le N hN
  unfold marcinkiewiczLogQuotient
  calc
    (1 / 4 : ℝ) * (Real.sqrt (N : ℝ)) ^ δ
      ≤ (Real.sqrt (N : ℝ)) ^ δ * (mertensPrimeSqrtWindow N / Real.log N) := by
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left hwindow
            (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    _ = ((Real.sqrt (N : ℝ)) ^ δ * mertensPrimeSqrtWindow N) / Real.log N := by ring
    _ ≤ primeLogMass_weightedEulerCoefficientSpaces (fun n => (n : ℝ) ^ δ) N / Real.log N :=
      div_le_div_of_nonneg_right hmass hlog.le

end RHTower

end
