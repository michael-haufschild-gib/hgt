import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheMaxKernelFormOfTheDampingAutocorrelation

/-!
# The exact pronic cost of a capped row

The square energy of `min(n,k)` is `2k-H_k-k²/(T+1)` for `T>=k`.
Its limiting value is the sharp uniform envelope for additive defects of
prefixes whose increments occupy an interval of width one. A hinge attains it.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

/-- The total pronic square mass of a linear row capped at length `k`. -/
def cappedLinearCost (k : ℕ) : ℝ :=
  2 * (k : ℝ) - ∑ n ∈ Icc 1 k, 1 / (n : ℝ)

theorem sum_pronic_linear_head (k : ℕ) :
    (∑ n ∈ Icc 1 k, (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
      (k : ℝ) - (∑ n ∈ Icc 1 k, 1 / (n : ℝ)) + 1 - 1 / ((k : ℝ) + 1) := by
  have hcell (n : ℕ) (hn : n ∈ Icc 1 k) :
      (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
        1 - 1 / (n : ℝ) + 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    field_simp [hn0.ne', (by positivity : (n : ℝ) + 1 ≠ 0)]
    ring
  rw [sum_congr rfl hcell, sum_add_distrib, sum_sub_distrib,
    sum_Icc_pronic_tail_mass (N := 1) (by omega) (by omega)]
  simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel,
    Nat.cast_one, one_div_one, mul_one]
  ring

/-- The omitted horizon tail is exactly `k²/(T+1)`. -/
theorem pronicNorm_cappedLinear_sq_eq {k T : ℕ} (hkT : k ≤ T) :
    pronicNorm T (fun n => ((min n k : ℕ) : ℝ)) ^ 2 =
      cappedLinearCost k - (k : ℝ) ^ 2 / ((T : ℝ) + 1) := by
  have hsplit : Icc 1 T = Icc 1 k ∪ Icc (k + 1) T := by
    ext n
    simp only [mem_Icc, mem_union]
    omega
  have hdisj : Disjoint (Icc 1 k) (Icc (k + 1) T) := by
    rw [disjoint_left]
    intro n hn hn'
    have h1 := (mem_Icc.mp hn).2
    have h2 := (mem_Icc.mp hn').1
    omega
  rw [pronicNorm_sq, hsplit, sum_union hdisj]
  have hleft : (∑ n ∈ Icc 1 k,
      ((min n k : ℕ) : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ n ∈ Icc 1 k, (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    exact sum_congr rfl fun n hn => by rw [min_eq_left (mem_Icc.mp hn).2]
  have hright : (∑ n ∈ Icc (k + 1) T,
      ((min n k : ℕ) : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
      (k : ℝ) ^ 2 * (1 / ((k : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    calc
      _ = (k : ℝ) ^ 2 * ∑ n ∈ Icc (k + 1) T,
          1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        rw [mul_sum]
        exact sum_congr rfl fun n hn => by
          rw [min_eq_right (by have := (mem_Icc.mp hn).1; omega)]
          ring
      _ = _ := by
        rw [sum_Icc_pronic_tail_mass (by omega) (by omega)]
        simp only [Nat.cast_add, Nat.cast_one]
  rw [hleft, hright, sum_pronic_linear_head, cappedLinearCost]
  have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hk0, (by positivity : (T : ℝ) + 1 ≠ 0)]
  ring

/-- The exact infinite envelope uniformly bounds every truncated horizon. -/
theorem pronicNorm_cappedLinear_sq_le_cost (k T : ℕ) :
    pronicNorm T (fun n => ((min n k : ℕ) : ℝ)) ^ 2 ≤ cappedLinearCost k := by
  have hmono : pronicNorm T (fun n => ((min n k : ℕ) : ℝ)) ^ 2 ≤
      pronicNorm (max k T) (fun n => ((min n k : ℕ) : ℝ)) ^ 2 := by
    rw [pronicNorm_sq, pronicNorm_sq]
    exact sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc le_rfl (le_max_right k T)) (fun n _ _ => by positivity)
  rw [pronicNorm_cappedLinear_sq_eq (le_max_left k T)] at hmono
  exact hmono.trans (sub_le_self _ (by positivity))

theorem cappedLinearCost_le_two_mul (k : ℕ) : cappedLinearCost k ≤ 2 * (k : ℝ) := by
  exact sub_le_self _ (sum_nonneg fun n _ => by positivity)

/-- The linear upper bound is the sharp envelope with its harmonic saving discarded. -/
theorem pronicNorm_cappedLinear_sq_le (k T : ℕ) :
    pronicNorm T (fun n => ((min n k : ℕ) : ℝ)) ^ 2 ≤ 2 * (k : ℝ) :=
  (pronicNorm_cappedLinear_sq_le_cost k T).trans (cappedLinearCost_le_two_mul k)

/-- Truncation approaches the exact cap cost, so no smaller uniform constant works. -/
theorem tendsto_pronicNorm_cappedLinear_sq (k : ℕ) :
    Tendsto (fun T => pronicNorm T (fun n => ((min n k : ℕ) : ℝ)) ^ 2)
      atTop (𝓝 (cappedLinearCost k)) := by
  have hdiv : Tendsto (fun T : ℕ => (k : ℝ) ^ 2 / ((T + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hlim := (tendsto_const_nhds (x := cappedLinearCost k)).sub hdiv
  simp only [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop k] with T hT
  simpa only [Nat.cast_add, Nat.cast_one] using (pronicNorm_cappedLinear_sq_eq hT).symm

/-- A hinge prefix has increments in the unit interval and attains the cap envelope. -/
def hingePrefix (k n : ℕ) : ℝ := (n - k : ℕ)

theorem hingePrefix_increment (k n : ℕ) :
    0 ≤ hingePrefix k (n + 1) - hingePrefix k n ∧
      hingePrefix k (n + 1) - hingePrefix k n ≤ 1 := by
  unfold hingePrefix
  have h0 : n - k ≤ n + 1 - k := by omega
  have h1 : n + 1 - k ≤ (n - k) + 1 := by omega
  have h0' : ((n - k : ℕ) : ℝ) ≤ (n + 1 - k : ℕ) := by exact_mod_cast h0
  have h1' : ((n + 1 - k : ℕ) : ℝ) ≤ (n - k : ℕ) + 1 := by exact_mod_cast h1
  constructor <;> linarith only [h0', h1']

theorem hingePrefix_additiveDefect (k n : ℕ) :
    hingePrefix k (n + k) - hingePrefix k n - hingePrefix k k = (min n k : ℕ) := by
  unfold hingePrefix
  rw [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero, sub_zero]
  by_cases hnk : n ≤ k
  · rw [Nat.sub_eq_zero_of_le hnk, Nat.cast_zero, sub_zero, min_eq_left hnk]
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hnk)),
      Nat.cast_sub (le_of_lt (lt_of_not_ge hnk))]
    ring

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

