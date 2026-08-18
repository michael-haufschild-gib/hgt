import Mathlib

/-!
# Truncated powers and repeated integration of a jump

The normalized truncated power `truncPow c j t = (t - c)_+^j / j!` is the `j`-fold antiderivative,
based at any point left of `c`, of the unit jump at `c`.  Repeated integration therefore acts on the
family by `j ↦ j + 1`, and a finite superposition of jumps — a summatory profile — integrates to the
same superposition one level up.  This is the exact form in which the arithmetic part of an
Andersson-type recursion propagates: `j`-fold integration of `∑_{p ≤ x} a_p` is
`∑_{p ≤ x} a_p (x - p)^j / j!`.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The normalized truncated power `(t - c)_+^j / j!`, the `j`-fold antiderivative of the unit
jump at `c`. -/
def truncPow (c : ℝ) (j : ℕ) : ℝ → ℝ :=
  Set.indicator (Set.Ici c) (fun t => (t - c) ^ j / (j.factorial : ℝ))

theorem truncPow_of_le {c t : ℝ} (h : c ≤ t) (j : ℕ) :
    truncPow c j t = (t - c) ^ j / (j.factorial : ℝ) :=
  Set.indicator_of_mem h _

theorem truncPow_of_lt {c t : ℝ} (h : t < c) (j : ℕ) : truncPow c j t = 0 :=
  Set.indicator_of_notMem (by simpa using h) _

theorem truncPow_zero_step {c t : ℝ} : truncPow c 0 t = if c ≤ t then 1 else 0 := by
  classical
  by_cases h : c ≤ t
  · rw [truncPow_of_le h, if_pos h]
    simp
  · rw [truncPow_of_lt (lt_of_not_ge h), if_neg h]

theorem measurable_truncPow (c : ℝ) (j : ℕ) : Measurable (truncPow c j) := by
  refine Measurable.indicator ?_ measurableSet_Ici
  fun_prop

theorem abs_truncPow_le {c : ℝ} {j : ℕ} {M t : ℝ} (hM : |t - c| ≤ M) (hM0 : 0 ≤ M) :
    |truncPow c j t| ≤ M ^ j / (j.factorial : ℝ) := by
  have hfac : (0:ℝ) < (j.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos j
  by_cases h : c ≤ t
  · rw [truncPow_of_le h, abs_div, abs_of_pos hfac, abs_pow]
    have h1 : |t - c| ^ j ≤ M ^ j := pow_le_pow_left₀ (abs_nonneg _) hM j
    exact div_le_div_of_nonneg_right h1 hfac.le
  · rw [truncPow_of_lt (lt_of_not_ge h), abs_zero]
    positivity

theorem intervalIntegrable_truncPow (c : ℝ) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (truncPow c j) volume a b := by
  rw [intervalIntegrable_iff]
  have hM0 : (0:ℝ) ≤ |a| + |b| + |c| := by positivity
  have hconst : IntegrableOn (fun _ : ℝ => (|a| + |b| + |c|) ^ j / (j.factorial : ℝ))
      (Set.uIoc a b) := by
    refine MeasureTheory.integrableOn_const ?_ ?_
    · rw [Set.uIoc]
      exact measure_Ioc_lt_top.ne
    · simp
  refine MeasureTheory.Integrable.mono' hconst
    (measurable_truncPow c j).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
  have hlow : a ⊓ b < t := ht.1
  have hhigh : t ≤ a ⊔ b := ht.2
  have habs : |t| ≤ |a| + |b| := by
    rcases le_total a b with hab | hab
    · rw [inf_eq_left.2 hab] at hlow
      rw [sup_eq_right.2 hab] at hhigh
      have h1 := le_abs_self a
      have h2 := le_abs_self b
      have h3 := neg_abs_le a
      have h4 := neg_abs_le b
      have h5 := abs_nonneg a
      have h6 := abs_nonneg b
      rw [abs_le]
      constructor <;> linarith
    · rw [inf_eq_right.2 hab] at hlow
      rw [sup_eq_left.2 hab] at hhigh
      have h1 := le_abs_self a
      have h2 := le_abs_self b
      have h3 := neg_abs_le a
      have h4 := neg_abs_le b
      have h5 := abs_nonneg a
      have h6 := abs_nonneg b
      rw [abs_le]
      constructor <;> linarith
  have hbound : |t - c| ≤ |a| + |b| + |c| := by
    have := abs_sub_abs_le_abs_sub t c
    have h1 : |t - c| ≤ |t| + |c| := abs_sub t c
    linarith
  exact abs_truncPow_le hbound hM0

/-- Repeated integration raises the level of a truncated power. -/
theorem integral_truncPow {c y : ℝ} (hc : 1 ≤ c) (hy : 1 ≤ y) (j : ℕ) :
    (∫ t in (1:ℝ)..y, truncPow c j t) = truncPow c (j + 1) y := by
  have hne : ∀ᵐ t : ℝ, t ≠ c := by
    have h0 : volume ({c} : Set ℝ) = 0 := measure_singleton c
    have hmem := MeasureTheory.compl_mem_ae_iff.2 h0
    filter_upwards [hmem] with t ht
    simpa using ht
  rcases le_or_gt y c with hyc | hyc
  · have hzero : (∫ t in (1:ℝ)..y, truncPow c j t) = ∫ t in (1:ℝ)..y, (0:ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hne] with t htne ht
      have hty : t ≤ y := by
        rw [Set.uIoc_of_le hy] at ht
        exact ht.2
      exact truncPow_of_lt (lt_of_le_of_ne (le_trans hty hyc) htne) j
    rw [hzero, intervalIntegral.integral_zero]
    rcases eq_or_lt_of_le hyc with heq | hlt
    · rw [truncPow_of_le (le_of_eq heq.symm)]
      rw [heq]
      simp
    · exact (truncPow_of_lt hlt (j + 1)).symm
  · have hsplit : (∫ t in (1:ℝ)..y, truncPow c j t)
        = (∫ t in (1:ℝ)..c, truncPow c j t) + ∫ t in c..y, truncPow c j t :=
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_truncPow c j 1 c) (intervalIntegrable_truncPow c j c y)).symm
    have hleft : (∫ t in (1:ℝ)..c, truncPow c j t) = 0 := by
      have : (∫ t in (1:ℝ)..c, truncPow c j t) = ∫ t in (1:ℝ)..c, (0:ℝ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hne] with t htne ht
        have htc : t ≤ c := by
          rw [Set.uIoc_of_le hc] at ht
          exact ht.2
        exact truncPow_of_lt (lt_of_le_of_ne htc htne) j
      rw [this, intervalIntegral.integral_zero]
    have hright : (∫ t in c..y, truncPow c j t)
        = ∫ t in c..y, (t - c) ^ j / (j.factorial : ℝ) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      rw [Set.uIcc_of_le (le_of_lt hyc)] at ht
      exact truncPow_of_le ht.1 j
    have hpow : (∫ t in c..y, (t - c) ^ j) = (y - c) ^ (j + 1) / ((j : ℝ) + 1) := by
      rw [intervalIntegral.integral_comp_sub_right (fun u => u ^ j) c]
      rw [integral_pow]
      simp
    have hfac : (0:ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
    rw [hsplit, hleft, hright, intervalIntegral.integral_div, hpow, zero_add,
      truncPow_of_le (le_of_lt hyc)]
    rw [Nat.factorial_succ]
    push_cast
    field_simp

theorem intervalIntegrable_truncPow_ofReal (c : ℝ) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => ((truncPow c j t : ℝ) : ℂ)) volume a b :=
  ⟨((intervalIntegrable_truncPow c j a b).1).ofReal,
    ((intervalIntegrable_truncPow c j a b).2).ofReal⟩

/-- A finite superposition of unit jumps at the nodes, integrated `j` times from `1`. -/
def truncPowSum {ι : Type*} (S : Finset ι) (node : ι → ℝ) (a : ι → ℂ) (j : ℕ) (y : ℝ) : ℂ :=
  ∑ i ∈ S, a i * ((truncPow (node i) j y : ℝ) : ℂ)

/-- At level `0` the superposition is the summatory function of the coefficients. -/
theorem truncPowSum_zero {ι : Type*} [DecidableEq ι] (S : Finset ι) (node : ι → ℝ) (a : ι → ℂ)
    (y : ℝ) :
    truncPowSum S node a 0 y = ∑ i ∈ S with node i ≤ y, a i := by
  classical
  rw [truncPowSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [truncPow_zero_step]
  by_cases h : node i ≤ y
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]
    simp

/-- **Repeated integration of a superposition of jumps.**  Integrating the `j`-th level from `1`
gives the `(j+1)`-st level, provided every node lies to the right of `1`. -/
theorem integral_truncPowSum {ι : Type*} {S : Finset ι} {node : ι → ℝ} {a : ι → ℂ}
    (hnode : ∀ i ∈ S, 1 ≤ node i) {y : ℝ} (hy : 1 ≤ y) (j : ℕ) :
    (∫ t in (1:ℝ)..y, truncPowSum S node a j t) = truncPowSum S node a (j + 1) y := by
  have hsum : (∫ t in (1:ℝ)..y, truncPowSum S node a j t)
      = ∑ i ∈ S, ∫ t in (1:ℝ)..y, a i * ((truncPow (node i) j t : ℝ) : ℂ) := by
    refine intervalIntegral.integral_finsetSum ?_
    intro i _
    exact (intervalIntegrable_truncPow_ofReal (node i) j 1 y).const_mul (a i)
  rw [hsum, truncPowSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_truncPow (hnode i hi) hy j]

end GaloisForLFunctions.HTGeometry

end
