import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CumulativeQuadratureOfTheGcdDeficit

/-!
# Distribution of right endpoints in cumulative gcd shortfall

Place each shortfall at the value of the cumulative shortfall immediately
after that step. The discrepancy from uniform length is exactly the
largest jump in the supremum norm. On every power grid the first jump is
already maximal. The bias of the first moment instead measures the sum of
the squared jumps. These are the atomic corrections to the distribution
function interpretation of Pain (arXiv:2603.08959, §5).
-/

noncomputable section
open Finset
open GaloisForLFunctions.CumulativeQuadrature
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Total shortfall placed at or below a cumulative value t. -/
def gcdMassBelow (r N : ℕ) (t : ℝ) : ℝ :=
  rightSum (powerGridGcdDeficit r) (fun y => if y ≤ t then 1 else 0) N

private theorem zero_mass (r : ℕ) : powerGridGcdDeficit r 0 = 0 := by simp [powerGridGcdDeficit]

theorem first_gcd_shortfall (r : ℕ) : powerGridGcdDeficit r 1 = Real.log 2 := by
  have h : Finset.Ioc 0 1 = {1} := by decide
  simp [powerGridGcdDeficit, octaveGcdProduct, h, max_eq_left (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]

private theorem mass_below_succ (r N : ℕ) (t : ℝ) :
    gcdMassBelow r (N+1) t = gcdMassBelow r N t +
      if powerGridGcdDeficit r (N+1) ≤ t then powerGridGcdDeficit r (N+1) - powerGridGcdDeficit r N else 0 := by
  by_cases h : powerGridGcdDeficit r (N+1) ≤ t <;>
    simp only [gcdMassBelow, rightSum, Finset.sum_range_succ, h, if_true, if_false, mul_one, mul_zero]

private theorem mass_below_terminal {r N : ℕ} {t : ℝ} (h : powerGridGcdDeficit r N ≤ t) :
    gcdMassBelow r N t = powerGridGcdDeficit r N := by
  rw [gcdMassBelow, rightSum]
  have hi (i : ℕ) (hi : i ∈ range N) := ((monotone_gcd_deficit r)
    (Nat.succ_le_of_lt (mem_range.mp hi))).trans h
  calc _ = ∑ i ∈ range N, (powerGridGcdDeficit r (i+1)-powerGridGcdDeficit r i) :=
         sum_congr rfl (fun i hi' => by rw [if_pos (hi i hi'), mul_one])
       _ = _ := by rw [sum_range_sub, zero_mass, sub_zero]

/-- Every CDF reading lags uniform length by at most log 2, uniformly in
the endpoint, the test height, and the power of the grid. -/
theorem gcd_mass_below_discrepancy (r N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ min t (powerGridGcdDeficit r N) - gcdMassBelow r N t ∧
    min t (powerGridGcdDeficit r N) - gcdMassBelow r N t ≤ Real.log 2 := by
  induction N with
  | zero => simp [zero_mass, gcdMassBelow, rightSum, min_eq_right ht, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  | succ N ih =>
    by_cases h : powerGridGcdDeficit r (N+1) ≤ t
    · rw [mass_below_terminal h, min_eq_right h, sub_self]
      exact ⟨le_rfl,Real.log_nonneg (by norm_num)⟩
    rw [mass_below_succ, if_neg h, add_zero, min_eq_left (le_of_not_ge h)]
    by_cases hpre : powerGridGcdDeficit r N ≤ t
    · rw [mass_below_terminal hpre]
      exact ⟨sub_nonneg.mpr hpre, (sub_le_sub_right (le_of_not_ge h) _).trans
        (gcd_deficit_increment_bounds r N).2⟩
    · rwa [min_eq_left (le_of_not_ge hpre)] at ih

/-- At positive horizon the least uniform bound is log 2. This identifies
the exact Kolmogorov discrepancy after dividing by total mass. -/
theorem gcd_mass_below_uniform_bound_iff (r N : ℕ) (B : ℝ) :
    (∀ t : ℝ, 0 ≤ t → min t (powerGridGcdDeficit r (N+1)) - gcdMassBelow r (N+1) t ≤ B)
      ↔ Real.log 2 ≤ B := by
  constructor
  · intro hb
    by_contra! hsmall
    have hlog := Real.log_pos (by norm_num : (1:ℝ) < 2)
    obtain ⟨t,ht,hl⟩ := exists_between (max_lt hsmall hlog)
    have hfirst (i : ℕ) : Real.log 2 ≤ powerGridGcdDeficit r (i+1) := by
      rw [←first_gcd_shortfall r]
      exact monotone_gcd_deficit r (Nat.succ_le_succ (Nat.zero_le i))
    have hempty : gcdMassBelow r (N+1) t = 0 := by
      unfold gcdMassBelow rightSum
      apply Finset.sum_eq_zero
      intro i _
      change _ * (if powerGridGcdDeficit r (i+1) ≤ t then 1 else 0) = 0
      rw [if_neg (not_le_of_gt (hl.trans_le (hfirst i))),mul_zero]
    have h := hb t ((le_max_right ..).trans ht.le)
    rw [min_eq_left (hl.le.trans (hfirst N)),hempty,sub_zero] at h
    exact (not_lt_of_ge h) ((le_max_left ..).trans_lt ht)
  · intro h t ht
    exact (gcd_mass_below_discrepancy r (N+1) ht).2.trans h

/-- The excess first moment over uniform length equals exactly half the
sum of the squared atomic masses. -/
theorem gcd_right_endpoint_moment_bias (r N : ℕ) :
    2*rightSum (powerGridGcdDeficit r) id N - (powerGridGcdDeficit r N)^2 =
      ∑ i ∈ range N, (powerGridGcdDeficit r (i+1) - powerGridGcdDeficit r i)^2 := by
  induction N with
  | zero => simp [rightSum, zero_mass]
  | succ N ih =>
    rw [rightSum, Finset.sum_range_succ] at ⊢
    rw [rightSum] at ih
    rw [Finset.sum_range_succ (fun i => (powerGridGcdDeficit r (i+1)-powerGridGcdDeficit r i)^2),←ih]
    simp only [id_eq]
    ring

#print axioms gcd_mass_below_discrepancy
#print axioms gcd_mass_below_uniform_bound_iff
#print axioms gcd_right_endpoint_moment_bias

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
