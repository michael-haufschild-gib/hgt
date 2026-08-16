import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic

/-!
# Shifted moment towers do not determine the unshifted tail class

For a positive weight sequence `a` place the atom `a n` at the point `exp (-(n+1))`.  The shifted
moments of the resulting measure are

`T k = ∑ n, a n * exp (-(k * (n + 1)))`,

and the unshifted mass is `T 0 = ∑ n, a n`.

Finiteness of every shifted moment `k ≥ 1` is compatible with unshifted masses of wildly different
divergence rates: the harmonic weight, the constant weight and the stretched-exponential weight
`exp (√(n+1))` all have every shifted moment finite and divergent unshifted mass, while their
partial sums separate — the harmonic partial sums are `o` of the constant ones, and the constant
ones are `o` of the stretched-exponential ones.  The weight `exp (n+1)` already fails at `k = 1`,
so the shifted condition is not vacuous.
-/

noncomputable section

namespace RHTower

open Filter Finset
open scoped Topology BigOperators

/-- The `k`-shifted moment term of the exponential reciprocal measure. -/
def shiftedTowerTerm (a : ℕ → ℝ) (k : ℝ) (n : ℕ) : ℝ :=
  a n * Real.exp (-(k * (n + 1)))

/-- A geometric series in the exponential scale. -/
theorem summable_exp_linear {c : ℝ} (hc : c < 0) :
    Summable (fun n : ℕ => Real.exp (c * (n + 1))) := by
  have hrewrite : (fun n : ℕ => Real.exp (c * (n + 1))) =
      fun n : ℕ => Real.exp c * (Real.exp c) ^ n := by
    funext n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  rw [hrewrite]
  exact (summable_geometric_of_lt_one (Real.exp_pos c).le
    (Real.exp_lt_one_iff.mpr hc)).mul_left _

/-- A weight of exponential order strictly below the shift has summable shifted moment. -/
theorem summable_shiftedTowerTerm_of_exp_bound
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {C r k : ℝ}
    (hab : ∀ n, a n ≤ C * Real.exp (r * (n + 1))) (hk : r < k) :
    Summable (fun n : ℕ => shiftedTowerTerm a k n) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (ha n) (Real.exp_pos _).le) (fun n => ?_)
    ((summable_exp_linear (c := r - k) (by linarith)).mul_left C)
  have hstep : a n * Real.exp (-(k * (n + 1))) ≤
      (C * Real.exp (r * (n + 1))) * Real.exp (-(k * (n + 1))) := by
    have := hab n
    have hpos : (0 : ℝ) < Real.exp (-(k * (n + 1))) := Real.exp_pos _
    nlinarith [hpos]
  refine hstep.trans_eq ?_
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

/-! ### The three admissible weights -/

/-- Harmonic weight. -/
def harmonicWeight (n : ℕ) : ℝ := 1 / (n + 1)

/-- Constant weight. -/
def constantWeight (_ : ℕ) : ℝ := 1

/-- Stretched-exponential weight. -/
def stretchedWeight (n : ℕ) : ℝ := Real.exp (Real.sqrt (n + 1))

/-- Exponential control weight, outside the shifted-finite regime. -/
def exponentialWeight (n : ℕ) : ℝ := Real.exp (n + 1)

theorem harmonicWeight_nonneg (n : ℕ) : 0 ≤ harmonicWeight n := by
  unfold harmonicWeight
  positivity

theorem constantWeight_nonneg (n : ℕ) : 0 ≤ constantWeight n := zero_le_one

theorem stretchedWeight_nonneg (n : ℕ) : 0 ≤ stretchedWeight n := (Real.exp_pos _).le

/-- The square-root exponent is dominated by a quarter of the argument plus one. -/
theorem sqrt_le_quarter_add_one (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ≤ x / 4 + 1 := by
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith [sq_nonneg (Real.sqrt x - 2)]

theorem summable_shiftedTowerTerm_harmonic {k : ℝ} (hk : 0 < k) :
    Summable (fun n : ℕ => shiftedTowerTerm harmonicWeight k n) := by
  refine summable_shiftedTowerTerm_of_exp_bound harmonicWeight harmonicWeight_nonneg
    (C := 1) (r := 0) (fun n => ?_) hk
  have hle : harmonicWeight n ≤ 1 := by
    unfold harmonicWeight
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  simpa using hle

theorem summable_shiftedTowerTerm_constant {k : ℝ} (hk : 0 < k) :
    Summable (fun n : ℕ => shiftedTowerTerm constantWeight k n) := by
  refine summable_shiftedTowerTerm_of_exp_bound constantWeight constantWeight_nonneg
    (C := 1) (r := 0) (fun n => ?_) hk
  simp [constantWeight]

theorem summable_shiftedTowerTerm_stretched {k : ℝ} (hk : (1 : ℝ) / 4 < k) :
    Summable (fun n : ℕ => shiftedTowerTerm stretchedWeight k n) := by
  refine summable_shiftedTowerTerm_of_exp_bound stretchedWeight stretchedWeight_nonneg
    (C := Real.exp 1) (r := 1 / 4) (fun n => ?_) hk
  have hx : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hbound : Real.sqrt ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / 4 + 1 :=
    sqrt_le_quarter_add_one _ hx
  have := Real.exp_le_exp.mpr hbound
  calc stretchedWeight n = Real.exp (Real.sqrt ((n : ℝ) + 1)) := rfl
    _ ≤ Real.exp (((n : ℝ) + 1) / 4 + 1) := this
    _ = Real.exp 1 * Real.exp ((1 / 4) * ((n : ℝ) + 1)) := by
        rw [← Real.exp_add]
        ring_nf

/-! ### Every unshifted mass diverges -/

theorem not_summable_harmonicWeight : ¬ Summable harmonicWeight := by
  intro h
  have : Summable (fun n : ℕ => 1 / ((n : ℝ))) := by
    refine (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ))) 1).mp ?_
    refine h.congr fun n => ?_
    unfold harmonicWeight
    push_cast
    ring_nf
  exact Real.not_summable_one_div_natCast this

theorem not_summable_one : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro h
  have hzero : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := h.tendsto_atTop_zero
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hEq := tendsto_nhds_unique hzero hone
  norm_num at hEq

theorem not_summable_constantWeight : ¬ Summable constantWeight := not_summable_one

theorem not_summable_stretchedWeight : ¬ Summable stretchedWeight := by
  intro h
  have hzero := h.tendsto_atTop_zero
  have hge : ∀ n : ℕ, (1 : ℝ) ≤ stretchedWeight n := by
    intro n
    unfold stretchedWeight
    rw [Real.one_le_exp_iff]
    positivity
  have hlt : ∀ᶠ n : ℕ in atTop, |stretchedWeight n| < 1 := by
    have := hzero
    rw [Metric.tendsto_atTop] at this
    obtain ⟨N, hN⟩ := this 1 one_pos
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa [Real.dist_eq] using hN n hn
  obtain ⟨n, hn⟩ := hlt.exists
  have := hge n
  rw [abs_of_nonneg (stretchedWeight_nonneg n)] at hn
  linarith

/-- **Control case.**  The exponential weight already fails at the first shift. -/
theorem not_summable_shiftedTowerTerm_exponential :
    ¬ Summable (fun n : ℕ => shiftedTowerTerm exponentialWeight 1 n) := by
  have hone : (fun n : ℕ => shiftedTowerTerm exponentialWeight 1 n) = fun _ : ℕ => (1 : ℝ) := by
    funext n
    unfold shiftedTowerTerm exponentialWeight
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [hone]
  exact not_summable_one

/-! ### The three divergence rates are pairwise incompatible -/

/-- The harmonic partial sums are `o` of the constant-weight partial sums. -/
theorem tendsto_harmonic_div_constant_partialSum :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, harmonicWeight n) / (∑ n ∈ range N, constantWeight n)) atTop (𝓝 0) := by
  have hterm : Tendsto harmonicWeight atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hces := hterm.cesaro
  refine hces.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hsum : (∑ _n ∈ range N, constantWeight _n) = (N : ℝ) := by
    simp [constantWeight]
  rw [hsum, inv_mul_eq_div]

/-- The constant-weight partial sums are `o` of the stretched-exponential ones. -/
theorem tendsto_constant_div_stretched_partialSum :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, constantWeight n) / (∑ n ∈ range N, stretchedWeight n)) atTop (𝓝 0) := by
  have hsqrtAtTop : Tendsto Real.sqrt atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ⟨(max b 0) ^ 2, fun a ha => ?_⟩
    have h1 : Real.sqrt ((max b 0) ^ 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt ha
    rw [Real.sqrt_sq (le_max_right b 0)] at h1
    exact le_trans (le_max_left b 0) h1
  have hkey : Tendsto (fun N : ℕ => (N : ℝ) / Real.exp (Real.sqrt N)) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
      hsqrtAtTop.comp tendsto_natCast_atTop_atTop
    have hbase : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
    have := hbase.comp hcomp
    refine this.congr fun N => ?_
    have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
    simp only [Function.comp_apply, hsq, Real.exp_neg]
    ring
  refine squeeze_zero' ?_ ?_ hkey
  · filter_upwards with N
    exact div_nonneg (Finset.sum_nonneg fun i _ => constantWeight_nonneg i)
      (Finset.sum_nonneg fun i _ => stretchedWeight_nonneg i)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hsumc : (∑ _n ∈ range N, constantWeight _n) = (N : ℝ) := by simp [constantWeight]
    have hlow : Real.exp (Real.sqrt N) ≤ ∑ n ∈ range N, stretchedWeight n := by
      have hmem : N - 1 ∈ range N := by
        simp only [mem_range]
        omega
      have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
        have h1 : (1 : ℕ) ≤ N := hN
        rw [Nat.cast_sub h1]
        norm_num
      have hterm : stretchedWeight (N - 1) = Real.exp (Real.sqrt N) := by
        unfold stretchedWeight
        rw [hcast]
      rw [← hterm]
      exact Finset.single_le_sum (f := stretchedWeight)
        (fun i _ => stretchedWeight_nonneg i) hmem
    rw [hsumc]
    have hpos : (0 : ℝ) < Real.exp (Real.sqrt N) := Real.exp_pos _
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) hpos hlow

end RHTower
