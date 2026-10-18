import GaloisForLFunctions.BezoutValuationIncidence.PostStepInactivePrefixAndSixDivisibilityPronicDefect

/-!
# Pillar XXVI: General Linear Pronic Abel Summation, Post-Step Inactive Energy Equivalence & Exact Pronic–Gradient Conservation

In Pillar XXV (`PostStepInactivePrefixAndSixDivisibilityPronicDefect`), we introduced the
horizon-free post-step inactive residual prefix
$$\operatorname{pmPostStepInactivePrefix}\,\varepsilon\,n = A_\varepsilon(n) + \operatorname{pmActiveSawtoothComponent}\,\varepsilon\,n$$
whose BVI forward difference replaces the single divisor impulse $\widetilde{\tau}_\varepsilon(n + 1)$
by the two-point Bézout average
$\frac{1}{2}\bigl(\widetilde{\tau}_\varepsilon(n) + \widetilde{\tau}_\varepsilon(n + 1)\bigr) + \frac{1}{2}\,\operatorname{addDiff}\,(\tau_{1+\varepsilon})\,n$.

In this twenty-sixth pillar of **Bézout–Valuation Incidence Mechanics**, we establish three new
foundational mechanisms:

1. **General Linear Pronic Abel Summation & Exact Pronic Reciprocal Telescoping
   (`sum_div_pronicSeq_add_terminal_eq_abel`,
   `sum_div_pronicSeq_eq_compensated_abel`,
   `sum_one_div_pronicSeq_eq`,
   `sum_one_div_pronicSeq_le_one`)**:
   - For **every** sequence $B : \mathbb{N} \to \mathbb{R}$ and every horizon $T \ge 1$:
     $$\sum_{n=1}^T \frac{B(n)}{\operatorname{pronicSeq}\,n} + \frac{B(T)}{T + 1}
       = B(1) + \sum_{n=1}^{T-1} \frac{\operatorname{addDiff}\,B\,n}{n + 1},$$
     and in terminal-compensated form:
     $$\sum_{n=1}^T \frac{B(n)}{\operatorname{pronicSeq}\,n}
       = B(1)\left(1 - \frac{1}{T + 1}\right) +
         \sum_{n=1}^{T-1} \operatorname{addDiff}\,B\,n \cdot \left(\frac{1}{n + 1} - \frac{1}{T + 1}\right).$$
   - Specializing to $B(n) \equiv 1$ gives the exact pronic reciprocal telescoping identity
     $\sum_{n=1}^T \frac{1}{\operatorname{pronicSeq}\,n} = 1 - \frac{1}{T + 1} \le 1$, and
     bounding $B(n) = \bigl(\operatorname{pmActiveSawtoothComponent}\,\varepsilon\,n\bigr)^2 \in [0, 1/4]$
     yields the uniform $1/4$ ceiling
     $$0 \le \sum_{n=1}^T \frac{\bigl(\operatorname{pmActiveSawtoothComponent}\,\varepsilon\,n\bigr)^2}{\operatorname{pronicSeq}\,n} \le \frac{1}{4}.$$

2. **Post-Step Inactive Discrete Energy (`pmPostStepInactiveDiscreteEnergy`) & Two-Sided Equivalence with `pmPowerDampedDivisorDiscreteEnergy`
   (`pmPostStepInactiveDiscreteEnergy_add_terminal_eq_abel`,
   `pmPowerDampedDivisorDiscreteEnergy_le_two_mul_pmPostStepInactiveDiscreteEnergy_add_half`,
   `pmPostStepInactiveDiscreteEnergy_le_two_mul_pmPowerDampedDivisorDiscreteEnergy_add_half`,
   `riemannHypothesis_of_pmPostStepInactive_cofinal_discrete_budget`)**:
   - Defining $\operatorname{pmPostStepInactiveDiscreteEnergy}\,\varepsilon\,T := \sum_{n=1}^T \frac{(\operatorname{pmPostStepInactivePrefix}\,\varepsilon\,n)^2}{\operatorname{pronicSeq}\,n}$,
     for all $\varepsilon \ge 0$ and $T \in \mathbb{N}$:
     $$\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T
       \le 2\,\operatorname{pmPostStepInactiveDiscreteEnergy}\,\varepsilon\,T + \frac{1}{2},$$
     $$\operatorname{pmPostStepInactiveDiscreteEnergy}\,\varepsilon\,T
       \le 2\,\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T + \frac{1}{2}.$$
   - Consequently, uniform boundedness of `pmPostStepInactiveDiscreteEnergy ε T` along a cofinal
     sequence $\varepsilon \to 0^+$ implies `RiemannHypothesis`.

3. **Exact Pronic–Diagonal–Gradient Conservation Law & Boundary-Free Finite Inequalities
   (`addDiff_pmPowerDampedDivisorCoeff_sq_add_two_mul_pronicSeq`,
   `addDiff_pmPowerDampedDivisorCoeff_sq_add_two_mul_centered_pronic`,
   `two_point_bezout_average_sq_add_quarter_addDiff_sq`,
   `sum_Icc_pronicSeq_add_addDiff_sq_eq`,
   `sum_Icc_pronicSeq_add_addDiff_sq_le_two_mul_sum_sq`,
   `tendsto_pronicSeq_add_half_addDiff_sq_mean`)**:
   - By Bézout coprimality $\gcd(n, n + 1) = 1$, for every $\varepsilon : \mathbb{R}$ and $n \in \mathbb{N}$:
     $$\bigl(\operatorname{addDiff}\,(\tau_\varepsilon)\,n\bigr)^2 + 2\,\tau_\varepsilon(\operatorname{pronicSeq}\,n)
       = \tau_\varepsilon(n)^2 + \tau_\varepsilon(n + 1)^2,$$
     $$\bigl(\operatorname{addDiff}\,(\tau_\varepsilon)\,n\bigr)^2 + 2\,\widetilde{\tau}_\varepsilon(n)\,\widetilde{\tau}_\varepsilon(n + 1)
       = \widetilde{\tau}_\varepsilon(n)^2 + \widetilde{\tau}_\varepsilon(n + 1)^2,$$
     and the squared two-point Bézout average obeys the exact parallelogram law:
     $$\left(\frac{\widetilde{\tau}_\varepsilon(n) + \widetilde{\tau}_\varepsilon(n + 1)}{2}\right)^2 +
       \frac{1}{4}\bigl(\operatorname{addDiff}\,(\tau_\varepsilon)\,n\bigr)^2
       = \frac{1}{2}\bigl(\widetilde{\tau}_\varepsilon(n)^2 + \widetilde{\tau}_\varepsilon(n + 1)^2\bigr).$$
   - Summing over $n \in [1, N]$ ($N \ge 1$) gives the exact finite conservation identity:
     $$2\sum_{n=1}^N \tau_\varepsilon(\operatorname{pronicSeq}\,n) +
       \sum_{n=1}^N \bigl(\operatorname{addDiff}\,(\tau_\varepsilon)\,n\bigr)^2
       = 2\sum_{n=1}^N \tau_\varepsilon(n)^2 + \tau_\varepsilon(N + 1)^2 - 1.$$
   - Because $\tau_\varepsilon(N + 1)^2 \le 1$ for all $\varepsilon \ge 0$, the boundary term
     $\tau_\varepsilon(N + 1)^2 - 1 \le 0$ is universally non-positive, yielding the **boundary-free**
     finite inequalities at every $N \ge 1$:
     $$2\sum_{n=1}^N \tau_\varepsilon(\operatorname{pronicSeq}\,n) +
       \sum_{n=1}^N \bigl(\operatorname{addDiff}\,(\tau_\varepsilon)\,n\bigr)^2
       \le 2\sum_{n=1}^N \tau_\varepsilon(n)^2,$$
     $$\sum_{n=1}^N \tau_\varepsilon(\operatorname{pronicSeq}\,n) \le \sum_{n=1}^N \tau_\varepsilon(n)^2, \qquad
       \sum_{n=1}^N \bigl(\operatorname{addDiff}\,(\tau_\varepsilon)\,n\bigr)^2 \le 2\sum_{n=1}^N \tau_\varepsilon(n)^2.$$
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. General Linear Pronic Abel Summation & Exact Pronic Reciprocal Telescoping -/

/-- **Telescoping Sum of Forward Differences (`sum_Icc_addDiff`):**
For every sequence `B : ℕ → ℝ` and every `T ≥ 1`:
`∑_{n=1}^{T-1} addDiff B n = B(T) - B(1)`. -/
theorem sum_Icc_addDiff (B : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (T - 1), addDiff B n) = B T - B 1 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, T = m + 1 := ⟨T - 1, by omega⟩
  clear hT
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hsplit : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]; omega
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [hsplit, Finset.sum_insert hnot, ih]
    unfold addDiff
    ring

/-- **General Linear Pronic Abel Summation (`sum_div_pronicSeq_add_terminal_eq_abel`):**
For every sequence `B : ℕ → ℝ` and every horizon `T ≥ 1`:
`∑_{n=1}^T B(n) / pronicSeq n + B(T) / (T + 1) = B(1) + ∑_{n=1}^{T-1} addDiff B n / (n + 1)`. -/
theorem sum_div_pronicSeq_add_terminal_eq_abel (B : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 T, B n / (pronicSeq n : ℝ)) +
      B T / ((T : ℝ) + 1) =
      B 1 + ∑ n ∈ Finset.Icc 1 (T - 1), addDiff B n / ((n : ℝ) + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, T = m + 1 := ⟨T - 1, by omega⟩
  clear hT
  induction m with
  | zero =>
    simp only [zero_add, Nat.sub_self, Finset.Icc_self, Finset.sum_singleton,
      Finset.Icc_eq_empty (by decide : ¬ (1 ≤ 0)), Finset.sum_empty, add_zero]
    unfold pronicSeq
    norm_num
  | succ m ih =>
    have hsplit_lhs :
        Finset.Icc 1 (m + 1 + 1) = insert (m + 1 + 1) (Finset.Icc 1 (m + 1)) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot_lhs : m + 1 + 1 ∉ Finset.Icc 1 (m + 1) := by
      simp only [Finset.mem_Icc]; omega
    have hsplit_rhs :
        Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot_rhs : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit_lhs, Finset.sum_insert hnot_lhs]
    simp only [Nat.add_sub_cancel] at ih ⊢
    have hrhs :
        (∑ n ∈ Finset.Icc 1 (m + 1), addDiff B n / ((n : ℝ) + 1)) =
        addDiff B (m + 1) / (((m + 1 : ℕ) : ℝ) + 1) +
          ∑ n ∈ Finset.Icc 1 m, addDiff B n / ((n : ℝ) + 1) := by
      rw [hsplit_rhs, Finset.sum_insert hnot_rhs]
    have hpronic :
        B (m + 1 + 1) / (pronicSeq (m + 1 + 1) : ℝ) +
          B (m + 1 + 1) / (((m + 1 + 1 : ℕ) : ℝ) + 1) -
          B (m + 1) / (((m + 1 : ℕ) : ℝ) + 1) =
          addDiff B (m + 1) / (((m + 1 : ℕ) : ℝ) + 1) := by
      unfold pronicSeq addDiff
      have h1 : (((m + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (((m + 1 + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    linarith

/-- **Terminal-Compensated Linear Pronic Abel Identity (`sum_div_pronicSeq_eq_compensated_abel`):**
For every sequence `B : ℕ → ℝ` and every `T ≥ 1`:
`∑_{n=1}^T B(n) / pronicSeq n = B(1) * (1 - 1 / (T + 1)) + ∑_{n=1}^{T-1} addDiff B n * (1 / (n + 1) - 1 / (T + 1))`. -/
theorem sum_div_pronicSeq_eq_compensated_abel (B : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 T, B n / (pronicSeq n : ℝ)) =
      B 1 * (1 - 1 / ((T : ℝ) + 1)) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff B n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  have habel := sum_div_pronicSeq_add_terminal_eq_abel B hT
  have hBT : B T = B 1 + ∑ n ∈ Finset.Icc 1 (T - 1), addDiff B n := by
    linarith [sum_Icc_addDiff B hT]
  have hBT_div :
      B T / ((T : ℝ) + 1) =
        B 1 / ((T : ℝ) + 1) +
          ∑ n ∈ Finset.Icc 1 (T - 1), addDiff B n / ((T : ℝ) + 1) := by
    rw [hBT, add_div, Finset.sum_div]
  have hsub :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff B n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      (∑ n ∈ Finset.Icc 1 (T - 1), addDiff B n / ((n : ℝ) + 1)) -
        ∑ n ∈ Finset.Icc 1 (T - 1), addDiff B n / ((T : ℝ) + 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hB1 : B 1 - B 1 / ((T : ℝ) + 1) = B 1 * (1 - 1 / ((T : ℝ) + 1)) := by ring
  linarith

/-- **Exact Pronic Reciprocal Telescoping Identity (`sum_one_div_pronicSeq_eq`):**
For every `T ≥ 1`:
`∑_{n=1}^T 1 / pronicSeq n = 1 - 1 / (T + 1)`. -/
theorem sum_one_div_pronicSeq_eq {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 T, (1 : ℝ) / (pronicSeq n : ℝ)) = 1 - 1 / ((T : ℝ) + 1) := by
  simpa [addDiff] using sum_div_pronicSeq_eq_compensated_abel (fun _ : ℕ => (1 : ℝ)) hT

/-- **Universal Unit Bound on the Pronic Reciprocal Sum (`sum_one_div_pronicSeq_le_one`):**
For every `T : ℕ`, `∑_{n=1}^T 1 / pronicSeq n ≤ 1`. -/
theorem sum_one_div_pronicSeq_le_one (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, (1 : ℝ) / (pronicSeq n : ℝ)) ≤ 1 := by
  by_cases hT : 1 ≤ T
  · rw [sum_one_div_pronicSeq_eq hT]
    have hpos : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
    linarith
  · have hT0 : T = 0 := by omega
    subst hT0
    simp

/-- **Uniform `[0, 1 / 4]` Bounds on the Active Sawtooth Pronic Energy
(`sum_pmActiveSawtoothComponent_sq_div_pronicSeq_bounds`):**
For every `ε ≥ 0` and `T : ℕ`:
`0 ≤ ∑_{n=1}^T (pmActiveSawtoothComponent ε n)² / pronicSeq n ≤ 1 / 4`. -/
theorem sum_pmActiveSawtoothComponent_sq_div_pronicSeq_bounds {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    0 ≤ (∑ n ∈ Finset.Icc 1 T, pmActiveSawtoothComponent ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) ∧
      (∑ n ∈ Finset.Icc 1 T, pmActiveSawtoothComponent ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) ≤ 1 / 4 := by
  refine ⟨Finset.sum_nonneg fun n _ => by positivity, ?_⟩
  have hle :
      (∑ n ∈ Finset.Icc 1 T, pmActiveSawtoothComponent ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 T, (1 / 4 : ℝ) * ((1 : ℝ) / (pronicSeq n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n _
    obtain ⟨h0, hhalf⟩ := pmActiveSawtoothComponent_bounds hε n
    have hsq : pmActiveSawtoothComponent ε n ^ (2 : ℕ) ≤ 1 / 4 := by nlinarith
    have hpr : (0 : ℝ) ≤ 1 / (pronicSeq n : ℝ) := by positivity
    calc
      pmActiveSawtoothComponent ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)
        = pmActiveSawtoothComponent ε n ^ (2 : ℕ) * ((1 : ℝ) / (pronicSeq n : ℝ)) := by ring
      _ ≤ (1 / 4 : ℝ) * ((1 : ℝ) / (pronicSeq n : ℝ)) := mul_le_mul_of_nonneg_right hsq hpr
  rw [← Finset.mul_sum] at hle
  linarith [sum_one_div_pronicSeq_le_one T]

/-! ## §2. Post-Step Inactive Discrete Energy & Two-Sided Equivalence with `pmPowerDampedDivisorDiscreteEnergy` -/

/-- The **post-step inactive discrete energy** of Route PM up to horizon `T`:
`pmPostStepInactiveDiscreteEnergy ε T = ∑_{n=1}^T (pmPostStepInactivePrefix ε n)² / pronicSeq n`. -/
def pmPostStepInactiveDiscreteEnergy (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 T,
    pmPostStepInactivePrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)

/-- At `n = 1`, `pmPostStepInactivePrefix ε 1 = pmPowerDampedCenteredDivisorCoeff ε 1`. -/
@[simp]
theorem pmPostStepInactivePrefix_one (ε : ℝ) :
    pmPostStepInactivePrefix ε 1 = pmPowerDampedCenteredDivisorCoeff ε 1 := by
  unfold pmPostStepInactivePrefix
  rw [pmPowerDampedCenteredDivisorPrefix_one, pmActiveSawtoothComponent_one, add_zero]

/-- **Exact Pronic Abel Decomposition of `pmPostStepInactiveDiscreteEnergy`
(`pmPostStepInactiveDiscreteEnergy_add_terminal_eq_abel`):**
For every `ε : ℝ` and `T ≥ 1`:
`pmPostStepInactiveDiscreteEnergy ε T + (pmPostStepInactivePrefix ε T)² / (T + 1)`
equals `(pmPowerDampedCenteredDivisorCoeff ε 1)²` plus
`∑_{n=1}^{T-1} ((pmPostStepInactivePrefix ε (n + 1))² - (pmPostStepInactivePrefix ε n)²) / (n + 1)`. -/
theorem pmPostStepInactiveDiscreteEnergy_add_terminal_eq_abel (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pmPostStepInactiveDiscreteEnergy ε T +
      pmPostStepInactivePrefix ε T ^ (2 : ℕ) / ((T : ℝ) + 1) =
      pmPowerDampedCenteredDivisorCoeff ε 1 ^ (2 : ℕ) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          (pmPostStepInactivePrefix ε (n + 1) ^ (2 : ℕ) -
            pmPostStepInactivePrefix ε n ^ (2 : ℕ)) / ((n : ℝ) + 1) := by
  unfold pmPostStepInactiveDiscreteEnergy
  rw [sum_sq_div_pronicSeq_add_terminal_eq_abel (pmPostStepInactivePrefix ε) hT,
    pmPostStepInactivePrefix_one]

/-- **Upper Bound on `pmPostStepInactiveDiscreteEnergy` by `pmPowerDampedDivisorDiscreteEnergy`
(`pmPostStepInactiveDiscreteEnergy_le_two_mul_pmPowerDampedDivisorDiscreteEnergy_add_half`):**
For every `ε ≥ 0` and `T : ℕ`:
`pmPostStepInactiveDiscreteEnergy ε T ≤ 2 * pmPowerDampedDivisorDiscreteEnergy ε T + 1 / 2`. -/
theorem pmPostStepInactiveDiscreteEnergy_le_two_mul_pmPowerDampedDivisorDiscreteEnergy_add_half
    {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    pmPostStepInactiveDiscreteEnergy ε T ≤
      2 * pmPowerDampedDivisorDiscreteEnergy ε T + 1 / 2 := by
  have hpt :
      pmPostStepInactiveDiscreteEnergy ε T ≤
        2 * pmPowerDampedDivisorDiscreteEnergy ε T +
          2 * ∑ n ∈ Finset.Icc 1 T,
            pmActiveSawtoothComponent ε n ^ (2 : ℕ) / (pronicSeq n : ℝ) := by
    unfold pmPostStepInactiveDiscreteEnergy
    rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    have hsq :
        pmPostStepInactivePrefix ε n ^ (2 : ℕ) ≤
          2 * pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) +
            2 * pmActiveSawtoothComponent ε n ^ (2 : ℕ) := by
      unfold pmPostStepInactivePrefix
      have hdiff :
          0 ≤ (pmPowerDampedCenteredDivisorPrefix ε n - pmActiveSawtoothComponent ε n) ^ (2 : ℕ) :=
        sq_nonneg _
      linarith
    have hpr : (0 : ℝ) ≤ 1 / (pronicSeq n : ℝ) := by positivity
    calc
      pmPostStepInactivePrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)
        = pmPostStepInactivePrefix ε n ^ (2 : ℕ) * (1 / (pronicSeq n : ℝ)) := by ring
      _ ≤ (2 * pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) +
            2 * pmActiveSawtoothComponent ε n ^ (2 : ℕ)) * (1 / (pronicSeq n : ℝ)) :=
        mul_le_mul_of_nonneg_right hsq hpr
      _ = 2 * (pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
            2 * (pmActiveSawtoothComponent ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) := by ring
  linarith [(sum_pmActiveSawtoothComponent_sq_div_pronicSeq_bounds hε T).2]

/-- **Upper Bound on `pmPowerDampedDivisorDiscreteEnergy` by `pmPostStepInactiveDiscreteEnergy`
(`pmPowerDampedDivisorDiscreteEnergy_le_two_mul_pmPostStepInactiveDiscreteEnergy_add_half`):**
For every `ε ≥ 0` and `T : ℕ`:
`pmPowerDampedDivisorDiscreteEnergy ε T ≤ 2 * pmPostStepInactiveDiscreteEnergy ε T + 1 / 2`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_le_two_mul_pmPostStepInactiveDiscreteEnergy_add_half
    {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T ≤
      2 * pmPostStepInactiveDiscreteEnergy ε T + 1 / 2 := by
  have hpt :
      pmPowerDampedDivisorDiscreteEnergy ε T ≤
        2 * pmPostStepInactiveDiscreteEnergy ε T +
          2 * ∑ n ∈ Finset.Icc 1 T,
            pmActiveSawtoothComponent ε n ^ (2 : ℕ) / (pronicSeq n : ℝ) := by
    unfold pmPostStepInactiveDiscreteEnergy
    rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    have hsq :
        pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) ≤
          2 * pmPostStepInactivePrefix ε n ^ (2 : ℕ) +
            2 * pmActiveSawtoothComponent ε n ^ (2 : ℕ) := by
      unfold pmPostStepInactivePrefix
      have hsum :
          0 ≤ (pmPowerDampedCenteredDivisorPrefix ε n +
            2 * pmActiveSawtoothComponent ε n) ^ (2 : ℕ) :=
        sq_nonneg _
      linarith
    have hpr : (0 : ℝ) ≤ 1 / (pronicSeq n : ℝ) := by positivity
    calc
      pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)
        = pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) * (1 / (pronicSeq n : ℝ)) := by ring
      _ ≤ (2 * pmPostStepInactivePrefix ε n ^ (2 : ℕ) +
            2 * pmActiveSawtoothComponent ε n ^ (2 : ℕ)) * (1 / (pronicSeq n : ℝ)) :=
        mul_le_mul_of_nonneg_right hsq hpr
      _ = 2 * (pmPostStepInactivePrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
            2 * (pmActiveSawtoothComponent ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) := by ring
  linarith [(sum_pmActiveSawtoothComponent_sq_div_pronicSeq_bounds hε T).2]

/-- **Post-Step Inactive Energy Criterion for the Riemann Hypothesis
(`riemannHypothesis_of_pmPostStepInactive_cofinal_discrete_budget`):**
If for every `δ > 0` there exist `ε ∈ (0, δ)` and a uniform bound `B : ℝ` such that the smoothed
post-step inactive discrete energy `pmPostStepInactiveDiscreteEnergy ε T` is bounded by `B` for all
`T : ℕ`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_pmPostStepInactive_cofinal_discrete_budget
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPostStepInactiveDiscreteEnergy ε T ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget
  intro δ hδ
  obtain ⟨ε, hε, hεδ, B, hB⟩ := h δ hδ
  refine ⟨ε, hε, hεδ, 2 * B + 1 / 2, fun T => ?_⟩
  have hle :=
    pmPowerDampedDivisorDiscreteEnergy_le_two_mul_pmPostStepInactiveDiscreteEnergy_add_half hε.le T
  linarith [hB T]

/-! ## §3. Exact Pronic–Diagonal–Gradient Conservation Laws & Boundary-Free Finite Inequalities -/

/-- **Pointwise Pronic–Diagonal–Gradient Conservation Law for `pmPowerDampedDivisorCoeff`
(`addDiff_pmPowerDampedDivisorCoeff_sq_add_two_mul_pronicSeq`):**
For every `ε : ℝ` and `n : ℕ`, the squared BVI forward difference `(addDiff (τ_ε) n)²` plus twice
the pronic value `2 * τ_ε(pronicSeq n)` equals the sum of consecutive diagonal squares
`τ_ε(n)² + τ_ε(n + 1)²`. -/
theorem addDiff_pmPowerDampedDivisorCoeff_sq_add_two_mul_pronicSeq (ε : ℝ) (n : ℕ) :
    addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ) +
      2 * pmPowerDampedDivisorCoeff ε (pronicSeq n) =
      pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ) +
        pmPowerDampedDivisorCoeff ε (n + 1) ^ (2 : ℕ) := by
  rw [← pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq]
  unfold addDiff
  ring

/-- **Pointwise Centered Pronic–Diagonal–Gradient Conservation Law
(`addDiff_pmPowerDampedDivisorCoeff_sq_add_two_mul_centered_pronic`):**
For every `ε : ℝ` and `n : ℕ`, the squared BVI forward difference `(addDiff (τ_ε) n)²` plus twice
the centered consecutive product `2 * widetilde_τ_ε(n) * widetilde_τ_ε(n + 1)` equals the sum of
consecutive centered diagonal squares `widetilde_τ_ε(n)² + widetilde_τ_ε(n + 1)²`. -/
theorem addDiff_pmPowerDampedDivisorCoeff_sq_add_two_mul_centered_pronic (ε : ℝ) (n : ℕ) :
    addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ) +
      2 * (pmPowerDampedCenteredDivisorCoeff ε n *
        pmPowerDampedCenteredDivisorCoeff ε (n + 1)) =
      pmPowerDampedCenteredDivisorCoeff ε n ^ (2 : ℕ) +
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) ^ (2 : ℕ) := by
  unfold addDiff pmPowerDampedCenteredDivisorCoeff
  ring

/-- **Parallelogram / Polarization Law for the Two-Point Bézout Average
(`two_point_bezout_average_sq_add_quarter_addDiff_sq`):**
For every `ε : ℝ` and `n : ℕ`, the square of the two-point Bézout average
`((widetilde_τ_ε(n) + widetilde_τ_ε(n + 1)) / 2)²` plus `(1 / 4) * (addDiff (τ_ε) n)²` equals
the symmetric diagonal square average `(1 / 2) * (widetilde_τ_ε(n)² + widetilde_τ_ε(n + 1)²)`. -/
theorem two_point_bezout_average_sq_add_quarter_addDiff_sq (ε : ℝ) (n : ℕ) :
    ((pmPowerDampedCenteredDivisorCoeff ε n +
        pmPowerDampedCenteredDivisorCoeff ε (n + 1)) / 2) ^ (2 : ℕ) +
      (1 / 4 : ℝ) * addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ) =
      (1 / 2 : ℝ) * (pmPowerDampedCenteredDivisorCoeff ε n ^ (2 : ℕ) +
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) ^ (2 : ℕ)) := by
  unfold addDiff pmPowerDampedCenteredDivisorCoeff
  ring

/-- **Telescoping Sum of Consecutive Pairs `f(n) + f(n + 1)` (`sum_Icc_add_succ`):**
For every sequence `f : ℕ → ℝ` and every `N : ℕ`:
`∑_{n=1}^N (f(n) + f(n + 1)) = 2 * ∑_{n=1}^N f(n) + f(N + 1) - f(1)`. -/
theorem sum_Icc_add_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (f n + f (n + 1))) =
      2 * (∑ n ∈ Finset.Icc 1 N, f n) + f (N + 1) - f 1 := by
  have htel : (∑ n ∈ Finset.Icc 1 N, (f (n + 1) - f n)) = f (N + 1) - f 1 := by
    simpa [addDiff] using sum_Icc_addDiff f (by omega : 1 ≤ N + 1)
  have hrew :
      (∑ n ∈ Finset.Icc 1 N, (f n + f (n + 1))) =
        2 * (∑ n ∈ Finset.Icc 1 N, f n) +
          ∑ n ∈ Finset.Icc 1 N, (f (n + 1) - f n) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  linarith

/-- **Exact Finite Pronic–Diagonal–Gradient Conservation Identity
(`sum_Icc_pronicSeq_add_addDiff_sq_eq`):**
For every `ε : ℝ` and `N : ℕ`:
`2 * ∑_{n=1}^N τ_ε(pronicSeq n) + ∑_{n=1}^N (addDiff (τ_ε) n)² = 2 * ∑_{n=1}^N τ_ε(n)² + τ_ε(N + 1)² - 1`. -/
theorem sum_Icc_pronicSeq_add_addDiff_sq_eq (ε : ℝ) (N : ℕ) :
    2 * (∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff ε (pronicSeq n)) +
      (∑ n ∈ Finset.Icc 1 N, addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ)) =
      2 * (∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ)) +
        pmPowerDampedDivisorCoeff ε (N + 1) ^ (2 : ℕ) - 1 := by
  have hsum :
      2 * (∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff ε (pronicSeq n)) +
        (∑ n ∈ Finset.Icc 1 N, addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ)) =
      ∑ n ∈ Finset.Icc 1 N,
        (pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ) +
          pmPowerDampedDivisorCoeff ε (n + 1) ^ (2 : ℕ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    linarith [addDiff_pmPowerDampedDivisorCoeff_sq_add_two_mul_pronicSeq ε n]
  rw [hsum, sum_Icc_add_succ (fun n => pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ)) N,
    pmPowerDampedDivisorCoeff_one]
  ring

/-- **Boundary-Free Finite Pronic–Gradient Inequality
(`sum_Icc_pronicSeq_add_addDiff_sq_le_two_mul_sum_sq`):**
For every `ε ≥ 0` and `N : ℕ`, because `0 ≤ τ_ε(N + 1) ≤ 1` forces `τ_ε(N + 1)² - 1 ≤ 0`, the
combined pronic and gradient sum is bounded by `2 * ∑_{n=1}^N τ_ε(n)²` with **zero boundary error**:
`2 * ∑_{n=1}^N τ_ε(pronicSeq n) + ∑_{n=1}^N (addDiff (τ_ε) n)² ≤ 2 * ∑_{n=1}^N τ_ε(n)²`. -/
theorem sum_Icc_pronicSeq_add_addDiff_sq_le_two_mul_sum_sq {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ) :
    2 * (∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff ε (pronicSeq n)) +
      (∑ n ∈ Finset.Icc 1 N, addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ)) ≤
      2 * (∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ)) := by
  have h0 : 0 ≤ pmPowerDampedDivisorCoeff ε (N + 1) :=
    pmPowerDampedDivisorCoeff_nonneg hε (N + 1)
  have h1 : pmPowerDampedDivisorCoeff ε (N + 1) ≤ 1 :=
    pmPowerDampedDivisorCoeff_le_one hε (N + 1)
  have hsq : pmPowerDampedDivisorCoeff ε (N + 1) ^ (2 : ℕ) ≤ 1 := by nlinarith
  linarith [sum_Icc_pronicSeq_add_addDiff_sq_eq ε N]

/-- **Boundary-Free Finite Pronic Dominance by Diagonal Squares (`sum_Icc_pronicSeq_le_sum_sq`):**
For every `ε ≥ 0` and `N : ℕ`:
`∑_{n=1}^N τ_ε(pronicSeq n) ≤ ∑_{n=1}^N τ_ε(n)²` and
`∑_{n=1}^N (addDiff (τ_ε) n)² ≤ 2 * ∑_{n=1}^N τ_ε(n)²`. -/
theorem sum_Icc_pronicSeq_and_addDiff_sq_le_sum_sq {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff ε (pronicSeq n)) ≤
      (∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ)) ∧
    (∑ n ∈ Finset.Icc 1 N, addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ)) ≤
      2 * (∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ)) := by
  have hcomb := sum_Icc_pronicSeq_add_addDiff_sq_le_two_mul_sum_sq hε N
  have hpr0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff ε (pronicSeq n) :=
    Finset.sum_nonneg fun n _ => pmPowerDampedDivisorCoeff_nonneg hε (pronicSeq n)
  have hgr0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ) :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- **Exact Finite Centered Pronic–Diagonal–Gradient Conservation Identity
(`sum_Icc_centered_pronic_add_addDiff_sq_eq`):**
For every `ε : ℝ` and `N : ℕ`:
`2 * ∑_{n=1}^N widetilde_τ_ε(n) * widetilde_τ_ε(n + 1) + ∑_{n=1}^N (addDiff (τ_ε) n)² = 2 * ∑_{n=1}^N widetilde_τ_ε(n)² + widetilde_τ_ε(N + 1)² - widetilde_τ_ε(1)²`. -/
theorem sum_Icc_centered_pronic_add_addDiff_sq_eq (ε : ℝ) (N : ℕ) :
    2 * (∑ n ∈ Finset.Icc 1 N,
        pmPowerDampedCenteredDivisorCoeff ε n *
          pmPowerDampedCenteredDivisorCoeff ε (n + 1)) +
      (∑ n ∈ Finset.Icc 1 N, addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ)) =
      2 * (∑ n ∈ Finset.Icc 1 N, pmPowerDampedCenteredDivisorCoeff ε n ^ (2 : ℕ)) +
        pmPowerDampedCenteredDivisorCoeff ε (N + 1) ^ (2 : ℕ) -
        pmPowerDampedCenteredDivisorCoeff ε 1 ^ (2 : ℕ) := by
  have hsum :
      2 * (∑ n ∈ Finset.Icc 1 N,
          pmPowerDampedCenteredDivisorCoeff ε n *
            pmPowerDampedCenteredDivisorCoeff ε (n + 1)) +
        (∑ n ∈ Finset.Icc 1 N, addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ)) =
      ∑ n ∈ Finset.Icc 1 N,
        (pmPowerDampedCenteredDivisorCoeff ε n ^ (2 : ℕ) +
          pmPowerDampedCenteredDivisorCoeff ε (n + 1) ^ (2 : ℕ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    linarith [addDiff_pmPowerDampedDivisorCoeff_sq_add_two_mul_centered_pronic ε n]
  rw [hsum, sum_Icc_add_succ (fun n => pmPowerDampedCenteredDivisorCoeff ε n ^ (2 : ℕ)) N]

end
end GaloisForLFunctions.BezoutValuationIncidence
