import GaloisForLFunctions.BezoutValuationIncidence.ShiftedExponentAsymptoticDensityAndActiveMartingaleRate

/-!
# Pillar XXI: Horizon-Free Active-Deleted Energy Decomposition & Shifted-Exponent Covariance for Route PM

In Pillars XVII–XX, we discovered that at each step $n \mapsto n + 1$, the sub-horizon active
sawtooth sum evaluates to the **cutoff-independent** closed form
$$\operatorname{activeCenteredSawtoothSum}\,N\,c_\varepsilon\,(n + 1)\,n =
  -\frac{1}{2}\bigl(\tau_\varepsilon(n + 1) - \tau_{1+\varepsilon}(n + 1)\bigr).$$

In this twenty-first pillar of **Bézout–Valuation Incidence Mechanics**, we lift this decomposition
directly to the **horizon-free Route PM prefix**
$A_\varepsilon(n) = \operatorname{pmPowerDampedCenteredDivisorPrefix}\,\varepsilon\,n$ (without any
cutoff $N$ or $Y_N(1)$ discrepancy), splitting $A_\varepsilon(n)$ across step $n \mapsto n + 1$ into
its **horizon-free active pre-jump component**
$$\operatorname{pmActiveSawtoothComponent}\,\varepsilon\,(n + 1) :=
  -\frac{1}{2}\bigl(\tau_\varepsilon(n + 1) - \tau_{1+\varepsilon}(n + 1)\bigr)$$
and its **horizon-free inactive residual prefix**
$$\operatorname{pmInactiveResidualPrefix}\,\varepsilon\,n :=
  A_\varepsilon(n) - \operatorname{pmActiveSawtoothComponent}\,\varepsilon\,(n + 1).$$

## Core Main Theorems (100% Unconditional)

1. **Horizon-Free Active-Deleted Square-Increment & Discrete Energy Decomposition
   (`pmPowerDampedCenteredDivisorCoeff_sq_add_two_mul_active_eq`,
   `pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq_active_deleted`,
   `pmActiveDeletedCovarianceDiagonal_eq_diagonal_add_two_mul_active`,
   `pmPowerDampedDivisorDiscreteEnergy_eq_activeDeletedDiagonal_add_two_mul_inactive`)**:
   For every $\varepsilon : \mathbb{R}$, $n : \mathbb{N}$, and $T : \mathbb{N}$:
   - Pointwise across $n \mapsto n + 1$:
     $$A_\varepsilon(n + 1)^2 - A_\varepsilon(n)^2 =
       \operatorname{pmActiveDeletedDiagonalCoeff}\,\varepsilon\,(n + 1) +
       2\,\widetilde{\tau}_\varepsilon(n + 1)\,\operatorname{pmInactiveResidualPrefix}\,\varepsilon\,n,$$
     where $\operatorname{pmActiveDeletedDiagonalCoeff}\,\varepsilon\,m =
       \widetilde{\tau}_\varepsilon(m)\,\bigl(\tau_{1+\varepsilon}(m) - (\operatorname{pmPowerDampedDivisorDensity}\,\varepsilon).\text{re}\bigr)$.
   - Globally at any horizon $T$:
     $$\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T =
       \operatorname{pmActiveDeletedCovarianceDiagonal}\,\varepsilon\,T +
       2\,\operatorname{pmInactivePredictableMartingaleSum}\,\varepsilon\,T.$$

2. **Strict Positivity, Cesàro Mean & Logarithmic Asymptotics of `pmShiftedExponentCovariance`
   (`pmShiftedExponentCovariance_pos`,
   `tendsto_pmActiveDeletedDiagonalCoeff_mean`,
   `tendsto_pmActiveDeletedCovarianceDiagonal_div_log`)**:
   For every $\varepsilon > 0$, the asymptotic mean of $\operatorname{pmActiveDeletedDiagonalCoeff}\,\varepsilon\,m$
   is the **shifted-exponent covariance**
   $$\operatorname{pmShiftedExponentCovariance}\,\varepsilon :=
     \operatorname{pmShiftedExponentSecondDensity}\,\varepsilon -
     (\operatorname{pmPowerDampedDivisorDensity}\,\varepsilon).\text{re} \cdot
       (\operatorname{pmPowerDampedDivisorDensity}\,(1 + \varepsilon)).\text{re} > 0,$$
   and
   $$\lim_{N \to \infty} \frac{\operatorname{pmActiveDeletedCovarianceDiagonal}\,\varepsilon\,N}{\log N} =
     \operatorname{pmShiftedExponentCovariance}\,\varepsilon.$$

3. **Asymptotic Drift of the Inactive Predictable Martingale & Route PM Cancellation Criterion for RH
   (`tendsto_pmInactivePredictableMartingaleSum_div_log`,
   `tendsto_pmInactivePredictableMartingaleSum_div_log_of_half_le`,
   `riemannHypothesis_of_pmInactivePredictableMartingale_cancellation`)**:
   Whenever `pmPowerDampedFermiSource ε ∈ L²((0, ∞))` (in particular unconditionally for all
   $\varepsilon \ge 1/2$),
   $$\lim_{N \to \infty} \frac{\operatorname{pmInactivePredictableMartingaleSum}\,\varepsilon\,N}{\log N} =
     -\frac{1}{2}\,\operatorname{pmShiftedExponentCovariance}\,\varepsilon < 0.$$
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Horizon-Free Active Sawtooth Component & Inactive Residual Prefix -/

/-- The **horizon-free active pre-jump sawtooth component** at integer `m`:
`pmActiveSawtoothComponent ε m = -(1 / 2) * (pmPowerDampedDivisorCoeff ε m - pmPowerDampedDivisorCoeff (1 + ε) m)`. -/
def pmActiveSawtoothComponent (ε : ℝ) (m : ℕ) : ℝ :=
  -(1 / 2 : ℝ) * (pmPowerDampedDivisorCoeff ε m - pmPowerDampedDivisorCoeff (1 + ε) m)

/-- For every `ε : ℝ` and sub-horizon step `n + 1 ≤ N`, `activeCenteredSawtoothSum` coincides with
the horizon-free `pmActiveSawtoothComponent ε (n + 1)`. -/
theorem activeCenteredSawtoothSum_eq_pmActiveSawtoothComponent
    (ε : ℝ) {N n : ℕ} (hnN : n + 1 ≤ N) :
    activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n =
      pmActiveSawtoothComponent ε (n + 1) :=
  activeCenteredSawtoothSum_pmPowerDampedRealWeight_pred_eq ε hnN

/-- At `m = 1`, `pmActiveSawtoothComponent ε 1 = 0`. -/
@[simp]
theorem pmActiveSawtoothComponent_one (ε : ℝ) :
    pmActiveSawtoothComponent ε 1 = 0 := by
  unfold pmActiveSawtoothComponent
  rw [pmPowerDampedDivisorCoeff_one, pmPowerDampedDivisorCoeff_one]
  ring

/-- For every `ε ≥ 0` and `m : ℕ`, `0 ≤ pmActiveSawtoothComponent ε m`. -/
theorem pmActiveSawtoothComponent_nonneg {ε : ℝ} (hε : 0 ≤ ε) (m : ℕ) :
    0 ≤ pmActiveSawtoothComponent ε m := by
  unfold pmActiveSawtoothComponent
  have hle := (pmPowerDampedDivisorCoeff_le_add_one hε m).2
  linarith

/-- The **horizon-free inactive residual prefix** of Route PM before step `n ↦ n + 1`:
`pmInactiveResidualPrefix ε n = pmPowerDampedCenteredDivisorPrefix ε n - pmActiveSawtoothComponent ε (n + 1)`. -/
def pmInactiveResidualPrefix (ε : ℝ) (n : ℕ) : ℝ :=
  pmPowerDampedCenteredDivisorPrefix ε n - pmActiveSawtoothComponent ε (n + 1)

/-- **Horizon-Free Active + Inactive Split of `pmPowerDampedCenteredDivisorPrefix`
(`pmPowerDampedCenteredDivisorPrefix_eq_active_add_inactive`):**
For every `ε : ℝ` and `n : ℕ`:
`pmPowerDampedCenteredDivisorPrefix ε n = pmActiveSawtoothComponent ε (n + 1) + pmInactiveResidualPrefix ε n`. -/
theorem pmPowerDampedCenteredDivisorPrefix_eq_active_add_inactive (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n =
      pmActiveSawtoothComponent ε (n + 1) + pmInactiveResidualPrefix ε n := by
  unfold pmInactiveResidualPrefix
  ring

/-- The **horizon-free active-deleted diagonal coefficient** at integer `m`:
`pmActiveDeletedDiagonalCoeff ε m = pmPowerDampedCenteredDivisorCoeff ε m * (pmPowerDampedDivisorCoeff (1 + ε) m - (pmPowerDampedDivisorDensity ε).re)`. -/
def pmActiveDeletedDiagonalCoeff (ε : ℝ) (m : ℕ) : ℝ :=
  pmPowerDampedCenteredDivisorCoeff ε m *
    (pmPowerDampedDivisorCoeff (1 + ε) m - (pmPowerDampedDivisorDensity ε).re)

/-- At `m = 1`, `pmActiveDeletedDiagonalCoeff ε 1 = (pmPowerDampedCenteredDivisorCoeff ε 1)²`. -/
@[simp]
theorem pmActiveDeletedDiagonalCoeff_one (ε : ℝ) :
    pmActiveDeletedDiagonalCoeff ε 1 =
      pmPowerDampedCenteredDivisorCoeff ε 1 ^ (2 : ℕ) := by
  unfold pmActiveDeletedDiagonalCoeff pmPowerDampedCenteredDivisorCoeff
  rw [pmPowerDampedDivisorCoeff_one, pmPowerDampedDivisorCoeff_one]
  ring

/-- **Horizon-Free Active-Martingale Diagonal Reduction
(`pmPowerDampedCenteredDivisorCoeff_sq_add_two_mul_active_eq`):**
For every `ε : ℝ` and `m : ℕ`, adding twice the active pre-jump product
`2 * pmPowerDampedCenteredDivisorCoeff ε m * pmActiveSawtoothComponent ε m` to the centered
diagonal square `(pmPowerDampedCenteredDivisorCoeff ε m)²` yields `pmActiveDeletedDiagonalCoeff ε m`. -/
theorem pmPowerDampedCenteredDivisorCoeff_sq_add_two_mul_active_eq (ε : ℝ) (m : ℕ) :
    pmPowerDampedCenteredDivisorCoeff ε m ^ (2 : ℕ) +
      2 * pmPowerDampedCenteredDivisorCoeff ε m * pmActiveSawtoothComponent ε m =
      pmActiveDeletedDiagonalCoeff ε m := by
  unfold pmActiveDeletedDiagonalCoeff pmActiveSawtoothComponent pmPowerDampedCenteredDivisorCoeff
  ring

/-- **Horizon-Free Active-Deleted Square-Increment Identity for Route PM
(`pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq_active_deleted`):**
For every `ε : ℝ` and `n : ℕ`:
`(pmPowerDampedCenteredDivisorPrefix ε (n + 1))² - (pmPowerDampedCenteredDivisorPrefix ε n)² = pmActiveDeletedDiagonalCoeff ε (n + 1) + 2 * pmPowerDampedCenteredDivisorCoeff ε (n + 1) * pmInactiveResidualPrefix ε n`. -/
theorem pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq_active_deleted (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ (2 : ℕ) -
      pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) =
      pmActiveDeletedDiagonalCoeff ε (n + 1) +
        2 * pmPowerDampedCenteredDivisorCoeff ε (n + 1) * pmInactiveResidualPrefix ε n := by
  rw [pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq,
    pmPowerDampedCenteredDivisorPrefix_eq_active_add_inactive ε n,
    ← pmPowerDampedCenteredDivisorCoeff_sq_add_two_mul_active_eq]
  ring

/-! ## §2. Exact Horizon-Free Active-Deleted Decomposition of `pmPowerDampedDivisorDiscreteEnergy` -/

/-- The **horizon-free active-deleted covariance diagonal** at horizon `T`:
`pmActiveDeletedCovarianceDiagonal ε T = ∑_{m=1}^T pmActiveDeletedDiagonalCoeff ε m * (1 / m - 1 / (T + 1))`. -/
def pmActiveDeletedCovarianceDiagonal (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 T,
    pmActiveDeletedDiagonalCoeff ε m * (1 / (m : ℝ) - 1 / ((T : ℝ) + 1))

/-- The **active predictable martingale sum** at horizon `T`:
`pmActivePredictableMartingaleSum ε T = ∑_{n=1}^{T-1} pmPowerDampedCenteredDivisorCoeff ε (n + 1) * pmActiveSawtoothComponent ε (n + 1) * (1 / (n + 1) - 1 / (T + 1))`. -/
def pmActivePredictableMartingaleSum (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (T - 1),
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
      pmActiveSawtoothComponent ε (n + 1) *
      (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))

/-- The **inactive predictable martingale sum** at horizon `T`:
`pmInactivePredictableMartingaleSum ε T = ∑_{n=1}^{T-1} pmPowerDampedCenteredDivisorCoeff ε (n + 1) * pmInactiveResidualPrefix ε n * (1 / (n + 1) - 1 / (T + 1))`. -/
def pmInactivePredictableMartingaleSum (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (T - 1),
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
      pmInactiveResidualPrefix ε n *
      (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))

/-- **Active + Inactive Split of `pmPredictableMartingaleSum`
(`pmPredictableMartingaleSum_eq_active_add_inactive`):**
For every `ε : ℝ` and `T : ℕ`:
`pmPredictableMartingaleSum ε T = pmActivePredictableMartingaleSum ε T + pmInactivePredictableMartingaleSum ε T`. -/
theorem pmPredictableMartingaleSum_eq_active_add_inactive (ε : ℝ) (T : ℕ) :
    pmPredictableMartingaleSum ε T =
      pmActivePredictableMartingaleSum ε T + pmInactivePredictableMartingaleSum ε T := by
  unfold pmPredictableMartingaleSum pmActivePredictableMartingaleSum
    pmInactivePredictableMartingaleSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [pmPowerDampedCenteredDivisorPrefix_eq_active_add_inactive ε n]
  ring

/-- **Absorption of `2 * pmActivePredictableMartingaleSum` into the Covariance Diagonal
(`pmActiveDeletedCovarianceDiagonal_eq_diagonal_add_two_mul_active`):**
For every `ε : ℝ` and `T : ℕ`:
`pmActiveDeletedCovarianceDiagonal ε T = pmPowerDampedDivisorCovarianceDiagonal ε T + 2 * pmActivePredictableMartingaleSum ε T`. -/
theorem pmActiveDeletedCovarianceDiagonal_eq_diagonal_add_two_mul_active (ε : ℝ) (T : ℕ) :
    pmActiveDeletedCovarianceDiagonal ε T =
      pmPowerDampedDivisorCovarianceDiagonal ε T + 2 * pmActivePredictableMartingaleSum ε T := by
  by_cases hT : 1 ≤ T
  · unfold pmActiveDeletedCovarianceDiagonal
    rw [sum_Icc_one_split_head_and_shift
      (fun m : ℕ => pmActiveDeletedDiagonalCoeff ε m *
        (1 / (m : ℝ) - 1 / ((T : ℝ) + 1))) hT,
      pmPowerDampedDivisorCovarianceDiagonal_eq_abel_diagonal ε hT]
    unfold pmActivePredictableMartingaleSum
    rw [pmActiveDeletedDiagonalCoeff_one, Finset.mul_sum]
    have hsum :
        (∑ n ∈ Finset.Icc 1 (T - 1),
          pmActiveDeletedDiagonalCoeff ε (n + 1) *
            (1 / ((n + 1 : ℕ) : ℝ) - 1 / ((T : ℝ) + 1))) =
        (∑ n ∈ Finset.Icc 1 (T - 1),
          pmPowerDampedCenteredDivisorCoeff ε (n + 1) ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          2 * (pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
            pmActiveSawtoothComponent ε (n + 1) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← pmPowerDampedCenteredDivisorCoeff_sq_add_two_mul_active_eq]
      push_cast
      ring
    rw [hsum]
    norm_num
    ring
  · have hT0 : T = 0 := by omega
    subst hT0
    unfold pmActiveDeletedCovarianceDiagonal pmPowerDampedDivisorCovarianceDiagonal
      pmActivePredictableMartingaleSum
    simp

/-- **Horizon-Free Active-Deleted Decomposition of `pmPowerDampedDivisorDiscreteEnergy`
(`pmPowerDampedDivisorDiscreteEnergy_eq_activeDeletedDiagonal_add_two_mul_inactive`):**
For every `ε : ℝ` and `T : ℕ`, the Route PM discrete energy decomposes into the horizon-free
active-deleted covariance diagonal plus twice the purely inactive predictable martingale sum:
`pmPowerDampedDivisorDiscreteEnergy ε T = pmActiveDeletedCovarianceDiagonal ε T + 2 * pmInactivePredictableMartingaleSum ε T`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_eq_activeDeletedDiagonal_add_two_mul_inactive
    (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T =
      pmActiveDeletedCovarianceDiagonal ε T + 2 * pmInactivePredictableMartingaleSum ε T := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_diagonal_add_two_mul_pmPredictableMartingaleSum,
    pmPredictableMartingaleSum_eq_active_add_inactive,
    pmActiveDeletedCovarianceDiagonal_eq_diagonal_add_two_mul_active]
  ring

/-! ## §3. Shifted-Exponent Covariance, Strict Positivity, Harmonic Asymptotics & RH Criterion -/

/-- The **shifted-exponent covariance** between `τ_ε(n)` and `τ_{1+ε}(n)`:
`pmShiftedExponentCovariance ε = pmShiftedExponentSecondDensity ε - (pmPowerDampedDivisorDensity ε).re * (pmPowerDampedDivisorDensity (1 + ε)).re`. -/
def pmShiftedExponentCovariance (ε : ℝ) : ℝ :=
  pmShiftedExponentSecondDensity ε -
    (pmPowerDampedDivisorDensity ε).re * (pmPowerDampedDivisorDensity (1 + ε)).re

/-- For every `σ > 0`, `0 < (pmPowerDampedDivisorDensity σ).re`. -/
theorem pmPowerDampedDivisorDensity_re_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < (pmPowerDampedDivisorDensity σ).re := by
  have hnonneg : 0 ≤ (pmPowerDampedDivisorDensity σ).re := by
    apply ge_of_tendsto' (pmPowerDampedDivisorDensity_hasProd_real hσ)
    intro S
    refine Finset.prod_nonneg fun p _ => ?_
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_le
    have hp0 : (0 : ℝ) < p := by linarith
    have ht1 : (p : ℝ) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr hσ.le)
    have hdiv : (p : ℝ) ^ (-σ) / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr (by linarith)
    linarith
  exact lt_of_le_of_ne hnonneg (pmPowerDampedDivisorDensity_re_ne_zero hσ).symm

/-- **Strict Positivity of `pmShiftedExponentCovariance` (`pmShiftedExponentCovariance_pos`):**
For every `ε > 0`, `0 < pmShiftedExponentCovariance ε`. -/
theorem pmShiftedExponentCovariance_pos {ε : ℝ} (hε : 0 < ε) :
    0 < pmShiftedExponentCovariance ε := by
  have hlocal (p : Nat.Primes) :
      (1 - (p : ℝ) ^ (-ε) / (p : ℝ)) * (1 - (p : ℝ) ^ (-(1 + ε)) / (p : ℝ)) <
        1 - pmShiftedExponentSecondWeight ε p / (p : ℝ) := by
    apply sub_pos.mp
    rw [pmShiftedExponentFactor_gap ε p.property.pos]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    exact div_pos (mul_pos (sq_pos_of_pos (Real.rpow_pos_of_pos hp0 _)) (sub_pos.mpr hp1))
      (pow_pos hp0 3)
  have hf0 (p : Nat.Primes) :
      0 ≤ (1 - (p : ℝ) ^ (-ε) / (p : ℝ)) * (1 - (p : ℝ) ^ (-(1 + ε)) / (p : ℝ)) := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_le
    have hp0 : (0 : ℝ) < p := by linarith
    have ht1 : (p : ℝ) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr hε.le)
    have hu1 : (p : ℝ) ^ (-(1 + ε)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
    exact mul_nonneg (sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith)))
      (sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith)))
  have hprod_pos :
      0 < (pmPowerDampedDivisorDensity ε).re * (pmPowerDampedDivisorDensity (1 + ε)).re :=
    mul_pos (pmPowerDampedDivisorDensity_re_pos hε)
      (pmPowerDampedDivisorDensity_re_pos (by linarith))
  have h := pm_hasProd_lt_real
    ((pmPowerDampedDivisorDensity_hasProd_real hε).mul
      (pmPowerDampedDivisorDensity_hasProd_real (by linarith : 0 < 1 + ε)))
    (pmShiftedExponentSecondDensity_hasProd hε)
    hf0 (fun p => (hlocal p).le) hprod_pos (hlocal ⟨2, Nat.prime_two⟩)
  exact sub_pos.mpr h

/-- Expansion of `∑_{n=1}^N pmActiveDeletedDiagonalCoeff ε n` into four elementary sums. -/
theorem pm_activeDeleted_sum_expand (ε : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, pmActiveDeletedDiagonalCoeff ε n) =
      (∑ n ∈ Finset.Icc 1 N,
        pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n) -
      (pmPowerDampedDivisorDensity ε).re *
        (∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff ε n) -
      (pmPowerDampedDivisorDensity ε).re *
        (∑ n ∈ Finset.Icc 1 N, pmPowerDampedDivisorCoeff (1 + ε) n) +
      (pmPowerDampedDivisorDensity ε).re ^ 2 * (N : ℝ) := by
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      pmActiveDeletedDiagonalCoeff ε n =
        (pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n -
          (pmPowerDampedDivisorDensity ε).re * pmPowerDampedDivisorCoeff ε n -
          (pmPowerDampedDivisorDensity ε).re * pmPowerDampedDivisorCoeff (1 + ε) n) +
        (pmPowerDampedDivisorDensity ε).re ^ 2 := by
    intro n _
    unfold pmActiveDeletedDiagonalCoeff pmPowerDampedCenteredDivisorCoeff
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel]
  ring

/-- **Cesàro Mean Convergence of `pmActiveDeletedDiagonalCoeff`
(`tendsto_pmActiveDeletedDiagonalCoeff_mean`):**
For every `ε > 0`:
`Tendsto (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, pmActiveDeletedDiagonalCoeff ε n) / x) atTop (𝓝 (pmShiftedExponentCovariance ε))`. -/
theorem tendsto_pmActiveDeletedDiagonalCoeff_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, pmActiveDeletedDiagonalCoeff ε n) / x)
      atTop (𝓝 (pmShiftedExponentCovariance ε)) := by
  have hf : Tendsto (fun x : ℝ => ((⌊x⌋₊ : ℕ) : ℝ) / x) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul] using
      (tendsto_nat_floor_mul_div_atTop (a := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1))
  have h1 := tendsto_pmPowerDampedDivisorCoeff_mul_add_one_mean hε
  have h2 := (tendsto_pmPowerDampedDivisorSum_div_real hε).const_mul
    (pmPowerDampedDivisorDensity ε).re
  have h3 := (tendsto_pmPowerDampedDivisorSum_div_real (by linarith : 0 < 1 + ε)).const_mul
    (pmPowerDampedDivisorDensity ε).re
  have h4 := hf.const_mul ((pmPowerDampedDivisorDensity ε).re ^ 2)
  have h := ((h1.sub h2).sub h3).add h4
  have he :
      pmShiftedExponentSecondDensity ε -
        (pmPowerDampedDivisorDensity ε).re * (pmPowerDampedDivisorDensity ε).re -
        (pmPowerDampedDivisorDensity ε).re * (pmPowerDampedDivisorDensity (1 + ε)).re +
        (pmPowerDampedDivisorDensity ε).re ^ 2 * 1 =
      pmShiftedExponentCovariance ε := by
    dsimp only [pmShiftedExponentCovariance]
    ring
  rw [he] at h
  convert h using 1
  funext x
  rw [pm_activeDeleted_sum_expand ε ⌊x⌋₊]
  unfold pmPowerDampedDivisorSum
  ring

/-- Discrete Cesàro mean convergence of `pmActiveDeletedDiagonalCoeff` along `N : ℕ`. -/
theorem tendsto_pmActiveDeletedDiagonalCoeff_nat_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, pmActiveDeletedDiagonalCoeff ε n) / (N : ℝ))
      atTop (𝓝 (pmShiftedExponentCovariance ε)) := by
  have h := (tendsto_pmActiveDeletedDiagonalCoeff_mean hε).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  simpa only [Function.comp_def, Nat.floor_natCast] using h

/-- Harmonic average convergence of `pmActiveDeletedDiagonalCoeff` along `N : ℕ`. -/
theorem tendsto_pmActiveDeletedDiagonalCoeff_harmonic {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, pmActiveDeletedDiagonalCoeff ε n / (n : ℝ)) / Real.log N)
      atTop (𝓝 (pmShiftedExponentCovariance ε)) :=
  pm_tendsto_harmonic_average_of_mean (tendsto_pmActiveDeletedDiagonalCoeff_nat_mean hε)

/-- Shifted-denominator Cesàro mean convergence of `pmActiveDeletedDiagonalCoeff` along `N : ℕ`. -/
theorem tendsto_pmActiveDeletedDiagonalCoeff_shift_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, pmActiveDeletedDiagonalCoeff ε n) / ((N : ℝ) + 1))
      atTop (𝓝 (pmShiftedExponentCovariance ε)) := by
  have h := (tendsto_pmActiveDeletedDiagonalCoeff_nat_mean hε).mul
    (tendsto_natCast_div_add_atTop (1 : ℝ))
  simpa only [mul_one, Pi.mul_def] using h.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp)

/-- Decomposition of `pmActiveDeletedCovarianceDiagonal` into harmonic and shifted-mean sums. -/
theorem pmActiveDeletedCovarianceDiagonal_eq (ε : ℝ) (N : ℕ) :
    pmActiveDeletedCovarianceDiagonal ε N =
      (∑ n ∈ Finset.Icc 1 N, pmActiveDeletedDiagonalCoeff ε n / (n : ℝ)) -
        (∑ n ∈ Finset.Icc 1 N, pmActiveDeletedDiagonalCoeff ε n) / ((N : ℝ) + 1) := by
  simp only [pmActiveDeletedCovarianceDiagonal, mul_sub, mul_one_div,
    Finset.sum_sub_distrib, Finset.sum_div]

/-- **Logarithmic Asymptotics of `pmActiveDeletedCovarianceDiagonal`
(`tendsto_pmActiveDeletedCovarianceDiagonal_div_log`):**
For every `ε > 0`:
`Tendsto (fun N : ℕ => pmActiveDeletedCovarianceDiagonal ε N / Real.log N) atTop (𝓝 (pmShiftedExponentCovariance ε))`. -/
theorem tendsto_pmActiveDeletedCovarianceDiagonal_div_log {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => pmActiveDeletedCovarianceDiagonal ε N / Real.log N)
      atTop (𝓝 (pmShiftedExponentCovariance ε)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (tendsto_pmActiveDeletedDiagonalCoeff_harmonic hε).sub
    ((tendsto_pmActiveDeletedDiagonalCoeff_shift_mean hε).div_atTop hlog)
  have hl : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, pmActiveDeletedDiagonalCoeff ε n / (n : ℝ)) / Real.log N -
        ((∑ n ∈ Finset.Icc 1 N, pmActiveDeletedDiagonalCoeff ε n) / ((N : ℝ) + 1)) /
          Real.log N)
      atTop (𝓝 (pmShiftedExponentCovariance ε)) := by
    simpa [Pi.sub_def] using h
  refine hl.congr fun N => ?_
  rw [pmActiveDeletedCovarianceDiagonal_eq]
  ring

/-- **Logarithmic Asymptotic Drift of `pmInactivePredictableMartingaleSum`
(`tendsto_pmInactivePredictableMartingaleSum_div_log`):**
For every `ε > 0` such that `pmPowerDampedFermiSource ε ∈ L²((0, ∞))`, the purely inactive
predictable martingale sum `pmInactivePredictableMartingaleSum ε N` divided by `log N` converges
as `N → ∞` to `-pmShiftedExponentCovariance ε / 2 < 0`. -/
theorem tendsto_pmInactivePredictableMartingaleSum_div_log {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    Tendsto (fun N : ℕ => pmInactivePredictableMartingaleSum ε N / Real.log N)
      atTop (𝓝 (-pmShiftedExponentCovariance ε / 2)) := by
  have h := ((tendsto_pmPowerDampedDivisorDiscreteEnergy_div_log hε hf).sub
    (tendsto_pmActiveDeletedCovarianceDiagonal_div_log hε)).div_const (2 : ℝ)
  have hl : Tendsto (fun N : ℕ =>
      (pmPowerDampedDivisorDiscreteEnergy ε N / Real.log N -
        pmActiveDeletedCovarianceDiagonal ε N / Real.log N) / 2)
      atTop (𝓝 (-pmShiftedExponentCovariance ε / 2)) := by
    simpa [Pi.sub_def] using h
  refine hl.congr fun N => ?_
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_activeDeletedDiagonal_add_two_mul_inactive]
  ring

/-- **Unconditional Logarithmic Asymptotic Drift of `pmInactivePredictableMartingaleSum` for `ε ≥ 1/2`
(`tendsto_pmInactivePredictableMartingaleSum_div_log_of_half_le`):**
For every `ε ≥ 1/2`, unconditionally:
`Tendsto (fun N => pmInactivePredictableMartingaleSum ε N / Real.log N) atTop (𝓝 (-pmShiftedExponentCovariance ε / 2))`. -/
theorem tendsto_pmInactivePredictableMartingaleSum_div_log_of_half_le
    {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    Tendsto (fun N : ℕ => pmInactivePredictableMartingaleSum ε N / Real.log N)
      atTop (𝓝 (-pmShiftedExponentCovariance ε / 2)) :=
  tendsto_pmInactivePredictableMartingaleSum_div_log (by linarith)
    (memLp_pmPowerDampedFermiSource_of_half_le hε)

/-- **Route PM Active-Deleted / Inactive Martingale Cancellation Criterion for the Riemann Hypothesis
(`riemannHypothesis_of_pmInactivePredictableMartingale_cancellation`):**
If for every `δ > 0` there exist `ε ∈ (0, δ)` and a uniform bound `B : ℝ` such that for all `T ≥ 1`,
`pmActiveDeletedCovarianceDiagonal ε T + 2 * pmInactivePredictableMartingaleSum ε T ≤ B`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_pmInactivePredictableMartingale_cancellation
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, 1 ≤ T →
        pmActiveDeletedCovarianceDiagonal ε T +
          2 * pmInactivePredictableMartingaleSum ε T ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget
  intro δ hδ
  obtain ⟨ε, hε, hεδ, B, hB⟩ := h δ hδ
  refine ⟨ε, hε, hεδ, max B 0, fun T => ?_⟩
  by_cases hT : 1 ≤ T
  · rw [pmPowerDampedDivisorDiscreteEnergy_eq_activeDeletedDiagonal_add_two_mul_inactive]
    exact (hB T hT).trans (le_max_left B 0)
  · have hT0 : T = 0 := by omega
    subst hT0
    unfold pmPowerDampedDivisorDiscreteEnergy
    simp [le_max_right B 0]

end
end GaloisForLFunctions.BezoutValuationIncidence
