import GaloisForLFunctions.BezoutValuationIncidence.CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget

/-!
# Pronic Potential Self-Cancellation, the Non-Circular Interior Gradient Conservation Law, and Pure-Interior Energy Equivalence

In `InteriorMartingaleQuadraticGradientAndRenormalizedDriftBudget`, summation by parts along the
compensated harmonic kernel $w_T(n) = \frac{1}{n + 1} - \frac{1}{T + 1}$ yielded:
$$2\,\operatorname{pmBezoutInteriorMartingaleSum}\,\varepsilon\,T =
  \sum_{n=1}^T \frac{\operatorname{pmInteriorActivePotential}\,\varepsilon\,n}{\operatorname{pronicSeq}\,n} -
  \operatorname{pmInteriorActivePotential}\,\varepsilon\,1\left(1 - \frac{1}{T + 1}\right) -
  \operatorname{pmBezoutInteriorGradientSum}\,\varepsilon\,T -
  2\,\operatorname{pmBezoutLocalImpulseCrossSum}\,\varepsilon\,T,$$
where
$$\operatorname{pmInteriorActivePotential}\,\varepsilon\,n =
  I_\varepsilon(n)^2 + 2\,I_\varepsilon(n)\,\operatorname{addDiff}(S_\varepsilon)\,n =
  A_\varepsilon(n)^2 - \bigl(\operatorname{addDiff}(S_\varepsilon)\,n\bigr)^2.$$

In this module, we complete **Step 2** of the Wall 1 Bézout programme by resolving the apparent
circularity between $\sum_{n=1}^T \frac{\operatorname{pmInteriorActivePotential}\,\varepsilon\,n}{\operatorname{pronicSeq}\,n}$
and $\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T = \sum_{n=1}^T \frac{A_\varepsilon(n)^2}{\operatorname{pronicSeq}\,n}$:

1. **Uniform `[0, 1 / 4]` Bounds on `pmActivePairPronicEnergy` & Exact Pronic Split of `pmInteriorActivePotential`
   (`pmActiveSawtoothComponent_le_half`,
   `abs_addDiff_pmActiveSawtoothComponent_le_half`,
   `addDiff_pmActiveSawtoothComponent_sq_le_quarter`,
   `pmActivePairPronicEnergy_bounds`,
   `sum_pmInteriorActivePotential_div_pronicSeq_eq`):**
   - For every $\varepsilon \ge 0$ and $n \in \mathbb{N}$, $0 \le S_\varepsilon(n) \le 1/2$, so
     $|\operatorname{addDiff}(S_\varepsilon)\,n| \le 1/2$ and $(\operatorname{addDiff}(S_\varepsilon)\,n)^2 \le 1/4$.
   - Consequently, the active-pair pronic energy
     $\operatorname{pmActivePairPronicEnergy}\,\varepsilon\,T = \sum_{n=1}^T \frac{(\operatorname{addDiff} S_\varepsilon(n))^2}{\operatorname{pronicSeq}\,n}$
     satisfies $0 \le \operatorname{pmActivePairPronicEnergy}\,\varepsilon\,T \le 1/4$ uniformly for all $T \in \mathbb{N}$ and $\varepsilon \ge 0$, and:
     $$\sum_{n=1}^T \frac{\operatorname{pmInteriorActivePotential}\,\varepsilon\,n}{\operatorname{pronicSeq}\,n} =
       \operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T -
       \operatorname{pmActivePairPronicEnergy}\,\varepsilon\,T.$$

2. **Exact Self-Cancellation of `E_T` & the Non-Circular Interior Gradient + Local-Impulse Conservation Law
   (`two_mul_pmBezoutInteriorMartingaleSum_eq_discreteEnergy_sub`,
   `pmBezoutInteriorGradient_add_two_mul_localImpulse_eq_activeDeleted_add_predecessorPeak`,
   `tendsto_pmBezoutInteriorGradient_add_two_mul_localImpulse_div_log`,
   `tendsto_two_mul_pmInteriorLogCounterterm_div_parameter`):**
   - Substituting $\sum_{n=1}^T \frac{\Phi_\varepsilon(n)}{\operatorname{pronicSeq}\,n} = E_T - \operatorname{pmActivePairPronicEnergy}\,\varepsilon\,T$
     into the summation-by-parts identity for $2 M_T^{\text{int}}$ and combining with the complete
     energy identity $E_T = D_T^{\text{act}} + 2 P_T^{\text{pred}} + 2 M_T^{\text{int}}$
     **cancels $E_T$ and $2 M_T^{\text{int}}$ identically from both sides**, leaving the exact
     non-circular conservation law:
     $$\operatorname{pmBezoutInteriorGradientSum}\,\varepsilon\,T +
       2\,\operatorname{pmBezoutLocalImpulseCrossSum}\,\varepsilon\,T =
       \operatorname{pmActiveDeletedCovarianceDiagonal}\,\varepsilon\,T +
       2\,\operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,T -
       \operatorname{pmActivePairPronicEnergy}\,\varepsilon\,T -
       \operatorname{pmInteriorActivePotential}\,\varepsilon\,1\left(1 - \frac{1}{T + 1}\right).$$
   - Dividing by $\log T$ proves **unconditionally for every $\varepsilon > 0$** (without any `MemLp`
     hypothesis!) that the combined interior gradient energy plus local impulse cross-sum has exact
     logarithmic drift $2\,\operatorname{pmInteriorLogCounterterm}\,\varepsilon$, whose small-damping
     slope as $\varepsilon \to 0^+$ is $1 - \operatorname{pmAdjacentArtinConstant} \ge 7/12 > 0$.

3. **Two-Sided Equivalence Between `pmPowerDampedDivisorDiscreteEnergy` and `pmBezoutInteriorPronicEnergy`
   (`pmPowerDampedDivisorDiscreteEnergy_le_two_mul_interiorPronic_add_half`,
   `pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half`,
   `riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded`):**
   - For every $\varepsilon \ge 0$ and $T \in \mathbb{N}$, the pure-interior pronic energy
     $\operatorname{pmBezoutInteriorPronicEnergy}\,\varepsilon\,T = \sum_{n=1}^T \frac{I_\varepsilon(n)^2}{\operatorname{pronicSeq}\,n}$
     and $\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T$ obey the explicit two-sided comparison:
     $$\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T \le
       2\,\operatorname{pmBezoutInteriorPronicEnergy}\,\varepsilon\,T + \frac{1}{2},$$
     $$\operatorname{pmBezoutInteriorPronicEnergy}\,\varepsilon\,T \le
       2\,\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T + \frac{1}{2},$$
     yielding an unconditional pure-interior pronic energy criterion for `RiemannHypothesis`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Uniform `[0, 1 / 4]` Bounds on `pmActivePairPronicEnergy` & Exact Pronic Split -/

/-- For every `ε ≥ 0` and `m : ℕ`, `pmActiveSawtoothComponent ε m ≤ 1 / 2`. -/
theorem pmActiveSawtoothComponent_le_half {ε : ℝ} (hε : 0 ≤ ε) (m : ℕ) :
    pmActiveSawtoothComponent ε m ≤ 1 / 2 := by
  unfold pmActiveSawtoothComponent
  have h0 : 0 ≤ pmPowerDampedDivisorCoeff ε m := pmPowerDampedDivisorCoeff_nonneg hε m
  have h1 : pmPowerDampedDivisorCoeff (1 + ε) m ≤ 1 :=
    pmPowerDampedDivisorCoeff_le_one (by linarith) m
  linarith

/-- **Pointwise `1 / 2` Bound on `|addDiff (pmActiveSawtoothComponent ε) n|`
(`abs_addDiff_pmActiveSawtoothComponent_le_half`):**
For every `ε ≥ 0` and `n : ℕ`, because both `pmActiveSawtoothComponent ε (n + 1)` and
`pmActiveSawtoothComponent ε n` lie in `[0, 1 / 2]`, their difference has absolute value at most `1 / 2`. -/
theorem abs_addDiff_pmActiveSawtoothComponent_le_half {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    |addDiff (pmActiveSawtoothComponent ε) n| ≤ 1 / 2 := by
  unfold addDiff
  have h0_low := pmActiveSawtoothComponent_nonneg hε n
  have h0_high := pmActiveSawtoothComponent_le_half hε n
  have h1_low := pmActiveSawtoothComponent_nonneg hε (n + 1)
  have h1_high := pmActiveSawtoothComponent_le_half hε (n + 1)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Pointwise `1 / 4` Bound on `(addDiff (pmActiveSawtoothComponent ε) n)²`
(`addDiff_pmActiveSawtoothComponent_sq_le_quarter`):**
For every `ε ≥ 0` and `n : ℕ`:
`0 ≤ addDiff (pmActiveSawtoothComponent ε) n ^ 2 ≤ 1 / 4`. -/
theorem addDiff_pmActiveSawtoothComponent_sq_le_quarter {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) ∧
      addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) ≤ 1 / 4 := by
  refine ⟨sq_nonneg _, ?_⟩
  have habs := abs_addDiff_pmActiveSawtoothComponent_le_half hε n
  obtain ⟨hlow, hhigh⟩ := abs_le.mp habs
  nlinarith

/-- The pronic series of the squared active-pair increment `addDiff (pmActiveSawtoothComponent ε) n`:
`pmActivePairPronicEnergy ε T = ∑_{n=1}^T (addDiff (pmActiveSawtoothComponent ε) n)² / pronicSeq n`. -/
def pmActivePairPronicEnergy (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 T,
    addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) / (pronicSeq n : ℝ)

/-- **Uniform `[0, 1 / 4]` Bounds on `pmActivePairPronicEnergy ε T`
(`pmActivePairPronicEnergy_bounds`):**
For every `ε ≥ 0` and `T : ℕ`:
`0 ≤ pmActivePairPronicEnergy ε T ≤ 1 / 4`. -/
theorem pmActivePairPronicEnergy_bounds {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    0 ≤ pmActivePairPronicEnergy ε T ∧ pmActivePairPronicEnergy ε T ≤ 1 / 4 := by
  unfold pmActivePairPronicEnergy
  refine ⟨Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _), ?_⟩
  have hle :
      (∑ n ∈ Finset.Icc 1 T,
        addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) / (pronicSeq n : ℝ)) ≤
      ∑ n ∈ Finset.Icc 1 T, (1 / 4 : ℝ) * ((1 : ℝ) / (pronicSeq n : ℝ)) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have hsq := (addDiff_pmActiveSawtoothComponent_sq_le_quarter hε n).2
    have hpr : (0 : ℝ) ≤ 1 / (pronicSeq n : ℝ) := by positivity
    calc
      addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) / (pronicSeq n : ℝ)
        = addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) * ((1 : ℝ) / (pronicSeq n : ℝ)) := by
            ring
      _ ≤ (1 / 4 : ℝ) * ((1 : ℝ) / (pronicSeq n : ℝ)) := mul_le_mul_of_nonneg_right hsq hpr
  rw [← Finset.mul_sum] at hle
  linarith [sum_one_div_pronicSeq_le_one T]

/-- **Exact Pronic Decomposition of `pmInteriorActivePotential`
(`sum_pmInteriorActivePotential_div_pronicSeq_eq`):**
For every `ε : ℝ` and `T : ℕ`:
`∑_{n=1}^T pmInteriorActivePotential ε n / pronicSeq n = pmPowerDampedDivisorDiscreteEnergy ε T - pmActivePairPronicEnergy ε T`. -/
theorem sum_pmInteriorActivePotential_div_pronicSeq_eq (ε : ℝ) (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, pmInteriorActivePotential ε n / (pronicSeq n : ℝ)) =
      pmPowerDampedDivisorDiscreteEnergy ε T - pmActivePairPronicEnergy ε T := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
  unfold pmActivePairPronicEnergy pmInteriorActivePotential
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [pmBezoutInteriorPrefix_sq_add_two_mul_eq_prefix_sq_sub_active_sq]
  ring

/-! ## §2. Exact Self-Cancellation of `E_T` & the Non-Circular Interior Gradient Conservation Law -/

/-- The compensated interior quadratic-gradient energy at horizon `T`:
`pmBezoutInteriorGradientSum ε T = ∑_{n=1}^{T-1} (addDiff (pmBezoutInteriorPrefix ε) n)² * (1 / (n + 1) - 1 / (T + 1))`. -/
def pmBezoutInteriorGradientSum (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (T - 1),
    addDiff (pmBezoutInteriorPrefix ε) n ^ (2 : ℕ) *
      (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))

/-- `pmBezoutInteriorGradientSum ε T` is non-negative for all `ε : ℝ` and `T : ℕ`. -/
theorem pmBezoutInteriorGradientSum_nonneg (ε : ℝ) (T : ℕ) :
    0 ≤ pmBezoutInteriorGradientSum ε T := by
  unfold pmBezoutInteriorGradientSum
  refine Finset.sum_nonneg fun n hn => ?_
  obtain ⟨_, hnT⟩ := Finset.mem_Icc.mp hn
  have hle : (n : ℝ) + 1 ≤ (T : ℝ) + 1 := by exact_mod_cast (by omega : n + 1 ≤ T + 1)
  exact mul_nonneg (sq_nonneg _)
    (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) hle))

/-- The compensated local-impulse cross-sum at horizon `T`:
`pmBezoutLocalImpulseCrossSum ε T = ∑_{n=1}^{T-1} addDiff (pmActiveSawtoothComponent ε) (n + 1) * addDiff (pmBezoutInteriorPrefix ε) n * (1 / (n + 1) - 1 / (T + 1))`. -/
def pmBezoutLocalImpulseCrossSum (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (T - 1),
    addDiff (pmActiveSawtoothComponent ε) (n + 1) *
      addDiff (pmBezoutInteriorPrefix ε) n *
      (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))

/-- **Discrete-Energy Form of the Summation-by-Parts Identity for `2 * pmBezoutInteriorMartingaleSum`
(`two_mul_pmBezoutInteriorMartingaleSum_eq_discreteEnergy_sub`):**
For every `ε : ℝ` and `T ≥ 1`:
`2 * pmBezoutInteriorMartingaleSum ε T = pmPowerDampedDivisorDiscreteEnergy ε T - pmActivePairPronicEnergy ε T - pmInteriorActivePotential ε 1 * (1 - 1 / (T + 1)) - pmBezoutInteriorGradientSum ε T - 2 * pmBezoutLocalImpulseCrossSum ε T`. -/
theorem two_mul_pmBezoutInteriorMartingaleSum_eq_discreteEnergy_sub
    (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    2 * pmBezoutInteriorMartingaleSum ε T =
      pmPowerDampedDivisorDiscreteEnergy ε T -
        pmActivePairPronicEnergy ε T -
        pmInteriorActivePotential ε 1 * (1 - 1 / ((T : ℝ) + 1)) -
        pmBezoutInteriorGradientSum ε T -
        2 * pmBezoutLocalImpulseCrossSum ε T := by
  rw [two_mul_pmBezoutInteriorMartingaleSum_eq_pronic_sub_grad_sub_local ε hT,
    sum_pmInteriorActivePotential_div_pronicSeq_eq]
  rfl

/-- **Exact Non-Circular Interior Gradient + Local-Impulse Conservation Law
(`pmBezoutInteriorGradient_add_two_mul_localImpulse_eq_activeDeleted_add_predecessorPeak`):**
Combining `two_mul_pmBezoutInteriorMartingaleSum_eq_discreteEnergy_sub` with the complete energy
decomposition `E_T = D_T^act + 2 * P_T^pred + 2 * M_T^int` **cancels `E_T` and `2 * M_T^int`
identically from both sides**, proving that for every `ε : ℝ` and `T ≥ 1`:
`pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T = pmActiveDeletedCovarianceDiagonal ε T + 2 * pmPredecessorPeakMartingaleSum ε T - pmActivePairPronicEnergy ε T - pmInteriorActivePotential ε 1 * (1 - 1 / (T + 1))`. -/
theorem pmBezoutInteriorGradient_add_two_mul_localImpulse_eq_activeDeleted_add_predecessorPeak
    (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T =
      pmActiveDeletedCovarianceDiagonal ε T +
        2 * pmPredecessorPeakMartingaleSum ε T -
        pmActivePairPronicEnergy ε T -
        pmInteriorActivePotential ε 1 * (1 - 1 / ((T : ℝ) + 1)) := by
  have h1 := two_mul_pmBezoutInteriorMartingaleSum_eq_discreteEnergy_sub ε hT
  have h2 := pmPowerDampedDivisorDiscreteEnergy_eq_activeDeleted_add_predecessorPeak_add_bezoutInterior ε T
  linarith

/-- **Unconditional Logarithmic Drift of `pmBezoutInteriorGradientSum + 2 * pmBezoutLocalImpulseCrossSum`
(`tendsto_pmBezoutInteriorGradient_add_two_mul_localImpulse_div_log`):**
For **every** `ε > 0` (without any `MemLp` hypothesis!), the combined interior gradient energy plus
twice the local impulse cross-sum divided by `log T` converges as `T → ∞` to
`2 * pmInteriorLogCounterterm ε`. -/
theorem tendsto_pmBezoutInteriorGradient_add_two_mul_localImpulse_div_log
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℕ =>
      (pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T) /
        Real.log T)
      atTop (𝓝 (2 * pmInteriorLogCounterterm ε)) := by
  have hlog : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlead :
      Tendsto (fun T : ℕ =>
        (pmActiveDeletedCovarianceDiagonal ε T +
          2 * pmPredecessorPeakMartingaleSum ε T) / Real.log T)
        atTop (𝓝 (2 * pmInteriorLogCounterterm ε)) := by
    have h := (tendsto_pmActiveDeletedCovarianceDiagonal_div_log hε).add
      ((tendsto_pmPredecessorPeakMartingaleSum_div_log hε).const_mul (2 : ℝ))
    have heq :
        pmShiftedExponentCovariance ε + 2 * pmPredecessorPeakLogDrift ε =
          2 * pmInteriorLogCounterterm ε := by
      linarith [pmInteriorLogCounterterm_eq_half_shiftedCovariance_add_predecessorPeak ε]
    rw [← heq]
    refine h.congr fun T => ?_
    ring
  have hrem :
      Tendsto (fun T : ℕ =>
        (pmActivePairPronicEnergy ε T +
          pmInteriorActivePotential ε 1 * (1 - 1 / ((T : ℝ) + 1))) / Real.log T)
        atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      ((tendsto_const_nhds
        (x := (1 / 4 : ℝ) + |pmInteriorActivePotential ε 1|)).div_atTop hlog)
    filter_upwards [eventually_ge_atTop 2] with T hT
    have hlog0 : 0 < Real.log T := Real.log_pos (by exact_mod_cast hT)
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog0]
    apply div_le_div_of_nonneg_right _ hlog0.le
    have hpr := pmActivePairPronicEnergy_bounds hε.le T
    have h1T0 : 0 ≤ 1 - 1 / ((T : ℝ) + 1) := by
      have : (1 : ℝ) / ((T : ℝ) + 1) ≤ 1 :=
        div_le_self zero_le_one (by linarith [Nat.cast_nonneg (α := ℝ) T])
      linarith
    have h1T1 : 1 - 1 / ((T : ℝ) + 1) ≤ 1 := by
      have : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
      linarith
    have habs_add := abs_add_le (pmActivePairPronicEnergy ε T)
      (pmInteriorActivePotential ε 1 * (1 - 1 / ((T : ℝ) + 1)))
    rw [abs_of_nonneg hpr.1, abs_mul, abs_of_nonneg h1T0] at habs_add
    have hmul :
        |pmInteriorActivePotential ε 1| * (1 - 1 / ((T : ℝ) + 1)) ≤
          |pmInteriorActivePotential ε 1| * 1 :=
      mul_le_mul_of_nonneg_left h1T1 (abs_nonneg _)
    linarith [hpr.2]
  have hmain := hlead.sub hrem
  rw [sub_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [pmBezoutInteriorGradient_add_two_mul_localImpulse_eq_activeDeleted_add_predecessorPeak ε hT]
  ring

/-- **Small-Damping Limit (`1 - pmAdjacentArtinConstant ≥ 7 / 12`) of the Conservation-Law Drift
(`tendsto_two_mul_pmInteriorLogCounterterm_div_parameter`):**
As `ε → 0⁺`, `(2 * pmInteriorLogCounterterm ε) / ε → 1 - pmAdjacentArtinConstant ≥ 7 / 12 > 0`. -/
theorem tendsto_two_mul_pmInteriorLogCounterterm_div_parameter :
    Tendsto (fun ε : ℝ => (2 * pmInteriorLogCounterterm ε) / ε) (𝓝[>] 0)
      (𝓝 (1 - pmAdjacentArtinConstant)) := by
  have h := tendsto_pmInteriorLogCounterterm_div_parameter.const_mul (2 : ℝ)
  have heq : 2 * ((1 - pmAdjacentArtinConstant) / 2) = 1 - pmAdjacentArtinConstant := by
    ring
  rw [heq] at h
  refine h.congr fun ε => ?_
  ring

/-! ## §3. Two-Sided Equivalence Between `pmPowerDampedDivisorDiscreteEnergy` and `pmBezoutInteriorPronicEnergy` -/

/-- The pure-interior pronic energy at horizon `T`:
`pmBezoutInteriorPronicEnergy ε T = ∑_{n=1}^T (pmBezoutInteriorPrefix ε n)² / pronicSeq n`. -/
def pmBezoutInteriorPronicEnergy (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 T,
    pmBezoutInteriorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)

/-- `pmBezoutInteriorPronicEnergy ε T` is non-negative for all `ε : ℝ` and `T : ℕ`. -/
theorem pmBezoutInteriorPronicEnergy_nonneg (ε : ℝ) (T : ℕ) :
    0 ≤ pmBezoutInteriorPronicEnergy ε T :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **Upper Bound on `pmPowerDampedDivisorDiscreteEnergy` by `2 * pmBezoutInteriorPronicEnergy + 1 / 2`
(`pmPowerDampedDivisorDiscreteEnergy_le_two_mul_interiorPronic_add_half`):**
For every `ε ≥ 0` and `T : ℕ`:
`pmPowerDampedDivisorDiscreteEnergy ε T ≤ 2 * pmBezoutInteriorPronicEnergy ε T + 1 / 2`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_le_two_mul_interiorPronic_add_half
    {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T ≤
      2 * pmBezoutInteriorPronicEnergy ε T + 1 / 2 := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
  have hle :
      (∑ n ∈ Finset.Icc 1 T,
        pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) ≤
      ∑ n ∈ Finset.Icc 1 T,
        (2 * (pmBezoutInteriorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
          2 * (addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) / (pronicSeq n : ℝ))) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have hsplit := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
    have hquad :
        pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) ≤
          2 * pmBezoutInteriorPrefix ε n ^ (2 : ℕ) +
            2 * addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) := by
      rw [hsplit]
      have hsq : 0 ≤ (pmBezoutInteriorPrefix ε n -
          addDiff (pmActiveSawtoothComponent ε) n) ^ (2 : ℕ) := sq_nonneg _
      nlinarith
    have hpr : (0 : ℝ) ≤ 1 / (pronicSeq n : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hquad hpr
    linarith [show pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ) =
        pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) * (1 / (pronicSeq n : ℝ)) by ring,
      show 2 * (pmBezoutInteriorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
          2 * (addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) / (pronicSeq n : ℝ)) =
        (2 * pmBezoutInteriorPrefix ε n ^ (2 : ℕ) +
          2 * addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ)) *
          (1 / (pronicSeq n : ℝ)) by ring]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hle
  change _ ≤ 2 * pmBezoutInteriorPronicEnergy ε T + 2 * pmActivePairPronicEnergy ε T at hle
  linarith [(pmActivePairPronicEnergy_bounds hε T).2]

/-- **Upper Bound on `pmBezoutInteriorPronicEnergy` by `2 * pmPowerDampedDivisorDiscreteEnergy + 1 / 2`
(`pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half`):**
For every `ε ≥ 0` and `T : ℕ`:
`pmBezoutInteriorPronicEnergy ε T ≤ 2 * pmPowerDampedDivisorDiscreteEnergy ε T + 1 / 2`. -/
theorem pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half
    {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    pmBezoutInteriorPronicEnergy ε T ≤
      2 * pmPowerDampedDivisorDiscreteEnergy ε T + 1 / 2 := by
  unfold pmBezoutInteriorPronicEnergy
  have hle :
      (∑ n ∈ Finset.Icc 1 T,
        pmBezoutInteriorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) ≤
      ∑ n ∈ Finset.Icc 1 T,
        (2 * (pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
          2 * (addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) / (pronicSeq n : ℝ))) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have hsplit := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
    have hI :
        pmBezoutInteriorPrefix ε n =
          pmPowerDampedCenteredDivisorPrefix ε n -
            addDiff (pmActiveSawtoothComponent ε) n := by
      linarith [hsplit]
    have hquad :
        pmBezoutInteriorPrefix ε n ^ (2 : ℕ) ≤
          2 * pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) +
            2 * addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) := by
      rw [hI]
      have hsq : 0 ≤ (pmPowerDampedCenteredDivisorPrefix ε n +
          addDiff (pmActiveSawtoothComponent ε) n) ^ (2 : ℕ) := sq_nonneg _
      nlinarith
    have hpr : (0 : ℝ) ≤ 1 / (pronicSeq n : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hquad hpr
    linarith [show pmBezoutInteriorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ) =
        pmBezoutInteriorPrefix ε n ^ (2 : ℕ) * (1 / (pronicSeq n : ℝ)) by ring,
      show 2 * (pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
          2 * (addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) / (pronicSeq n : ℝ)) =
        (2 * pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) +
          2 * addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ)) *
          (1 / (pronicSeq n : ℝ)) by ring]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq] at hle
  change _ ≤ 2 * pmPowerDampedDivisorDiscreteEnergy ε T + 2 * pmActivePairPronicEnergy ε T at hle
  linarith [(pmActivePairPronicEnergy_bounds hε T).2]

/-- The unconditional PM source bound at damping `ε ≥ 1/2` also bounds the
pure-interior energy, uniformly in the observation horizon. This transports
the existing endpoint theorem; it does not give a bound below `1/2`. -/
theorem exists_pmBezoutInteriorPronicEnergy_budget_of_half_le {ε : ℝ}
    (hε : (1 / 2 : ℝ) ≤ ε) :
    ∃ B : ℝ, ∀ T : ℕ, pmBezoutInteriorPronicEnergy ε T ≤ B := by
  obtain ⟨B, hB⟩ := RHTower.exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le hε
  refine ⟨2 * B + 1 / 2, fun T => ?_⟩
  exact (pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half
    (by linarith) T).trans (by linarith [hB T])

/-- **Pure-Interior Pronic Energy Criterion for the Riemann Hypothesis
(`riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded`):**
If for every `δ > 0` there exist `ε ∈ (0, δ)` and a uniform bound `B : ℝ` such that for all `T ≥ 1`,
`pmBezoutInteriorPronicEnergy ε T ≤ B`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, 1 ≤ T → pmBezoutInteriorPronicEnergy ε T ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget
  intro δ hδ
  obtain ⟨ε, hε, hεδ, B, hB⟩ := h δ hδ
  refine ⟨ε, hε, hεδ, max (2 * B + 1 / 2) 0, fun T => ?_⟩
  by_cases hT : 1 ≤ T
  · have h1 := pmPowerDampedDivisorDiscreteEnergy_le_two_mul_interiorPronic_add_half hε.le T
    have h2 := hB T hT
    exact (by linarith : pmPowerDampedDivisorDiscreteEnergy ε T ≤ 2 * B + 1 / 2).trans
      (le_max_left _ _)
  · have hT0 : T = 0 := by omega
    subst hT0
    unfold pmPowerDampedDivisorDiscreteEnergy
    simp

end
end GaloisForLFunctions.BezoutValuationIncidence
