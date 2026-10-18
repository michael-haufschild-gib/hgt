import GaloisForLFunctions.BezoutValuationIncidence.BezoutPronicInteriorSawtoothAndPredecessorPeakSplit
import GaloisForLFunctions.BezoutValuationIncidence.ModularGcdLcmMultiplicativityAndCenteredSuccessorCovariance

/-!
# Pillar XXIV: Bézout Pronic–Totient–Interior Martingale Synthesis & Two-Step Midpoint Duality

In Pillar XVI (`ModularGcdLcmMultiplicativityAndCenteredSuccessorCovariance`), we proved the
Bézout successor pronic covariance identity
$$\widetilde{\tau}_\varepsilon(n)\,\widetilde{\tau}_\varepsilon(n + 1) =
  \tau_\varepsilon(\operatorname{pronicSeq}\,n) -
  \alpha_\varepsilon\bigl(\tau_\varepsilon(n) + \tau_\varepsilon(n + 1)\bigr) + \alpha_\varepsilon^2.$$
And in Pillars XXI–XXIII, we decomposed the Route PM prefix $A_\varepsilon(n)$ across step
$n \mapsto n + 1$ into the Bézout active pair
$$\operatorname{addDiff}\,(\operatorname{pmActiveSawtoothComponent}\,\varepsilon)\,n =
  \operatorname{pmActiveSawtoothComponent}\,\varepsilon\,(n + 1) -
  \operatorname{pmActiveSawtoothComponent}\,\varepsilon\,n$$
plus the doubly-inactive Bézout interior prefix `pmBezoutInteriorPrefix ε n`.

In this twenty-fourth pillar of **Bézout–Valuation Incidence Mechanics**, we unify Pillar XVI with
Pillars XVII–XXIII by proving the **Exact Bézout Pronic–Totient–Interior Martingale Identity**:
absorbing both the pre-jump trough at $n + 1$ and the post-jump peak at $n$ into the diagonal
square $\widetilde{\tau}_\varepsilon(n + 1)^2$ **completely eliminates the diagonal square** and
replaces it by the **Bézout successor pronic covariance** $\widetilde{\tau}_\varepsilon(n)\,\widetilde{\tau}_\varepsilon(n + 1)$
plus the **shifted-exponent totient forward difference**
$\widetilde{\tau}_\varepsilon(n + 1)\,\operatorname{addDiff}\,(\tau_{1+\varepsilon})\,n$:
$$A_\varepsilon(n + 1)^2 - A_\varepsilon(n)^2 =
  \widetilde{\tau}_\varepsilon(n)\,\widetilde{\tau}_\varepsilon(n + 1) +
  \widetilde{\tau}_\varepsilon(n + 1)\,\operatorname{addDiff}\,(\operatorname{pmPowerDampedDivisorCoeff}\,(1 + \varepsilon))\,n +
  2\,\widetilde{\tau}_\varepsilon(n + 1)\,\operatorname{pmBezoutInteriorPrefix}\,\varepsilon\,n.$$

## Core Main Theorems (100% Unconditional)

1. **Exact Bézout Pronic–Totient–Interior Square-Increment Identity & Two-Step Midpoint Duality
   (`pmActiveDeleted_add_predecessorPeak_eq_pronic_add_shiftedAddDiff`,
   `pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq_eq_pronic_add_shiftedAddDiff_add_interior`,
   `pmBezoutInteriorPrefix_add_half_shiftedAddDiff_eq_two_step_midpoint`)**:
   For every $\varepsilon : \mathbb{R}$ and $n : \mathbb{N}$:
   - Pointwise across $n \mapsto n + 1$:
     $$A_\varepsilon(n + 1)^2 - A_\varepsilon(n)^2 =
       \widetilde{\tau}_\varepsilon(n)\,\widetilde{\tau}_\varepsilon(n + 1) +
       \widetilde{\tau}_\varepsilon(n + 1)\,\operatorname{addDiff}\,(\tau_{1+\varepsilon})\,n +
       2\,\widetilde{\tau}_\varepsilon(n + 1)\,\operatorname{pmBezoutInteriorPrefix}\,\varepsilon\,n.$$
   - For every $n \ge 1$, the symmetric two-step prefix midpoint $\frac{1}{2}\bigl(A_\varepsilon(n - 1) + A_\varepsilon(n + 1)\bigr)$
     equals `pmBezoutInteriorPrefix ε n` plus $\frac{1}{2}\,\operatorname{addDiff}\,(\tau_{1+\varepsilon})\,n$.

2. **Exact Sub-Horizon Affine Equivalence Between `pmBezoutInteriorPrefix` and `bezoutInteriorSawtoothSum`
   (`addDiff_pmActiveSawtoothComponent_eq_bezout_active_pair`,
   `pmBezoutInteriorPrefix_sub_bezoutInteriorSawtoothSum_eq_affine`)**:
   For every $\varepsilon : \mathbb{R}$ and $1 \le n$ with $n + 1 \le N$:
   $$\operatorname{pmBezoutInteriorPrefix}\,\varepsilon\,n -
     \operatorname{bezoutInteriorSawtoothSum}\,N\,c_\varepsilon\,n =
     -W_{N, c_\varepsilon}(0) + n\,\bigl(Y_{N, c_\varepsilon}(1) - (\operatorname{pmPowerDampedDivisorDensity}\,\varepsilon).\text{re}\bigr).$$

3. **Global Bézout Pronic–Totient–Interior Decomposition of `pmPowerDampedDivisorDiscreteEnergy` & RH Criterion
   (`pmInactivePredictableMartingaleSum_eq_predecessorPeak_add_bezoutInterior`,
   `pmPowerDampedDivisorDiscreteEnergy_eq_activeDeleted_add_predecessorPeak_add_bezoutInterior`,
   `riemannHypothesis_of_pmBezoutInteriorMartingale_cancellation`)**:
   For every $\varepsilon : \mathbb{R}$ and $T : \mathbb{N}$:
   $$\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T =
     \operatorname{pmActiveDeletedCovarianceDiagonal}\,\varepsilon\,T +
     2\,\operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,T +
     2\,\operatorname{pmBezoutInteriorMartingaleSum}\,\varepsilon\,T.$$
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Bézout Pronic–Totient–Interior Square-Increment Identity & Two-Step Midpoint Duality -/

/-- **Unification of Active-Deleted Diagonal + Predecessor Peak with Pronic Covariance + Shifted Forward Difference
(`pmActiveDeleted_add_predecessorPeak_eq_pronic_add_shiftedAddDiff`):**
For every `ε : ℝ` and `n : ℕ`, combining `pmActiveDeletedDiagonalCoeff ε (n + 1)` with twice the
predecessor-peak martingale product `2 * pmPowerDampedCenteredDivisorCoeff ε (n + 1) * (-pmActiveSawtoothComponent ε n)`
yields the Bézout successor pronic covariance
`pmPowerDampedCenteredDivisorCoeff ε n * pmPowerDampedCenteredDivisorCoeff ε (n + 1)` plus
`pmPowerDampedCenteredDivisorCoeff ε (n + 1) * addDiff (pmPowerDampedDivisorCoeff (1 + ε)) n`. -/
theorem pmActiveDeleted_add_predecessorPeak_eq_pronic_add_shiftedAddDiff (ε : ℝ) (n : ℕ) :
    pmActiveDeletedDiagonalCoeff ε (n + 1) +
      2 * pmPowerDampedCenteredDivisorCoeff ε (n + 1) * (-pmActiveSawtoothComponent ε n) =
      pmPowerDampedCenteredDivisorCoeff ε n * pmPowerDampedCenteredDivisorCoeff ε (n + 1) +
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          addDiff (pmPowerDampedDivisorCoeff (1 + ε)) n := by
  unfold pmActiveDeletedDiagonalCoeff pmActiveSawtoothComponent
    pmPowerDampedCenteredDivisorCoeff addDiff
  ring

/-- **Exact Bézout Pronic–Totient–Interior Square-Increment Identity for Route PM
(`pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq_eq_pronic_add_shiftedAddDiff_add_interior`):**
For every `ε : ℝ` and `n : ℕ`, the Route PM square increment `A_ε(n + 1)² - A_ε(n)²` decomposes
with **zero diagonal square** into:
1. The Bézout successor pronic covariance `widetilde_τ_ε(n) * widetilde_τ_ε(n + 1)`,
2. The shifted-exponent totient forward difference `widetilde_τ_ε(n + 1) * addDiff (τ_{1+ε}) n`,
3. Twice the doubly-inactive Bézout interior martingale product
   `2 * widetilde_τ_ε(n + 1) * pmBezoutInteriorPrefix ε n`. -/
theorem pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq_eq_pronic_add_shiftedAddDiff_add_interior
    (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ (2 : ℕ) -
      pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) =
      pmPowerDampedCenteredDivisorCoeff ε n * pmPowerDampedCenteredDivisorCoeff ε (n + 1) +
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          addDiff (pmPowerDampedDivisorCoeff (1 + ε)) n +
        2 * pmPowerDampedCenteredDivisorCoeff ε (n + 1) * pmBezoutInteriorPrefix ε n := by
  rw [pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq_active_deleted,
    pmInactiveResidualPrefix_eq_neg_active_add_bezoutInterior,
    ← pmActiveDeleted_add_predecessorPeak_eq_pronic_add_shiftedAddDiff]
  ring

/-- **Two-Step Midpoint Duality for `pmBezoutInteriorPrefix`
(`pmBezoutInteriorPrefix_add_half_shiftedAddDiff_eq_two_step_midpoint`):**
For every `ε : ℝ` and every `n ≥ 1`, adding `(1 / 2) * addDiff (pmPowerDampedDivisorCoeff (1 + ε)) n`
to the doubly-inactive Bézout interior prefix `pmBezoutInteriorPrefix ε n` yields the exact
two-step symmetric prefix midpoint `(1 / 2) * (pmPowerDampedCenteredDivisorPrefix ε (n - 1) + pmPowerDampedCenteredDivisorPrefix ε (n + 1))`. -/
theorem pmBezoutInteriorPrefix_add_half_shiftedAddDiff_eq_two_step_midpoint
    (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    pmBezoutInteriorPrefix ε n +
      (1 / 2 : ℝ) * addDiff (pmPowerDampedDivisorCoeff (1 + ε)) n =
      (1 / 2 : ℝ) *
        (pmPowerDampedCenteredDivisorPrefix ε (n - 1) +
          pmPowerDampedCenteredDivisorPrefix ε (n + 1)) := by
  have hpred : pmPowerDampedCenteredDivisorPrefix ε n =
      pmPowerDampedCenteredDivisorPrefix ε (n - 1) +
        pmPowerDampedCenteredDivisorCoeff ε n := by
    have h := pmPowerDampedCenteredDivisorPrefix_succ ε (n - 1)
    rwa [Nat.sub_add_cancel hn] at h
  have hsucc := pmPowerDampedCenteredDivisorPrefix_succ ε n
  have hbij := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
  unfold addDiff pmActiveSawtoothComponent at hbij
  unfold pmPowerDampedCenteredDivisorCoeff at hpred hsucc
  unfold addDiff
  linarith

/-! ## §2. Exact Sub-Horizon Affine Equivalence Between `pmBezoutInteriorPrefix` and `bezoutInteriorSawtoothSum` -/

/-- **Sub-Horizon Identification of the Bézout Active Pair with `addDiff (pmActiveSawtoothComponent ε)`
(`addDiff_pmActiveSawtoothComponent_eq_bezout_active_pair`):**
For every `ε : ℝ` and `1 ≤ n` with `n + 1 ≤ N`:
`addDiff (pmActiveSawtoothComponent ε) n = activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) n n + activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n`. -/
theorem addDiff_pmActiveSawtoothComponent_eq_bezout_active_pair
    (ε : ℝ) {N n : ℕ} (hn1 : 1 ≤ n) (hnN : n + 1 ≤ N) :
    addDiff (pmActiveSawtoothComponent ε) n =
      activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) n n +
        activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n := by
  have hpred := activeCenteredSawtoothSum_eq_pmActiveSawtoothComponent ε hnN
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have hself := activeCenteredSawtoothSum_pmPowerDampedRealWeight_self_eq ε
    (by omega : k + 1 ≤ N)
  unfold addDiff
  unfold pmActiveSawtoothComponent at hpred ⊢
  linarith

/-- **Exact Sub-Horizon Affine Equivalence Between `pmBezoutInteriorPrefix` and `bezoutInteriorSawtoothSum`
(`pmBezoutInteriorPrefix_sub_bezoutInteriorSawtoothSum_eq_affine`):**
For every `ε : ℝ` and every `1 ≤ n` with `n + 1 ≤ N`, the difference between the horizon-free
`pmBezoutInteriorPrefix ε n` and `bezoutInteriorSawtoothSum N (pmPowerDampedRealWeight ε) n` is
the exact same zero-oscillation affine linear function of `n` as for the full prefix:
`pmBezoutInteriorPrefix ε n - bezoutInteriorSawtoothSum N (pmPowerDampedRealWeight ε) n = -weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε) 0 + n * (selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1 - (pmPowerDampedDivisorDensity ε).re)`. -/
theorem pmBezoutInteriorPrefix_sub_bezoutInteriorSawtoothSum_eq_affine
    (ε : ℝ) {N n : ℕ} (hn1 : 1 ≤ n) (hnN : n + 1 ≤ N) :
    pmBezoutInteriorPrefix ε n -
      bezoutInteriorSawtoothSum N (pmPowerDampedRealWeight ε) n =
      -weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε) 0 +
        (n : ℝ) * (selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1 -
          (pmPowerDampedDivisorDensity ε).re) := by
  have hfull := pmPowerDampedCenteredDivisorPrefix_sub_weightedCenteredSawtoothSum_eq_affine ε
    (by omega : n ≤ N)
  have hA := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
  have hW := weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior
    N (pmPowerDampedRealWeight ε) n
  have hpair := addDiff_pmActiveSawtoothComponent_eq_bezout_active_pair ε hn1 hnN
  linarith

/-! ## §3. Global Bézout Pronic–Totient–Interior Decomposition of `pmPowerDampedDivisorDiscreteEnergy` -/

/-- The **predecessor-peak predictable martingale sum** at horizon `T`:
`pmPredecessorPeakMartingaleSum ε T = ∑_{n=1}^{T-1} widetilde_τ_ε(n + 1) * (-pmActiveSawtoothComponent ε n) * (1 / (n + 1) - 1 / (T + 1))`. -/
def pmPredecessorPeakMartingaleSum (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (T - 1),
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
      (-pmActiveSawtoothComponent ε n) *
      (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))

/-- The **doubly-inactive Bézout interior predictable martingale sum** at horizon `T`:
`pmBezoutInteriorMartingaleSum ε T = ∑_{n=1}^{T-1} widetilde_τ_ε(n + 1) * pmBezoutInteriorPrefix ε n * (1 / (n + 1) - 1 / (T + 1))`. -/
def pmBezoutInteriorMartingaleSum (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (T - 1),
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
      pmBezoutInteriorPrefix ε n *
      (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))

/-- **Predecessor-Peak + Bézout Interior Split of `pmInactivePredictableMartingaleSum`
(`pmInactivePredictableMartingaleSum_eq_predecessorPeak_add_bezoutInterior`):**
For every `ε : ℝ` and `T : ℕ`:
`pmInactivePredictableMartingaleSum ε T = pmPredecessorPeakMartingaleSum ε T + pmBezoutInteriorMartingaleSum ε T`. -/
theorem pmInactivePredictableMartingaleSum_eq_predecessorPeak_add_bezoutInterior
    (ε : ℝ) (T : ℕ) :
    pmInactivePredictableMartingaleSum ε T =
      pmPredecessorPeakMartingaleSum ε T + pmBezoutInteriorMartingaleSum ε T := by
  unfold pmInactivePredictableMartingaleSum pmPredecessorPeakMartingaleSum
    pmBezoutInteriorMartingaleSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [pmInactiveResidualPrefix_eq_neg_active_add_bezoutInterior ε n]
  ring

/-- **Global Bézout Pronic–Totient–Interior Decomposition of `pmPowerDampedDivisorDiscreteEnergy`
(`pmPowerDampedDivisorDiscreteEnergy_eq_activeDeleted_add_predecessorPeak_add_bezoutInterior`):**
For every `ε : ℝ` and `T : ℕ`:
`pmPowerDampedDivisorDiscreteEnergy ε T = pmActiveDeletedCovarianceDiagonal ε T + 2 * pmPredecessorPeakMartingaleSum ε T + 2 * pmBezoutInteriorMartingaleSum ε T`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_eq_activeDeleted_add_predecessorPeak_add_bezoutInterior
    (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T =
      pmActiveDeletedCovarianceDiagonal ε T +
        2 * pmPredecessorPeakMartingaleSum ε T +
        2 * pmBezoutInteriorMartingaleSum ε T := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_activeDeletedDiagonal_add_two_mul_inactive,
    pmInactivePredictableMartingaleSum_eq_predecessorPeak_add_bezoutInterior]
  ring

/-- **Route PM Bézout Interior Martingale Cancellation Criterion for the Riemann Hypothesis
(`riemannHypothesis_of_pmBezoutInteriorMartingale_cancellation`):**
If for every `δ > 0` there exist `ε ∈ (0, δ)` and a uniform bound `B : ℝ` such that for all `T ≥ 1`,
`pmActiveDeletedCovarianceDiagonal ε T + 2 * pmPredecessorPeakMartingaleSum ε T + 2 * pmBezoutInteriorMartingaleSum ε T ≤ B`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_pmBezoutInteriorMartingale_cancellation
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, 1 ≤ T →
        pmActiveDeletedCovarianceDiagonal ε T +
          2 * pmPredecessorPeakMartingaleSum ε T +
          2 * pmBezoutInteriorMartingaleSum ε T ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmInactivePredictableMartingale_cancellation
  intro δ hδ
  obtain ⟨ε, hε, hεδ, B, hB⟩ := h δ hδ
  refine ⟨ε, hε, hεδ, B, fun T hT => ?_⟩
  rw [pmInactivePredictableMartingaleSum_eq_predecessorPeak_add_bezoutInterior]
  linarith [hB T hT]

end
end GaloisForLFunctions.BezoutValuationIncidence
