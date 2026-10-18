import GaloisForLFunctions.BezoutValuationIncidence.SummationByPartsActivePairAndUncenteredShiftedReduction
import GaloisForLFunctions.BezoutValuationIncidence.MultiLagBezoutLayerHierarchyAndFourStepInteriorCalculus

/-!
# Interior Martingale Quadratic-Gradient Reduction, Local Impulse Summation by Parts, and the Renormalized Drift Budget

In `BezoutPronicTotientInteriorMartingaleSynthesis` and `SummationByPartsActivePairAndUncenteredShiftedReduction`,
the Route PM discrete energy `pmPowerDampedDivisorDiscreteEnergy ε T` was decomposed into:
$$\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T =
  \operatorname{pmActiveDeletedCovarianceDiagonal}\,\varepsilon\,T +
  2\,\operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,T +
  2\,\operatorname{pmBezoutInteriorMartingaleSum}\,\varepsilon\,T.$$

In this module, we establish three unconditional theorems that eliminate the non-local prefix history
from `pmBezoutInteriorMartingaleSum ε T` and formalize the exact renormalized logarithmic drift budget:

1. **Exact Reduction of the Interior Martingale Product to Total Forward Differences + Local Impulse Products
   (`pmPowerDampedCenteredDivisorCoeff_succ_eq_addDiff_active_add_interior`,
   `two_mul_centered_mul_pmBezoutInteriorPrefix_eq_addDiff_sq_sub`,
   `mul_addDiff_eq_addDiff_mul_sub_succ_mul_addDiff`,
   `two_mul_centered_mul_pmBezoutInteriorPrefix_eq_local_impulse`):**
   - Taking the forward difference of `A_ε(n) = addDiff (S_ε) n + I_ε(n)` gives:
     $$\widetilde{\tau}_\varepsilon(n + 1) = \operatorname{addDiff}\bigl(\operatorname{addDiff}(S_\varepsilon)\bigr)\,n +
       \operatorname{addDiff}(I_\varepsilon)\,n.$$
   - Combining $2\,I_\varepsilon(n)\,\operatorname{addDiff}(I_\varepsilon)(n) = \operatorname{addDiff}(I_\varepsilon^2)(n) - (\operatorname{addDiff}(I_\varepsilon)(n))^2$
     with the discrete Leibniz identity $2\,I_\varepsilon(n)\,\operatorname{addDiff}^2(S_\varepsilon)(n) = 2\,\operatorname{addDiff}(I_\varepsilon \cdot \operatorname{addDiff}(S_\varepsilon))(n) - 2\,\operatorname{addDiff}(S_\varepsilon)(n+1)\,\operatorname{addDiff}(I_\varepsilon)(n)$
     absorbs **100% of the cumulative prefix $I_\varepsilon(n)$ into an exact forward difference**,
     leaving only the non-positive gradient dissipation $-(\operatorname{addDiff}(I_\varepsilon)(n))^2 \le 0$
     and the **purely local impulse product** $-2\,\operatorname{addDiff}(S_\varepsilon)(n+1)\,\operatorname{addDiff}(I_\varepsilon)(n)$
     (where $\operatorname{addDiff}(I_\varepsilon)(n) = \frac{1}{2}(\widetilde{\tau}_\varepsilon(n) + \widetilde{\tau}_\varepsilon(n+2)) - \frac{1}{2}\operatorname{addDiff}^2(\tau_{1+\varepsilon})(n)$).

2. **Compensated Summation-by-Parts Identity & Upper Bound for `2 * pmBezoutInteriorMartingaleSum`
   (`two_mul_pmBezoutInteriorMartingaleSum_eq_pronic_sub_grad_sub_local`,
   `pmBezoutInteriorPrefix_one_eq`):**
   Summing over $1 \le n \le T - 1$ against the compensated weight $w_T(n) = \frac{1}{n + 1} - \frac{1}{T + 1}$
   expresses $2\,\operatorname{pmBezoutInteriorMartingaleSum}\,\varepsilon\,T$ in terms of the pronic
   series of $I_\varepsilon(n)^2 + 2\,I_\varepsilon(n)\,\operatorname{addDiff}(S_\varepsilon)(n)$,
   the non-positive gradient dissipation $-\sum (\operatorname{addDiff} I_\varepsilon)^2 w_T \le 0$,
   and the local impulse cross-sum $-2\sum \operatorname{addDiff}(S_\varepsilon)(n+1)\,\operatorname{addDiff}(I_\varepsilon)(n)\,w_T(n)$.

3. **Exact Renormalized Complete Energy Budget & the `(1 - A) / 2 ≥ 7 / 24` Interior Drift Target
   (`pmCompensatedHarmonicSum`, `pmPowerDampedDivisorDiscreteEnergy_renormalized_budget_eq`,
   `pmInteriorDriftRate_algebraic_identity`, `pmInteriorDriftRate_lower_bound_of_artin_upper`,
   `riemannHypothesis_of_renormalized_pmBezoutInterior_budget`):**
   For any diagonal drift rate $v$ and active-pair drift rate $\kappa$, the complete energy decomposes
   identically into three renormalized brackets:
   $$\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T =
     \bigl[\operatorname{pmActiveDeletedCovarianceDiagonal}\,\varepsilon\,T - v\,H_T^{\text{comp}}\bigr] +
     2\,\bigl[\operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,T - \kappa\,H_T^{\text{comp}}\bigr] +
     2\,\bigl[\operatorname{pmBezoutInteriorMartingaleSum}\,\varepsilon\,T + \bigl(\tfrac{1}{2}v + \kappa\bigr)H_T^{\text{comp}}\bigr],$$
   where at the small-damping rates $v_0 = 1/2$ and $\kappa_0 = 1/4 - A/2$ ($A \le 5/12$ from primes $2, 3$),
   the required interior cancellation rate is $\frac{1}{2}v_0 + \kappa_0 = \frac{1 - A}{2} \ge \frac{7}{24} > 0$.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Pointwise Quadratic-Gradient & Local-Impulse Reduction of the Interior Martingale Product -/

/-- **Forward-Difference Decomposition of `pmPowerDampedCenteredDivisorCoeff ε (n + 1)`
(`pmPowerDampedCenteredDivisorCoeff_succ_eq_addDiff_active_add_interior`):**
For every `ε : ℝ` and `n : ℕ`:
`pmPowerDampedCenteredDivisorCoeff ε (n + 1) = addDiff (addDiff (pmActiveSawtoothComponent ε)) n + addDiff (pmBezoutInteriorPrefix ε) n`. -/
theorem pmPowerDampedCenteredDivisorCoeff_succ_eq_addDiff_active_add_interior
    (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) =
      addDiff (addDiff (pmActiveSawtoothComponent ε)) n +
        addDiff (pmBezoutInteriorPrefix ε) n := by
  have h0 := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
  have h1 := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε (n + 1)
  have hstep := pmPowerDampedCenteredDivisorPrefix_succ ε n
  unfold addDiff at h0 h1 ⊢
  linarith

/-- **Pointwise Quadratic-Gradient Identity for the Horizon-Free Interior Martingale Product
(`two_mul_centered_mul_pmBezoutInteriorPrefix_eq_addDiff_sq_sub`):**
For every `ε : ℝ` and `n : ℕ`:
`2 * widetilde_τ_ε(n + 1) * pmBezoutInteriorPrefix ε n = addDiff ((pmBezoutInteriorPrefix ε)²) n - (addDiff (pmBezoutInteriorPrefix ε) n)² + 2 * pmBezoutInteriorPrefix ε n * addDiff (addDiff (pmActiveSawtoothComponent ε)) n`. -/
theorem two_mul_centered_mul_pmBezoutInteriorPrefix_eq_addDiff_sq_sub
    (ε : ℝ) (n : ℕ) :
    2 * pmPowerDampedCenteredDivisorCoeff ε (n + 1) * pmBezoutInteriorPrefix ε n =
      addDiff (fun k => pmBezoutInteriorPrefix ε k ^ (2 : ℕ)) n -
        addDiff (pmBezoutInteriorPrefix ε) n ^ (2 : ℕ) +
        2 * pmBezoutInteriorPrefix ε n *
          addDiff (addDiff (pmActiveSawtoothComponent ε)) n := by
  rw [pmPowerDampedCenteredDivisorCoeff_succ_eq_addDiff_active_add_interior]
  unfold addDiff
  ring

/-- **Discrete Leibniz Identity for `X(n) * addDiff Y n`
(`mul_addDiff_eq_addDiff_mul_sub_succ_mul_addDiff`):**
For any two sequences `X, Y : ℕ → ℝ` and `n : ℕ`:
`X n * addDiff Y n = addDiff (fun k => X k * Y k) n - Y (n + 1) * addDiff X n`. -/
theorem mul_addDiff_eq_addDiff_mul_sub_succ_mul_addDiff (X Y : ℕ → ℝ) (n : ℕ) :
    X n * addDiff Y n =
      addDiff (fun k => X k * Y k) n - Y (n + 1) * addDiff X n := by
  unfold addDiff
  ring

/-- **Complete Elimination of the Cumulative Prefix `pmBezoutInteriorPrefix` in Favor of Local Impulses
(`two_mul_centered_mul_pmBezoutInteriorPrefix_eq_local_impulse`):**
For every `ε : ℝ` and `n : ℕ`, `2 * widetilde_τ_ε(n + 1) * pmBezoutInteriorPrefix ε n` decomposes into:
1. The exact forward difference of `(pmBezoutInteriorPrefix ε k)² + 2 * pmBezoutInteriorPrefix ε k * addDiff (pmActiveSawtoothComponent ε) k`,
2. The non-positive squared gradient `-(addDiff (pmBezoutInteriorPrefix ε) n)² ≤ 0`,
3. The purely local impulse product `-2 * addDiff (pmActiveSawtoothComponent ε) (n + 1) * addDiff (pmBezoutInteriorPrefix ε) n`. -/
theorem two_mul_centered_mul_pmBezoutInteriorPrefix_eq_local_impulse
    (ε : ℝ) (n : ℕ) :
    2 * pmPowerDampedCenteredDivisorCoeff ε (n + 1) * pmBezoutInteriorPrefix ε n =
      addDiff (fun k =>
        pmBezoutInteriorPrefix ε k ^ (2 : ℕ) +
          2 * pmBezoutInteriorPrefix ε k * addDiff (pmActiveSawtoothComponent ε) k) n -
        addDiff (pmBezoutInteriorPrefix ε) n ^ (2 : ℕ) -
        2 * addDiff (pmActiveSawtoothComponent ε) (n + 1) *
          addDiff (pmBezoutInteriorPrefix ε) n := by
  rw [two_mul_centered_mul_pmBezoutInteriorPrefix_eq_addDiff_sq_sub]
  unfold addDiff
  ring

/-- Moreover, the quantity `I_ε(k)² + 2 * I_ε(k) * addDiff (S_ε) k` inside the total forward difference
equals `A_ε(k)² - (addDiff (S_ε) k)²`. -/
theorem pmBezoutInteriorPrefix_sq_add_two_mul_eq_prefix_sq_sub_active_sq
    (ε : ℝ) (k : ℕ) :
    pmBezoutInteriorPrefix ε k ^ (2 : ℕ) +
      2 * pmBezoutInteriorPrefix ε k * addDiff (pmActiveSawtoothComponent ε) k =
      pmPowerDampedCenteredDivisorPrefix ε k ^ (2 : ℕ) -
        addDiff (pmActiveSawtoothComponent ε) k ^ (2 : ℕ) := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior]
  ring

/-! ## §2. Compensated Summation-by-Parts Identity for `2 * pmBezoutInteriorMartingaleSum` -/

/-- The combined interior-active potential at step `k`:
`pmInteriorActivePotential ε k = pmBezoutInteriorPrefix ε k ^ 2 + 2 * pmBezoutInteriorPrefix ε k * addDiff (pmActiveSawtoothComponent ε) k`. -/
def pmInteriorActivePotential (ε : ℝ) (k : ℕ) : ℝ :=
  pmBezoutInteriorPrefix ε k ^ (2 : ℕ) +
    2 * pmBezoutInteriorPrefix ε k * addDiff (pmActiveSawtoothComponent ε) k

/-- **Compensated Summation-by-Parts Identity for `2 * pmBezoutInteriorMartingaleSum`
(`two_mul_pmBezoutInteriorMartingaleSum_eq_pronic_sub_grad_sub_local`):**
For every `ε : ℝ` and `T ≥ 1`:
`2 * pmBezoutInteriorMartingaleSum ε T` equals:
1. The pronic series `∑_{n=1}^T pmInteriorActivePotential ε n / pronicSeq n - pmInteriorActivePotential ε 1 * (1 - 1 / (T + 1))`,
2. Minus the non-negative interior gradient energy `∑_{n=1}^{T-1} (addDiff (pmBezoutInteriorPrefix ε) n)² * (1 / (n + 1) - 1 / (T + 1))`,
3. Minus the local impulse cross-sum `2 * ∑_{n=1}^{T-1} addDiff (pmActiveSawtoothComponent ε) (n + 1) * addDiff (pmBezoutInteriorPrefix ε) n * (1 / (n + 1) - 1 / (T + 1))`. -/
theorem two_mul_pmBezoutInteriorMartingaleSum_eq_pronic_sub_grad_sub_local
    (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    2 * pmBezoutInteriorMartingaleSum ε T =
      (∑ n ∈ Finset.Icc 1 T, pmInteriorActivePotential ε n / (pronicSeq n : ℝ)) -
        pmInteriorActivePotential ε 1 * (1 - 1 / ((T : ℝ) + 1)) -
        (∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff (pmBezoutInteriorPrefix ε) n ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
        2 * ∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff (pmActiveSawtoothComponent ε) (n + 1) *
            addDiff (pmBezoutInteriorPrefix ε) n *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  unfold pmBezoutInteriorMartingaleSum
  have habel := sum_div_pronicSeq_eq_compensated_abel (pmInteriorActivePotential ε) hT
  have hrew :
      2 * (∑ n ∈ Finset.Icc 1 (T - 1),
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          pmBezoutInteriorPrefix ε n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      (∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff (pmInteriorActivePotential ε) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
        (∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff (pmBezoutInteriorPrefix ε) n ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
        2 * ∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff (pmActiveSawtoothComponent ε) (n + 1) *
            addDiff (pmBezoutInteriorPrefix ε) n *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hpt := two_mul_centered_mul_pmBezoutInteriorPrefix_eq_local_impulse ε n
    unfold pmInteriorActivePotential
    linarith [ congrArg (· * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) hpt ]
  linarith

/-! ## §3. Exact Renormalized Complete Energy Budget & the `(1 - A) / 2 ≥ 7 / 24` Interior Drift Target -/

/-- The compensated harmonic logarithmic weight sum at horizon `T`:
`pmCompensatedHarmonicSum T = ∑_{n=1}^{T-1} (1 / (n + 1) - 1 / (T + 1))`. -/
def pmCompensatedHarmonicSum (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (T - 1), (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))

/-- `pmCompensatedHarmonicSum T` is non-negative for every `T : ℕ`. -/
theorem pmCompensatedHarmonicSum_nonneg (T : ℕ) :
    0 ≤ pmCompensatedHarmonicSum T := by
  unfold pmCompensatedHarmonicSum
  refine Finset.sum_nonneg fun n hn => ?_
  obtain ⟨_, hnT⟩ := Finset.mem_Icc.mp hn
  have hle : (n : ℝ) + 1 ≤ (T : ℝ) + 1 := by exact_mod_cast (by omega : n + 1 ≤ T + 1)
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) hle)

/-- **Exact Finite-Horizon Renormalized Energy Budget Identity
(`pmPowerDampedDivisorDiscreteEnergy_renormalized_budget_eq`):**
For every `ε : ℝ`, `T : ℕ`, diagonal drift rate `v : ℝ`, and active-pair drift rate `κ : ℝ`,
the complete discrete energy decomposes identically into three renormalized brackets:
`pmPowerDampedDivisorDiscreteEnergy ε T = (pmActiveDeletedCovarianceDiagonal ε T - v * H_T) + 2 * (pmPredecessorPeakMartingaleSum ε T - κ * H_T) + 2 * (pmBezoutInteriorMartingaleSum ε T + (v / 2 + κ) * H_T)`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_renormalized_budget_eq
    (ε : ℝ) (T : ℕ) (v κ : ℝ) :
    pmPowerDampedDivisorDiscreteEnergy ε T =
      (pmActiveDeletedCovarianceDiagonal ε T - v * pmCompensatedHarmonicSum T) +
        2 * (pmPredecessorPeakMartingaleSum ε T - κ * pmCompensatedHarmonicSum T) +
        2 * (pmBezoutInteriorMartingaleSum ε T + (v / 2 + κ) * pmCompensatedHarmonicSum T) := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_activeDeleted_add_predecessorPeak_add_bezoutInterior]
  ring

/-- **Exact Small-Damping Interior Drift Rate Formula (`pmInteriorDriftRate_algebraic_identity`):**
When the normalized diagonal drift rate is `v₀ = 1 / 2` and the normalized active-pair drift rate is
`κ₀ = 1 / 4 - A / 2` (where `A` is Artin's constant `∏_p (1 - 1 / (p * (p - 1)))`), the required
normalized interior cancellation rate `v₀ / 2 + κ₀` equals `(1 - A) / 2`. -/
theorem pmInteriorDriftRate_algebraic_identity (A : ℝ) :
    (1 / 2 : ℝ) / 2 + (1 / 4 - A / 2) = (1 - A) / 2 := by
  ring

/-- **Two-Prime (`p = 2, 3`) Lower Bound on the Required Interior Cancellation Rate
(`pmInteriorDriftRate_lower_bound_of_artin_upper`):**
Because keeping only the prime factors `p = 2` (`1 - 1/2 = 1/2`) and `p = 3` (`1 - 1/6 = 5/6`)
bounds Artin's constant above by `A ≤ (1 / 2) * (5 / 6) = 5 / 12`, the required normalized interior
cancellation rate satisfies `(1 - A) / 2 ≥ 7 / 24 > 0`. -/
theorem pmInteriorDriftRate_lower_bound_of_artin_upper {A : ℝ}
    (hA : A ≤ (1 - 1 / (2 * (2 - 1 : ℝ))) * (1 - 1 / (3 * (3 - 1 : ℝ)))) :
    (7 / 24 : ℝ) ≤ (1 - A) / 2 := by
  linarith

/-- **Renormalized Bézout Interior Budget Criterion for the Riemann Hypothesis
(`riemannHypothesis_of_renormalized_pmBezoutInterior_budget`):**
If for every `δ > 0` there exist `ε ∈ (0, δ)`, drift rates `v, κ : ℝ`, and uniform bounds
`B_diag, B_pair, B_int : ℝ` such that for all `T ≥ 1`:
1. `pmActiveDeletedCovarianceDiagonal ε T - v * pmCompensatedHarmonicSum T ≤ B_diag`,
2. `pmPredecessorPeakMartingaleSum ε T - κ * pmCompensatedHarmonicSum T ≤ B_pair`,
3. `pmBezoutInteriorMartingaleSum ε T + (v / 2 + κ) * pmCompensatedHarmonicSum T ≤ B_int`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_renormalized_pmBezoutInterior_budget
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ v κ B_diag B_pair B_int : ℝ, ∀ T : ℕ, 1 ≤ T →
        pmActiveDeletedCovarianceDiagonal ε T - v * pmCompensatedHarmonicSum T ≤ B_diag ∧
        pmPredecessorPeakMartingaleSum ε T - κ * pmCompensatedHarmonicSum T ≤ B_pair ∧
        pmBezoutInteriorMartingaleSum ε T + (v / 2 + κ) * pmCompensatedHarmonicSum T ≤ B_int) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmBezoutInteriorMartingale_cancellation
  intro δ hδ
  obtain ⟨ε, hε, hεδ, v, κ, B_diag, B_pair, B_int, hB⟩ := h δ hδ
  refine ⟨ε, hε, hεδ, B_diag + 2 * B_pair + 2 * B_int, fun T hT => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hB T hT
  linarith

end
end GaloisForLFunctions.BezoutValuationIncidence
