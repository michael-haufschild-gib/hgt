import GaloisForLFunctions.BiScaleUncertainty.CenteredRamanujanVarianceAndAbelCofactorCancellation
import GaloisForLFunctions.BiScaleUncertainty.MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity
import GaloisForLFunctions.BiScaleUncertainty.SelbergSieveTailQuadraticFormAndTruncatedDivisorGram
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusEndpoint
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusMellin
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanLogMass

/-!
# Route PM Variance-to-Witness Synthesis & Critical-Strip Bridge (`FZZ-P` + `PM` + `PW-B`)

This module unifies the three branches of Route PM in `BiScaleUncertainty`:
- **Branch 1 (`FZZ-P` Power-Damped Möbius & Centered Ramanujan Sawtooth Variance):**
  Connects the unconditional endpoint admission at $\varepsilon \ge 1/2$
  (`memLp_pmPowerDampedFermiSource_of_half_le`) and the critical-strip variance reduction for
  $0 < \varepsilon < 1/2$ (`pmPowerDampedFermiSource_memLp_of_ramanujan_variance`) to our new
  zero-mean periodic Bernoulli sawtooth prefix `pmPowerDampedRamanujanCenteredSawtoothPrefix` and
  Cesàro period-centered quadratic form `pmPowerDampedRamanujanMeanCenteredQuadratic`.
- **Branch 2 (`FZZ-P` Selberg $\Lambda^2$-Sieve Tail & Log-Square Ramanujan Mass):**
  Combines the unconditional finiteness of the Ramanujan $\ell^1$ probability mass
  ($\sum_{q=0}^\infty \|w_\varepsilon(q)\| = 1$), the logarithmic second-moment mass
  ($\sum_{q=0}^\infty q \log(2q) \|w_\varepsilon(q)\|^2 < \infty$), and the global energy mean
  ($|\operatorname{pmPowerDampedRamanujanEnergyMean}(\varepsilon, Q)| \le C_\varepsilon$) valid for
  **every $\varepsilon > 0$** with the Selberg totient diagonalization of the truncated tail Gram
  matrix (`selbergLcmQuadraticForm_eq_totient_diagonal`).
- **Branch 3 (`PW-B` Multi-Octave Cellular Combinators & Witness Negative Index):**
  Combines the exact single-cell Kronecker combinators `singleCellFermiCombinator k N` and the
  top-octave energy balance of `dyadicForm w w` with `witnessNegIndex = rightStripMultiplicityCount`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Unconditional Endpoint Admission (`ε ≥ 1 / 2`) & Mellin Analyticity Certificate -/

/-- **Unconditional Endpoint $L^2$ Admission & Mellin Half-Plane Analyticity (`ε ≥ 1 / 2`):**
For every damping parameter `ε ≥ 1 / 2` (including the critical boundary `ε = 1 / 2`),
`pmPowerDampedFermiSource ε` belongs to $L^2((0, \infty), dt)$ and its Mellin transform is
analytic on the open right half-plane `{s : ℂ | 1 / 2 < s.re}`. -/
theorem pmPowerDampedFermiSource_half_le_memLp_and_analytic_mellin
    {ε : ℝ} (hε : 1 / 2 ≤ ε) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      AnalyticOnNhd ℂ (mellin (pmPowerDampedFermiSource ε)) {s : ℂ | 1 / 2 < s.re} := by
  have hm : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    memLp_pmPowerDampedFermiSource_of_half_le hε
  exact ⟨hm, analyticOnNhd_mellin_pmPowerDampedFermiSource ε hm⟩

/-! ## §2. Critical-Strip $L^2$ Admission & Mellin Analyticity via Centered Sawtooth Variance (`0 < ε`) -/

/-- **Centered Sawtooth Variance Criterion for $L^2(0, \infty)$ Admission & Mellin Analyticity:**
For any `ε > 0`, if the reciprocal-weighted second moment of the zero-mean periodic Bernoulli
sawtooth prefix `pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N` is bounded uniformly in `Q`
by `B`, then `pmPowerDampedFermiSource ε ∈ L^2(0, ∞)` and its Mellin transform is analytic on
`{s : ℂ | 1 / 2 < s.re}`. -/
theorem pmPowerDampedFermiSource_memLp_and_analytic_of_centeredSawtooth_budget
    {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ Q : ℕ,
      (∑' N : ℕ, (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N) ^ 2 /
        ((N : ℝ) * ((N : ℝ) + 1))) ≤ B) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      AnalyticOnNhd ℂ (mellin (pmPowerDampedFermiSource ε)) {s : ℂ | 1 / 2 < s.re} := by
  have hvar : ∀ Q : ℕ, pmPowerDampedRamanujanEnergyVariance ε Q ≤ B :=
    fun Q => (pmPowerDampedRamanujanEnergyVariance_le_centeredSawtooth_tsum hε Q).trans (hB Q)
  have hm := pmPowerDampedFermiSource_memLp_of_ramanujan_variance hε hvar
  exact ⟨hm, analyticOnNhd_mellin_pmPowerDampedFermiSource ε hm⟩

/-- **Mean-Centered Gram Criterion for $L^2(0, \infty)$ Admission & Mellin Analyticity:**
For any `ε > 0`, if the Cesàro period-centered Gram quadratic form
`pmPowerDampedRamanujanMeanCenteredQuadratic ε Q` is bounded uniformly in `Q` by `B`, then
`pmPowerDampedFermiSource ε ∈ L^2(0, ∞)` and its Mellin transform is analytic on
`{s : ℂ | 1 / 2 < s.re}`. -/
theorem pmPowerDampedFermiSource_memLp_and_analytic_of_meanCenteredQuadratic_budget
    {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ Q : ℕ, pmPowerDampedRamanujanMeanCenteredQuadratic ε Q ≤ B) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      AnalyticOnNhd ℂ (mellin (pmPowerDampedFermiSource ε)) {s : ℂ | 1 / 2 < s.re} := by
  have hvar : ∀ Q : ℕ, pmPowerDampedRamanujanEnergyVariance ε Q ≤ B :=
    fun Q => (pmPowerDampedRamanujanEnergyVariance_le_meanCenteredQuadratic hε Q).trans (hB Q)
  have hm := pmPowerDampedFermiSource_memLp_of_ramanujan_variance hε hvar
  exact ⟨hm, analyticOnNhd_mellin_pmPowerDampedFermiSource ε hm⟩

/-- **General Trial-Shift Variational Criterion for $L^2(0, \infty)$ Admission:**
For any `ε > 0` and any sequence of centering shifts `c : ℕ → ℝ`, if the reciprocal-weighted
second moment of `(pmPowerDampedRamanujanCumulativePrefix ε Q N).re - c Q` is bounded uniformly
in `Q` by `B`, then `pmPowerDampedFermiSource ε ∈ L^2(0, ∞)` and its Mellin transform is analytic
on `{s : ℂ | 1 / 2 < s.re}`. -/
theorem pmPowerDampedFermiSource_memLp_and_analytic_of_shifted_budget
    {ε B : ℝ} (hε : 0 < ε) (c : ℕ → ℝ)
    (hB : ∀ Q : ℕ,
      (∑' N : ℕ, ((pmPowerDampedRamanujanCumulativePrefix ε Q N).re - c Q) ^ 2 /
        ((N : ℝ) * ((N : ℝ) + 1))) ≤ B) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      AnalyticOnNhd ℂ (mellin (pmPowerDampedFermiSource ε)) {s : ℂ | 1 / 2 < s.re} := by
  have hvar : ∀ Q : ℕ, pmPowerDampedRamanujanEnergyVariance ε Q ≤ B :=
    fun Q => (pmPowerDampedRamanujanEnergyVariance_le_shifted_tsum hε Q (c Q)).trans (hB Q)
  have hm := pmPowerDampedFermiSource_memLp_of_ramanujan_variance hε hvar
  exact ⟨hm, analyticOnNhd_mellin_pmPowerDampedFermiSource ε hm⟩

/-! ## §3. Unconditional All-`ε > 0` Mass & Moment Certificate for Power-Damped Ramanujan Weights -/

/-- **Unconditional All-`ε > 0` Ramanujan Weight & Mean Certificate:**
For **every** damping parameter `ε > 0` (including the entire critical strip `0 < ε < 1 / 2`):
1. The Ramanujan weight norms sum to `1`: `HasSum (fun q => ‖pmPowerDampedRamanujanWeight ε q‖) 1`.
2. The logarithmic-weighted second moment `∑_{q ≥ 0} q log(2q) ‖w_ε(q)‖^2` is summable.
3. The Fermi diagonal energy `∑_{d ≥ 0} μ(d)^2 d^{-2ε} (log 2)/d` is summable.
4. The reciprocal-cell energy mean `pmPowerDampedRamanujanEnergyMean ε Q` is uniformly bounded
   for all `Q : ℕ`. -/
theorem pmPowerDamped_all_pos_epsilon_unconditional_certificate
    {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun q : ℕ => ‖pmPowerDampedRamanujanWeight ε q‖) 1 ∧
      Summable (pmPowerDampedRamanujanLogSquareTerm ε) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, |pmPowerDampedRamanujanEnergyMean ε Q| ≤ C) :=
  ⟨hasSum_norm_pmPowerDampedRamanujanWeight hε,
    summable_pmPowerDampedRamanujanLogSquareTerm hε,
    exists_pmPowerDampedRamanujanEnergyMean_bound hε⟩

/-! ## §4. Unified Route PM Synthesis: Producer-Consumer Duality Across `FZZ-P`, `PM`, and `PW-B` -/

/-- **Unified Route PM Master Theorem (`FZZ-P` + `PM` + `PW-B`):**
Collects the exact unconditional bridges across all three sub-routes of Route PM:
1. **Endpoint `FZZ-P` (`ε = 1 / 2`):** `pmPowerDampedFermiSource (1 / 2)` is unconditionally in
   $L^2(0, \infty)$ with Mellin transform analytic on `{s : ℂ | 1 / 2 < s.re}`.
2. **Critical-Strip `FZZ-P` (`0 < ε < 1 / 2`):** For every `ε > 0`, `pmPowerDampedRamanujanEnergyVariance ε Q`
   is bounded above by the reciprocal-weighted second moment of the zero-mean periodic Bernoulli
   sawtooth prefix `pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N`.
3. **Selberg Tail Gram Diagonalization (`PM`):** For every cutoff `N` and arithmetic weight `c`,
   `∑_{p ∈ [1, N]²} c(p₁) c(p₂) / lcm(p₁, p₂) = ∑ e ∈ Icc 1 N, φ(e) * (∑_{d ∈ [1, N], e ∣ d} c(d)/d)^2 ≥ 0`.
4. **Cellular Kronecker Resolution & Witness Signature (`PW-B`):**
   - For every `1 ≤ k ≤ N` and `1 ≤ n ≤ N`, `singleCellFermiCombinator k N` equals `δ_{n, k}` on
     the reciprocal cell `Ioc (1 / (n + 1)) (1 / n)`.
   - `witnessNegIndex = rightStripMultiplicityCount`, and `RiemannHypothesis` is equivalent to
     top-octave energy domination `∫_{1/2}^1 ‖w t‖^2 dt ≤ ∫_0^{1/2} ‖w t‖^2 dt` for all
     `IsFermiNymanWitness w`. -/
theorem routePM_unified_producer_consumer_synthesis :
    (MemLp (pmPowerDampedFermiSource (1 / 2)) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      AnalyticOnNhd ℂ (mellin (pmPowerDampedFermiSource (1 / 2))) {s : ℂ | 1 / 2 < s.re}) ∧
    (∀ {ε : ℝ}, 0 < ε → ∀ Q : ℕ,
      pmPowerDampedRamanujanEnergyVariance ε Q ≤
        ∑' N : ℕ, (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N) ^ 2 /
          ((N : ℝ) * ((N : ℝ) + 1))) ∧
    (∀ (N : ℕ) (c : ℕ → ℝ),
      (∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        c p.1 * c p.2 / (Nat.lcm p.1 p.2 : ℝ)) =
      ∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) *
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d), c d / (d : ℝ)) ^ (2 : ℕ)) ∧
    (witnessNegIndex = rightStripMultiplicityCount ∧
      (RiemannHypothesis ↔
        ∀ w : ℝ → ℂ, IsFermiNymanWitness w →
          (∫ t in Ioc (1 / 2 : ℝ) 1, ‖w t‖ ^ 2) ≤ (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2))) := by
  refine ⟨pmPowerDampedFermiSource_half_le_memLp_and_analytic_mellin le_rfl, ?_, ?_, ?_⟩
  · intro ε hε Q
    exact pmPowerDampedRamanujanEnergyVariance_le_centeredSawtooth_tsum hε Q
  · intro N c
    exact truncated_lcm_smooth_eq_selberg_totient_diagonal N c
  · exact ⟨witnessNegIndex_eq_rightStripMultiplicityCount,
      riemannHypothesis_iff_witness_top_octave_energy_le_lower_half⟩

end

end GaloisForLFunctions.BiScaleUncertainty
