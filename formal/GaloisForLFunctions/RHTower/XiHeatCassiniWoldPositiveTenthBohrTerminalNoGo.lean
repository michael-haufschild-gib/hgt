import GaloisForLFunctions.RHTower.XiHeatCassiniWoldPositiveTenthJointBohrCofinality
import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockProfile

/-!
# T2 Bohr-to-terminal reconstruction no-go

The T2 positive-ray joint current is unconditionally Cauchy in Bohr mean square.  This module
tests the next proposed inference: recover vanishing of the positive Borel terminal from that
Hilbert convergence and the unweighted vanishing of its primitive.

The inference is false on the literal ordered-prime clock.  The explicit residual

`r_N = exp (-h_N / 20)`

tends to zero, and its exact Abel increments at height `1/10` are square summable.  Finite
exponential currents built from those increments therefore satisfy the same Parseval and
Bohr-Cauchy laws as the genuine T2 current.  Nevertheless its terminal is

`r_N exp (h_N / 10) = exp (h_N / 20)`,

which tends to infinity.  Thus no topology-only or closed-graph argument from the proved T2 data
can reach the RH-equivalent terminal landing.  A surviving T2 proof must add a Wold-specific
terminal-controlling arithmetic norm or identity.
-/

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Explicit vanishing primitive used to test terminal reconstruction on the prime clock. -/
def t2BohrTerminalCounterResidual (N : ℕ) : ℝ :=
  Real.exp (-xiMassNthPrimeLogHeight N / 20)

/-- Exact height-`1/10` Abel increment of the counterexample primitive. -/
def t2BohrTerminalCounterCoefficient (N : ℕ) : ℂ :=
  ((t2BohrTerminalCounterResidual (N + 1) -
      t2BohrTerminalCounterResidual N : ℝ) : ℂ) *
    (Real.exp (xiMassNthPrimeLogHeight (N + 1) / 10) : ℂ)

/-- Finite prime-frequency current with the same geometry as the T2 Abel current. -/
def t2BohrTerminalCounterCurrent (N : ℕ) (x : ℝ) : ℂ :=
  expSum_exponentialSumMeanSquareLower (Finset.range N) t2BohrTerminalCounterCoefficient
    xiHeatCassiniWoldPositiveTenthJointFrequency x

/-- The counterexample primitive vanishes before positive-height reweighting. -/
theorem t2BohrTerminalCounterResidual_tendsto_zero :
    Tendsto t2BohrTerminalCounterResidual atTop (𝓝 0) := by
  have hscale : Tendsto (fun x : ℝ => -((1 / 20 : ℝ) * x)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 20))
  have h := Real.tendsto_exp_atBot.comp
    (hscale.comp tendsto_xiMassNthPrimeLogHeight_atTop)
  convert h using 1
  funext N
  simp only [Function.comp_apply, t2BohrTerminalCounterResidual]
  ring_nf

/-- Its height-`1/10` terminal escapes to infinity with exact exponent `1/20`. -/
theorem t2BohrTerminalCounterTerminal_tendsto_atTop :
    Tendsto (fun N : ℕ =>
      t2BohrTerminalCounterResidual N *
        Real.exp (xiMassNthPrimeLogHeight N / 10)) atTop atTop := by
  have hscale : Tendsto (fun x : ℝ => (1 / 20 : ℝ) * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 20)
  have h := Real.tendsto_exp_atTop.comp
    (hscale.comp tendsto_xiMassNthPrimeLogHeight_atTop)
  convert h using 1
  funext N
  simp only [Function.comp_apply]
  rw [t2BohrTerminalCounterResidual, ← Real.exp_add]
  congr 1
  ring

/-- Absolute-value form matching the literal positive Borel terminal. -/
theorem t2BohrTerminalCounterAbsTerminal_tendsto_atTop :
    Tendsto (fun N : ℕ =>
      |t2BohrTerminalCounterResidual N| *
        Real.exp (xiMassNthPrimeLogHeight N / 10)) atTop atTop := by
  simpa [t2BohrTerminalCounterResidual, abs_of_pos] using
    t2BohrTerminalCounterTerminal_tendsto_atTop

/-- One counterexample increment is dominated by the proved positive-height prime-gap energy. -/
lemma norm_t2BohrTerminalCounterCoefficient_sq_le (N : ℕ) :
    ‖t2BohrTerminalCounterCoefficient N‖ ^ (2 : ℕ) ≤
      (1 / 400 : ℝ) *
        (xiHeatCassiniOrderedPrimeLogGap N ^ (2 : ℕ) *
          Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5)) := by
  let h : ℝ := xiMassNthPrimeLogHeight N
  let h' : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let g : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hh : h' = h + g := by
    simp only [h, h', g, xiHeatCassiniOrderedPrimeLogGap]
    ring
  have hg0 : 0 ≤ g := by
    simpa [g] using xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hh0 : 0 ≤ h := (xiMassNthPrimeLogHeight_pos N).le
  have hfactor : Real.exp (-h' / 20) =
      Real.exp (-h / 20) * Real.exp (-g / 20) := by
    rw [← Real.exp_add]
    congr 1
    rw [hh]
    ring
  have hexp0 : 0 ≤ Real.exp (-g / 20) := (Real.exp_pos _).le
  have hexple : Real.exp (-g / 20) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hone : 1 - Real.exp (-g / 20) ≤ g / 20 := by
    have hexp := Real.add_one_le_exp (-g / 20)
    linarith
  have hbasele : Real.exp (-h / 20) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hdiff_nonneg :
      0 ≤ Real.exp (-h / 20) - Real.exp (-h' / 20) := by
    rw [hfactor]
    nlinarith [Real.exp_pos (-h / 20)]
  have hdiff :
      |Real.exp (-h' / 20) - Real.exp (-h / 20)| ≤ g / 20 := by
    rw [abs_sub_comm, abs_of_nonneg hdiff_nonneg, hfactor]
    calc
      Real.exp (-h / 20) -
          Real.exp (-h / 20) * Real.exp (-g / 20) =
        Real.exp (-h / 20) * (1 - Real.exp (-g / 20)) := by ring
      _ ≤ 1 * (g / 20) := by
        exact mul_le_mul hbasele hone (sub_nonneg.mpr hexple) zero_le_one
      _ = g / 20 := one_mul _
  have hdiffsq :
      |Real.exp (-h' / 20) - Real.exp (-h / 20)| ^ (2 : ℕ) ≤
        (g / 20) ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  change ‖((Real.exp (-h' / 20) - Real.exp (-h / 20) : ℝ) : ℂ) *
      (Real.exp (h' / 10) : ℂ)‖ ^ (2 : ℕ) ≤
    (1 / 400 : ℝ) * (g ^ (2 : ℕ) * Real.exp (h' / 5))
  rw [norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  have hexpsq : Real.exp (h' / 10) ^ (2 : ℕ) = Real.exp (h' / 5) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexpsq]
  have hE0 : 0 ≤ Real.exp (h' / 5) := (Real.exp_pos _).le
  calc
    |Real.exp (-h' / 20) - Real.exp (-h / 20)| ^ (2 : ℕ) *
        Real.exp (h' / 5) ≤
      (g / 20) ^ (2 : ℕ) * Real.exp (h' / 5) :=
        mul_le_mul_of_nonneg_right hdiffsq hE0
    _ = (1 / 400 : ℝ) * (g ^ (2 : ℕ) * Real.exp (h' / 5)) := by ring

/-- Exact positive-height Abel increments of the witness are square summable. -/
theorem summable_norm_sq_t2BohrTerminalCounterCoefficient :
    Summable (fun N : ℕ => ‖t2BohrTerminalCounterCoefficient N‖ ^ (2 : ℕ)) := by
  have hmajor :=
    summable_xiHeatCassiniOrderedPrimeLogGap_sq_mul_positiveFifthHeight.mul_left
      (1 / 400 : ℝ)
  exact hmajor.of_nonneg_of_le (fun N => sq_nonneg _)
    norm_t2BohrTerminalCounterCoefficient_sq_le

theorem t2BohrTerminalCounterCurrent_sub_eq_expSum
    {L M : ℕ} (hLM : L ≤ M) (x : ℝ) :
    t2BohrTerminalCounterCurrent M x - t2BohrTerminalCounterCurrent L x =
      expSum_exponentialSumMeanSquareLower (Finset.Ico L M) t2BohrTerminalCounterCoefficient
        xiHeatCassiniWoldPositiveTenthJointFrequency x := by
  unfold t2BohrTerminalCounterCurrent expSum_exponentialSumMeanSquareLower
  let f : ℕ → ℂ := fun j =>
    t2BohrTerminalCounterCoefficient j *
      Complex.exp (-Complex.I *
        (xiHeatCassiniWoldPositiveTenthJointFrequency j : ℂ) * (x : ℂ))
  have hsplit :
      (∑ j ∈ Finset.range L, f j) + (∑ j ∈ Finset.Ico L M, f j) =
        ∑ j ∈ Finset.range M, f j := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le L) hLM
  change (∑ j ∈ Finset.range M, f j) - (∑ j ∈ Finset.range L, f j) =
    ∑ j ∈ Finset.Ico L M, f j
  linear_combination -hsplit

/-- Exact finite Parseval law for every counterexample-current tail. -/
theorem tendsto_t2BohrTerminalCounterCurrent_tail_cesaro_normSq
    {L M : ℕ} (hLM : L ≤ M) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ x in (1 : ℝ)..T,
      ‖t2BohrTerminalCounterCurrent M x -
        t2BohrTerminalCounterCurrent L x‖ ^ (2 : ℕ))
      atTop
      (𝓝 (∑ j ∈ Finset.Ico L M,
        ‖t2BohrTerminalCounterCoefficient j‖ ^ (2 : ℕ))) := by
  have hparseval := tendsto_cesaro_normSq_expSum
    (Finset.Ico L M) t2BohrTerminalCounterCoefficient
      xiHeatCassiniWoldPositiveTenthJointFrequency
      xiHeatCassiniWoldPositiveTenthJointFrequency_injective.injOn
  simpa only [t2BohrTerminalCounterCurrent_sub_eq_expSum hLM] using hparseval

/-- Finite counterexample currents have exactly the same Bohr-Cauchy conclusion as the T2
positive-ray joint current. -/
theorem t2BohrTerminalCounterCurrent_bohrCauchy :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ L M : ℕ, N ≤ L → L ≤ M →
        (∑ j ∈ Finset.Ico L M,
          ‖t2BohrTerminalCounterCoefficient j‖ ^ (2 : ℕ)) < ε ∧
        Tendsto (fun T : ℝ => (1 / T) * ∫ x in (1 : ℝ)..T,
          ‖t2BohrTerminalCounterCurrent M x -
            t2BohrTerminalCounterCurrent L x‖ ^ (2 : ℕ))
          atTop
          (𝓝 (∑ j ∈ Finset.Ico L M,
            ‖t2BohrTerminalCounterCoefficient j‖ ^ (2 : ℕ))) := by
  intro ε hε
  let c : ℕ → ℝ := fun j => ‖t2BohrTerminalCounterCoefficient j‖ ^ (2 : ℕ)
  have hc : Summable c := summable_norm_sq_t2BohrTerminalCounterCoefficient
  let S : ℝ := ∑' j, c j
  have htend : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, c j)
      atTop (𝓝 S) := by
    simpa [S] using hc.hasSum.tendsto_sum_nat
  have hev : ∀ᶠ N in atTop, S - ε < ∑ j ∈ Finset.range N, c j := by
    apply htend.eventually
    exact eventually_gt_nhds (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, ?_⟩
  intro L M hNL hLM
  have hlow : S - ε < ∑ j ∈ Finset.range L, c j := hN L hNL
  have hupper : (∑ j ∈ Finset.range M, c j) ≤ S := by
    exact Summable.sum_le_tsum (Finset.range M) (fun j _ => sq_nonneg _) hc
  have hsplit :
      (∑ j ∈ Finset.range L, c j) + (∑ j ∈ Finset.Ico L M, c j) =
        ∑ j ∈ Finset.range M, c j := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le L) hLM
  constructor
  · dsimp only [c] at hsplit ⊢
    linarith
  · exact tendsto_t2BohrTerminalCounterCurrent_tail_cesaro_normSq hLM

/-- Topology-only terminal reconstruction principle tested by the T2 Bohr landing branch. -/
def T2PrimeClockBohrTerminalLandingPrinciple : Prop :=
  ∀ r : ℕ → ℝ,
    Tendsto r atTop (𝓝 0) →
    Summable (fun N : ℕ =>
      ‖(((r (N + 1) - r N : ℝ) : ℂ) *
        (Real.exp (xiMassNthPrimeLogHeight (N + 1) / 10) : ℂ))‖ ^ (2 : ℕ)) →
    Tendsto (fun N : ℕ =>
      |r N| * Real.exp (xiMassNthPrimeLogHeight N / 10)) atTop (𝓝 0)

/-- **T2 Bohr-to-terminal no-go.** Even on the literal ordered-prime clock, square-summable
positive-height Abel increments plus an unweighted vanishing primitive do not force the positive
Borel terminal to vanish. -/
theorem not_T2PrimeClockBohrTerminalLandingPrinciple :
    ¬ T2PrimeClockBohrTerminalLandingPrinciple := by
  intro hlanding
  have hzero := hlanding t2BohrTerminalCounterResidual
    t2BohrTerminalCounterResidual_tendsto_zero
    summable_norm_sq_t2BohrTerminalCounterCoefficient
  have hsmall : ∀ᶠ N : ℕ in atTop,
      |t2BohrTerminalCounterResidual N| *
        Real.exp (xiMassNthPrimeLogHeight N / 10) < 1 :=
    hzero (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge : ∀ᶠ N : ℕ in atTop,
      1 < |t2BohrTerminalCounterResidual N| *
        Real.exp (xiMassNthPrimeLogHeight N / 10) :=
    t2BohrTerminalCounterAbsTerminal_tendsto_atTop
      (eventually_gt_atTop 1)
  obtain ⟨N, hs, hl⟩ := (hsmall.and hlarge).exists
  linarith

end

end RHTower
