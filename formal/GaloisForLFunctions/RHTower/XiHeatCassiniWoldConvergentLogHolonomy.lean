import GaloisForLFunctions.RHTower.XiHeatCassiniWoldCenteredLogConnection
import GaloisForLFunctions.RHTower.Sieve.MertensFirstExpRate

/-!
# Convergent logarithmic holonomy of the pure Wold Route-T producer

The bounded arithmetic primitive in the centered Wold connection is in fact convergent.  The
exponential-rate Mertens theorem supplies the limiting prime-log constant, while summability of the
Euler trace correction supplies the second limiting constant.  Their difference is the Wold
holonomy.  Splitting the primitive about this limit makes the constant component telescope exactly
to the first ordered-prime profile; the remaining connection has a primitive tending to zero.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The prime-window Mertens mass is the sieve Mertens mass. -/
theorem mertensPrimeWeightSum_eq_sieve_mertensA (N : ℕ) :
    mertensPrimeWeightSum N = Sieve.mertensA N := by
  rw [mertensPrimeWeightSum, Sieve.Icc_zero_eq_range,
    ← Sieve.sum_range_primeLogWeight]
  apply Finset.sum_congr rfl
  intro n hn
  rfl

/-- The Mertens prime-log discrepancy converges along natural cutoffs. -/
theorem exists_tendsto_sieve_mertensA_sub_log :
    ∃ c₁ : ℝ,
      Tendsto (fun N : ℕ => Sieve.mertensA N - Real.log N) atTop (𝓝 c₁) := by
  obtain ⟨c₁, B, c, hc, hB, hrate⟩ :=
    Sieve.exists_mertensA_sub_log_exp_rate
  have hrateNat : ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensA N - Real.log N - c₁| ≤
        B * Real.exp (-c * Real.sqrt (Real.log N)) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hrate
    filter_upwards [h] with N hN
    rwa [Nat.floor_natCast] at hN
  have hsqrtLog :
      Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hscaled :
      Tendsto (fun N : ℕ => c * Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    hsqrtLog.const_mul_atTop hc
  have hnegative :
      Tendsto (fun N : ℕ => -(c * Real.sqrt (Real.log (N : ℝ)))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hscaled
  have hexp :
      Tendsto (fun N : ℕ => Real.exp (-(c * Real.sqrt (Real.log (N : ℝ)))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  have hmajor :
      Tendsto (fun N : ℕ => B * Real.exp (-c * Real.sqrt (Real.log N)))
        atTop (𝓝 0) := by
    have h := hexp.const_mul B
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards with N
    congr 2
    ring
  have hnorm :
      Tendsto (fun N : ℕ => ‖Sieve.mertensA N - Real.log N - c₁‖)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun N => norm_nonneg _
    · simpa only [Real.norm_eq_abs] using hrateNat
    · exact hmajor
  have hzero :
      Tendsto (fun N : ℕ => Sieve.mertensA N - Real.log N - c₁)
        atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  refine ⟨c₁, ?_⟩
  have hconst : Tendsto (fun _ : ℕ => c₁) atTop (𝓝 c₁) :=
    tendsto_const_nhds
  have hsum : Tendsto (fun N : ℕ =>
      c₁ + (Sieve.mertensA N - Real.log N - c₁)) atTop (𝓝 (c₁ + 0)) :=
    hconst.add hzero
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards with N
  ring

/-- Canonical prime-log asymptotic constant selected from the proved convergence theorem. -/
def xiHeatCassiniMertensLogConstant : ℝ :=
  Classical.choose exists_tendsto_sieve_mertensA_sub_log

/-- The selected Mertens constant has its defining convergence law. -/
theorem tendsto_sieve_mertensA_sub_log :
    Tendsto (fun N : ℕ => Sieve.mertensA N - Real.log N) atTop
      (𝓝 xiHeatCassiniMertensLogConstant) :=
  Classical.choose_spec exists_tendsto_sieve_mertensA_sub_log

/-- Finite Euler-correction prefixes converge to their complete trace mass. -/
theorem tendsto_xiHeatCassiniWoldNatTraceCorrectionSum :
    Tendsto xiHeatCassiniWoldNatTraceCorrectionSum atTop
      (𝓝 xiHeatCassiniWoldNatTraceCorrectionMass) := by
  have hsum :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        xiHeatCassiniWoldNatTraceCorrection n) atTop
        (𝓝 xiHeatCassiniWoldNatTraceCorrectionMass) :=
    (Summable.hasSum_iff_tendsto_nat
      summable_xiHeatCassiniWoldNatTraceCorrection
      (m := xiHeatCassiniWoldNatTraceCorrectionMass)).mp
        summable_xiHeatCassiniWoldNatTraceCorrection.hasSum
  have hsucc := hsum.comp (Filter.tendsto_add_atTop_nat 1)
  apply hsucc.congr'
  filter_upwards with N
  simp only [Function.comp_apply, xiHeatCassiniWoldNatTraceCorrectionSum,
    Sieve.Icc_zero_eq_range]

/-- Persistent arithmetic holonomy after removing the finite Euler trace correction. -/
def xiHeatCassiniWoldLogHolonomyConstant : ℝ :=
  xiHeatCassiniMertensLogConstant -
    xiHeatCassiniWoldNatTraceCorrectionMass

/-- Natural-cutoff Wold discrepancy converges to the Wold logarithmic holonomy. -/
theorem tendsto_xiHeatCassiniWoldNatWeightSum_sub_log :
    Tendsto (fun N : ℕ =>
      xiHeatCassiniWoldNatWeightSum N - Real.log N) atTop
        (𝓝 xiHeatCassiniWoldLogHolonomyConstant) := by
  have hsub := tendsto_sieve_mertensA_sub_log.sub
    tendsto_xiHeatCassiniWoldNatTraceCorrectionSum
  apply hsub.congr'
  filter_upwards with N
  rw [← mertensPrimeWeightSum_eq_sieve_mertensA,
    mertensPrimeWeightSum_eq_wold_add_traceCorrection]
  ring

/-- Ordered-prime Wold discrepancy has the same holonomy limit. -/
theorem tendsto_xiHeatCassiniOrderedWoldLogDiscrepancy :
    Tendsto xiHeatCassiniOrderedWoldLogDiscrepancy atTop
      (𝓝 xiHeatCassiniWoldLogHolonomyConstant) := by
  have h := tendsto_xiHeatCassiniWoldNatWeightSum_sub_log.comp
    nthPrimeSubtype_strictMono.tendsto_atTop
  apply h.congr'
  filter_upwards with N
  simp only [Function.comp_apply, xiHeatCassiniOrderedWoldLogDiscrepancy,
    xiHeatCassiniOrderedWoldPartialMass_eq_natWeightSum,
    xiMassNthPrimeLogHeight]

/-- Centered residual primitive after removing the limiting logarithmic holonomy. -/
def xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N : ℕ) : ℝ :=
  xiHeatCassiniOrderedWoldLogDiscrepancy N -
    xiHeatCassiniWoldLogHolonomyConstant

/-- The residual arithmetic primitive vanishes on the ordered prime mesh. -/
theorem tendsto_xiHeatCassiniOrderedWoldResidualLogDiscrepancy :
    Tendsto xiHeatCassiniOrderedWoldResidualLogDiscrepancy atTop (𝓝 0) := by
  have h := tendsto_xiHeatCassiniOrderedWoldLogDiscrepancy.sub_const
    xiHeatCassiniWoldLogHolonomyConstant
  rw [sub_self] at h
  apply h.congr'
  filter_upwards with N
  rfl

/-- Terminal flux carried by the vanishing residual primitive. -/
def xiHeatCassiniOrderedWoldResidualTerminalFlux
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N *
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy N

/-- Connection atom carried by the vanishing residual primitive. -/
def xiHeatCassiniOrderedWoldResidualConnectionAtom
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
    (xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N -
      xiHeatCassiniOrderedPrimeHalfDensityProfile a τ (N + 1))

/-- Discrepancy terminal flux splits into constant holonomy and vanishing residual flux. -/
theorem xiHeatCassiniOrderedWoldDiscrepancyTerminalFlux_eq_holonomy_add_residual
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    xiHeatCassiniOrderedWoldDiscrepancyTerminalFlux a τ N =
      (xiHeatCassiniWoldLogHolonomyConstant : ℂ) *
        xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N +
      xiHeatCassiniOrderedWoldResidualTerminalFlux a τ N := by
  unfold xiHeatCassiniOrderedWoldDiscrepancyTerminalFlux
    xiHeatCassiniOrderedWoldResidualTerminalFlux
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy
  push_cast
  ring

/-- Every discrepancy connection atom splits into constant holonomy and vanishing residual. -/
theorem xiHeatCassiniOrderedWoldDiscrepancyConnectionAtom_eq_holonomy_add_residual
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    xiHeatCassiniOrderedWoldDiscrepancyConnectionAtom a τ N =
      (xiHeatCassiniWoldLogHolonomyConstant : ℂ) *
        (xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N -
          xiHeatCassiniOrderedPrimeHalfDensityProfile a τ (N + 1)) +
      xiHeatCassiniOrderedWoldResidualConnectionAtom a τ N := by
  unfold xiHeatCassiniOrderedWoldDiscrepancyConnectionAtom
    xiHeatCassiniOrderedWoldResidualConnectionAtom
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy
  push_cast
  ring

/-- **Static-holonomy telescope.**  The nonvanishing part of the bounded Wold discrepancy is exactly
one fixed first-prime boundary atom; every remaining arithmetic connection coefficient tends to
zero. -/
theorem xiHeatCassiniOrderedWoldDiscrepancyFlux_eq_staticHolonomy_add_residual
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    xiHeatCassiniOrderedWoldDiscrepancyTerminalFlux a τ N +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniOrderedWoldDiscrepancyConnectionAtom a τ n =
      (xiHeatCassiniWoldLogHolonomyConstant : ℂ) *
        xiHeatCassiniOrderedPrimeHalfDensityProfile a τ 0 +
      (xiHeatCassiniOrderedWoldResidualTerminalFlux a τ N +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniOrderedWoldResidualConnectionAtom a τ n) := by
  rw [xiHeatCassiniOrderedWoldDiscrepancyTerminalFlux_eq_holonomy_add_residual]
  conv_lhs =>
    enter [2, 2, n]
    rw [xiHeatCassiniOrderedWoldDiscrepancyConnectionAtom_eq_holonomy_add_residual]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub']
  ring

/-- **Convergent centered logarithmic connection law.**  Every finite pure Wold prefix consists of
the logarithmic-mesh current, one static holonomy atom, and a residual connection whose arithmetic
primitive tends to zero. -/
theorem sum_range_pureWoldHalfDensityAtom_eq_logMesh_add_staticHolonomy_add_residual
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
        xiHeatCassiniPureWoldHalfDensityAtom a τ (nthPrimeSubtype n) =
      (xiHeatCassiniOrderedLogMeshTerminalFlux a τ N +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniOrderedLogMeshConnectionAtom a τ n) +
      ((xiHeatCassiniWoldLogHolonomyConstant : ℂ) *
        xiHeatCassiniOrderedPrimeHalfDensityProfile a τ 0 +
      (xiHeatCassiniOrderedWoldResidualTerminalFlux a τ N +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniOrderedWoldResidualConnectionAtom a τ n)) := by
  rw [sum_range_pureWoldHalfDensityAtom_eq_logMesh_add_boundedDiscrepancy,
    xiHeatCassiniOrderedWoldDiscrepancyFlux_eq_staticHolonomy_add_residual]

end

end RHTower
