import GaloisForLFunctions.RHTower.SymmetricShiftZetaEulerBridge
import GaloisForLFunctions.RHTower.SymmetricShiftFinitePrimeContinuity

/-!
# Global Euler-abscissa discontinuity at symmetric-shift collision

The full logarithmic discrepancy coefficient has absolute-convergence abscissa exactly `1+a` at
every positive shift.  At zero shift the coefficient vanishes identically and its abscissa is
bottom.  Hence the abscissa map is genuinely discontinuous at collision, even though every fixed
prime-power coordinate and finite semilocal product converge there.
-/

open Complex Filter Topology LSeries Set

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Exact real-axis absolute summability boundary for the natural-number discrepancy series. -/
theorem symmetricShiftEulerLogDiscrepancyCoeff_summable_iff
    (a : SymmetricPositiveShift) (sigma : ℝ) :
    LSeriesSummable (symmetricShiftEulerLogDiscrepancyCoeff a) (sigma : ℂ) ↔
      1 + a.1 < sigma := by
  constructor
  · intro hsum
    have hprime : Summable (fun p : Nat.Primes =>
        LSeries.term (symmetricShiftEulerLogDiscrepancyCoeff a) (sigma : ℂ) p.1) := by
      apply hsum.comp_injective (i := fun p : Nat.Primes => p.1)
      intro p q hpq
      exact Subtype.ext hpq
    have hcomplex : Summable (fun p : Nat.Primes =>
        (symmetricShiftEulerPrimeDiscrepancyTerm a sigma p : ℂ)) := by
      apply hprime.congr
      intro p
      rw [show p.1 = p.1 ^ (0 + 1) by simp,
        term_symmetricShiftEulerLogDiscrepancyCoeff_prime_pow_eq_global,
        symmetricShiftEulerGlobalDiscrepancyTerm_zero]
    have hreal := Complex.reCLM.summable hcomplex
    have hfirst : Summable (fun p : Nat.Primes =>
        symmetricShiftEulerPrimeDiscrepancyTerm a sigma p) := by
      simpa using hreal
    exact (summable_symmetricShiftEulerPrimeDiscrepancyTerm_iff a sigma).mp hfirst
  · exact fun hs => symmetricShiftEulerLogDiscrepancyCoeff_summable a (by simpa using hs)

/-- Literal absolute-convergence abscissa `1+a` of the positive-shift discrepancy coefficient. -/
theorem abscissaOfAbsConv_symmetricShiftEulerLogDiscrepancyCoeff
    (a : SymmetricPositiveShift) :
    LSeries.abscissaOfAbsConv (symmetricShiftEulerLogDiscrepancyCoeff a) =
      ((1 + a.1 : ℝ) : EReal) := by
  simpa [LSeries.abscissaOfAbsConv,
    symmetricShiftEulerLogDiscrepancyCoeff_summable_iff,
    Set.Ioi_def, EReal.image_coe_Ioi]
    using csInf_Ioo (EReal.coe_lt_top (1 + a.1))

/-- Raw discrepancy coefficient, including the zero-shift collision point. -/
def symmetricShiftEulerLogDiscrepancyCoeffRaw (a : ℝ) : ℕ → ℂ :=
  lseriesPowerTwistCoeff RHTower.eulerLogDirichletCoeff (a : ℂ) +
    lseriesPowerTwistCoeff RHTower.eulerLogDirichletCoeff (-(a : ℂ)) -
      RHTower.eulerLogDirichletCoeff - RHTower.eulerLogDirichletCoeff

/-- At collision the logarithmic discrepancy coefficient vanishes identically. -/
theorem symmetricShiftEulerLogDiscrepancyCoeffRaw_zero :
    symmetricShiftEulerLogDiscrepancyCoeffRaw 0 = 0 := by
  funext n
  simp [symmetricShiftEulerLogDiscrepancyCoeffRaw, lseriesPowerTwistCoeff]

/-- The identically zero collision discrepancy has absolute-convergence abscissa bottom. -/
theorem abscissaOfAbsConv_symmetricShiftEulerLogDiscrepancyCoeffRaw_zero :
    LSeries.abscissaOfAbsConv (symmetricShiftEulerLogDiscrepancyCoeffRaw 0) = ⊥ := by
  rw [symmetricShiftEulerLogDiscrepancyCoeffRaw_zero]
  apply le_antisymm
  · apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
    intro sigma _
    exact LSeriesSummable_zero
  · exact bot_le

/-- The raw positive-shift coefficient is the established subtype-indexed coefficient. -/
theorem symmetricShiftEulerLogDiscrepancyCoeffRaw_eq
    (a : SymmetricPositiveShift) :
    symmetricShiftEulerLogDiscrepancyCoeffRaw a.1 =
      symmetricShiftEulerLogDiscrepancyCoeff a := rfl

/-- Every positive raw shift has absolute-convergence abscissa exactly `1+a`. -/
theorem abscissaOfAbsConv_symmetricShiftEulerLogDiscrepancyCoeffRaw_pos
    {a : ℝ} (ha : 0 < a) :
    LSeries.abscissaOfAbsConv (symmetricShiftEulerLogDiscrepancyCoeffRaw a) =
      ((1 + a : ℝ) : EReal) := by
  let ap : SymmetricPositiveShift := ⟨a, ha⟩
  rw [symmetricShiftEulerLogDiscrepancyCoeffRaw_eq ap,
    abscissaOfAbsConv_symmetricShiftEulerLogDiscrepancyCoeff ap]

/-- The global discrepancy abscissa is discontinuous at the collision parameter. -/
theorem not_continuousAt_abscissaOfAbsConv_symmetricShiftEulerLogDiscrepancyCoeffRaw :
    ¬ ContinuousAt
      (fun a : ℝ => LSeries.abscissaOfAbsConv
        (symmetricShiftEulerLogDiscrepancyCoeffRaw a)) 0 := by
  let u : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hu : Tendsto u atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hupos (n : ℕ) : 0 < u n := by
    dsimp [u]
    positivity
  have hone : Tendsto (fun n => ((1 + u n : ℝ) : EReal))
      atTop (𝓝 ((1 : ℝ) : EReal)) := by
    have hreal : Tendsto (fun n => 1 + u n) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hu
    have hcoe := (continuous_coe_real_ereal.tendsto (1 : ℝ)).comp hreal
    change Tendsto (Real.toEReal ∘ fun n => 1 + u n) atTop
      (𝓝 (Real.toEReal 1))
    exact hcoe
  have habsc : Tendsto
      (fun n => LSeries.abscissaOfAbsConv
        (symmetricShiftEulerLogDiscrepancyCoeffRaw (u n)))
      atTop (𝓝 ((1 : ℝ) : EReal)) := by
    apply hone.congr'
    exact Eventually.of_forall fun n =>
      (abscissaOfAbsConv_symmetricShiftEulerLogDiscrepancyCoeffRaw_pos (hupos n)).symm
  intro hcontinuous
  have hbot := hcontinuous.tendsto.comp hu
  rw [abscissaOfAbsConv_symmetricShiftEulerLogDiscrepancyCoeffRaw_zero] at hbot
  have heq : ((1 : ℝ) : EReal) = ⊥ := tendsto_nhds_unique habsc hbot
  exact (EReal.coe_ne_bot (1 : ℝ)) heq

end

end GaloisForLFunctions.RHTower
