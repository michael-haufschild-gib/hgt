import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelAbelRenormalization
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldRequiredResidualContinuation

/-!
# Rotated Borel continuation and exact Route-T Stokes charge

The source-ordered lower Borel ray is anchored to the canonical required-residual continuation.
Rotation `s = i z` then transports every surviving off-line Wold pole of multiplicity `m` to an
exact imaginary Borel residue `i m`.  Consequently regularity of this forced Borel continuation at
all rotated candidate poles is, under critical mesh energy, equivalent to RH.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Canonical required residual written in the Borel source coordinate `s = i z`. -/
def xiHeatCassiniWoldResidualBorelRenormalizedContinuation (z : ℂ) : ℂ :=
  xiHeatCassiniWoldResidualLaplaceContinuation (Complex.I * z)

/-- On the safe lower half-plane, the rotated continuation is the actual residual Hardy source. -/
theorem xiHeatCassiniWoldResidualBorelRenormalizedContinuation_eq_lowerHardy
    {z : ℂ} (hz : z.im < 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    xiHeatCassiniWoldResidualBorelRenormalizedContinuation z =
      xiHeatCassiniWoldResidualLowerHardyKernel z := by
  unfold xiHeatCassiniWoldResidualBorelRenormalizedContinuation
  have hs : 0 < (Complex.I * z).re := by
    simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul,
      zero_sub]
    linarith
  rw [xiHeatCassiniWoldResidualLaplaceContinuation_eq_lowerHardy hs hcritical]
  congr 1
  calc
    -Complex.I * (Complex.I * z) =
        -(Complex.I * Complex.I) * z := by ring
    _ = z := by rw [Complex.I_mul_I]; ring

/-- The source-ordered negative Borel ray lands on the forced continuation, not an auxiliary
branch. -/
theorem xiHeatCassiniWoldResidualBorelRenormalizedContinuation_eq_lowerRayLaplace
    (x : ℝ) {y : ℝ} (hy : 0 < y)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    xiHeatCassiniWoldResidualBorelRenormalizedContinuation
        ((x : ℂ) - (y : ℂ) * Complex.I) =
      ∫ t : ℝ in Ioi 0,
        ((Real.exp (-t) : ℝ) : ℂ) *
          xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier x (y * t) := by
  rw [xiHeatCassiniWoldResidualBorelRenormalizedContinuation_eq_lowerHardy
      (by simp; linarith) hcritical,
    integral_exp_neg_mul_xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier_eq_lowerHardy
      x hy.le]

private theorem tendsto_I_mul_punctured (a : ℂ) :
    Tendsto (fun z : ℂ => Complex.I * z)
      (𝓝[≠] (-Complex.I * a)) (𝓝[≠] a) := by
  have hcenter : Complex.I * (-Complex.I * a) = a := by
    rw [show Complex.I * (-Complex.I * a) =
        -(Complex.I * Complex.I) * a by ring, Complex.I_mul_I]
    ring
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcontinuous :
        ContinuousAt (fun z : ℂ => Complex.I * z) (-Complex.I * a) :=
      continuousAt_const.mul continuousAt_id
    simpa only [hcenter] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    change z ≠ -Complex.I * a at hz
    change Complex.I * z ≠ a
    intro heq
    apply hz
    calc
      z = -Complex.I * (Complex.I * z) := by
        rw [show -Complex.I * (Complex.I * z) =
          -(Complex.I * Complex.I) * z by ring, Complex.I_mul_I]
        ring
      _ = -Complex.I * a := by rw [heq]

/-- Every off-line Wold pole becomes an exact nonzero imaginary Borel charge `i m`. -/
theorem xiHeatCassiniWoldResidualBorelRenormalizedContinuation_nonzero_residue_of_criticalEnergy
    {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (hzeta : riemannZeta rho = 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun z : ℂ =>
        (z - (-Complex.I * (rho - 1))) *
          xiHeatCassiniWoldResidualBorelRenormalizedContinuation z)
        (𝓝[≠] (-Complex.I * (rho - 1)))
        (𝓝 (Complex.I * (m : ℂ))) := by
  obtain ⟨m, hm, hpole⟩ :=
    xiHeatCassiniWoldResidualLaplaceContinuation_nonzero_residue_of_criticalEnergy
      hrho hzeta hcritical
  refine ⟨m, hm, ?_⟩
  have hcomp := hpole.comp (tendsto_I_mul_punctured (rho - 1))
  have hscaled :
      Tendsto (fun z : ℂ =>
        (-Complex.I) *
          (((Complex.I * z) - (rho - 1)) *
            xiHeatCassiniWoldResidualLaplaceContinuation (Complex.I * z)))
        (𝓝[≠] (-Complex.I * (rho - 1)))
        (𝓝 ((-Complex.I) * (-(m : ℂ)))) :=
    tendsto_const_nhds.mul hcomp
  convert hscaled using 1
  · funext z
    unfold xiHeatCassiniWoldResidualBorelRenormalizedContinuation
    have hcoord : z - -Complex.I * (rho - 1) =
        -Complex.I * (Complex.I * z - (rho - 1)) := by
      calc
        z - -Complex.I * (rho - 1) =
            z + Complex.I * (rho - 1) := by ring
        _ = -(Complex.I * Complex.I) * z + Complex.I * (rho - 1) := by
          rw [Complex.I_mul_I]
          ring
        _ = -Complex.I * (Complex.I * z - (rho - 1)) := by ring
    rw [hcoord]
    ring
  · ring

/-- The exact imaginary Borel charge obstructs continuity at every rotated off-line pole. -/
theorem not_continuousAt_xiHeatCassiniWoldResidualBorelRenormalizedContinuation
    {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (hzeta : riemannZeta rho = 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    ¬ContinuousAt xiHeatCassiniWoldResidualBorelRenormalizedContinuation
      (-Complex.I * (rho - 1)) := by
  intro hcontinuous
  obtain ⟨m, hm, hpole⟩ :=
    xiHeatCassiniWoldResidualBorelRenormalizedContinuation_nonzero_residue_of_criticalEnergy
      hrho hzeta hcritical
  have hlin := tendsto_sub_self_punctured_zero (-Complex.I * (rho - 1))
  have hvalue :
      Tendsto xiHeatCassiniWoldResidualBorelRenormalizedContinuation
        (𝓝[≠] (-Complex.I * (rho - 1)))
        (𝓝 (xiHeatCassiniWoldResidualBorelRenormalizedContinuation
          (-Complex.I * (rho - 1)))) :=
    hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hzero :
      Tendsto (fun z : ℂ =>
        (z - (-Complex.I * (rho - 1))) *
          xiHeatCassiniWoldResidualBorelRenormalizedContinuation z)
        (𝓝[≠] (-Complex.I * (rho - 1))) (𝓝 0) := by
    simpa using hlin.mul hvalue
  have hunique : Complex.I * (m : ℂ) = 0 :=
    tendsto_nhds_unique hpole hzero
  have hm0 : (m : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_lt hm
  exact hm0 ((mul_eq_zero.mp hunique).resolve_left Complex.I_ne_zero)

/-- **Exact rotated-Borel Route-T endpoint.** Under critical mesh energy, RH is equivalent to
regularity of the unique continuation reached by the source-ordered lower Borel ray at every
rotated candidate pole. -/
theorem riemannHypothesis_iff_woldResidualBorelRenormalizedContinuation_continuousAt
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    RiemannHypothesis ↔
      ∀ rho : ℂ, 1 / 2 < rho.re → riemannZeta rho = 0 →
        ContinuousAt xiHeatCassiniWoldResidualBorelRenormalizedContinuation
          (-Complex.I * (rho - 1)) := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  constructor
  · intro hzeroFree rho hrho hzeta
    exact (hzeroFree rho hrho hzeta).elim
  · intro hregular rho hrho hzeta
    exact (not_continuousAt_xiHeatCassiniWoldResidualBorelRenormalizedContinuation
      hrho hzeta hcritical) (hregular rho hrho hzeta)

end

end RHTower
