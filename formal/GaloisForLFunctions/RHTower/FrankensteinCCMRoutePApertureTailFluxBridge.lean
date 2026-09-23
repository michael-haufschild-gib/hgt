import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDefectFirstFlux
import GaloisForLFunctions.RHTower.FrankensteinCCMRoutePBaseCubicGreenSourceBridge

/-!
# CCM/Route-P infinitesimal aperture-tail flux bridge

P-G188 splits weighted-aperture energy loss into a deleted hard-edge interval and a distributed
tail cocycle.  This module proves that the edge interval has zero first variation at the balanced
wall and the tail cocycle carries the entire first-order defect.  Its prime-depth coefficient is
exactly a literal CCM critical-Mellin atom tested against a quadratic Green profile.  Thus the
candidate infinitesimal polar--Gamma completion current is identified coefficient-faithfully
before Xi-divisor expansion.  No trace domination or RH conclusion is asserted.
-/

open Matrix MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The deleted hard-edge interval carries no first-order primitive mass. -/
theorem hasDerivWithinAt_routePPrimitiveBurnolApertureBoundaryDefectEnergy_zero
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    HasDerivWithinAt
      (fun c : ℝ => routePBurnolApertureEnergy
        (routePBurnolApertureBoundaryDefect c
          (routePPrimitiveBurnolWindowFeature pe kappa)))
      0 (Set.Ici 0) 0 := by
  let g : ℝ → ℝ := fun u =>
    ‖routePPrimitiveBurnolWindowFeature pe kappa u‖ ^ (2 : ℕ)
  have hgcont : Continuous g := by
    dsimp [g]
    exact (continuous_routePPrimitiveBurnolWindowFeature pe kappa).norm.pow 2
  have hbase : HasDerivAt (fun c : ℝ => ∫ u in (0 : ℝ)..c, g u) 0 0 := by
    have h := (hgcont.integral_hasStrictDerivAt 0 0).hasDerivAt
    simpa [g, routePPrimitiveBurnolWindowFeature,
      xiWardCubicBurnolWindowConormalFeature_eq,
      routePXiBaseConormalResidueFeature] using h
  apply hbase.hasDerivWithinAt.congr
  · intro c hc
    rw [routePBurnolApertureEnergy_boundaryDefect]
    exact (intervalIntegral.integral_of_le hc).symm
  · rw [routePBurnolApertureEnergy_boundaryDefect]
    simp

/-- The distributed P-G188 tail cocycle, not the deleted edge interval, carries the entire
first-order defect flux. -/
theorem hasDerivWithinAt_routePPrimitiveBurnolApertureTailDefectEnergy_zero
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    HasDerivWithinAt
      (fun c : ℝ => routePBurnolApertureEnergy
        (routePBurnolApertureTailDefect c
          (routePPrimitiveBurnolWindowFeature pe kappa)))
      (routePPrimitiveBurnolApertureDefectFlux pe) (Set.Ici 0) 0 := by
  have hmass :=
    (hasDerivAt_routePPrimitiveBurnolApertureDefectMass_zero pe).hasDerivWithinAt
      (s := Set.Ici 0)
  have hedge :=
    hasDerivWithinAt_routePPrimitiveBurnolApertureBoundaryDefectEnergy_zero pe kappa
  have hdiff := hmass.sub hedge
  have htail : HasDerivWithinAt
      (fun c : ℝ => routePBurnolApertureEnergy
        (routePBurnolApertureTailDefect c
          (routePPrimitiveBurnolWindowFeature pe kappa)))
      (routePPrimitiveBurnolApertureDefectFlux pe - 0) (Set.Ici 0) 0 := by
    apply hdiff.congr
    · intro c hc
      have henergy := routePPrimitiveBurnolApertureDefect_energy_eq_mass hc pe kappa
      simp only [Pi.sub_apply]
      linarith
    · have henergy := routePPrimitiveBurnolApertureDefect_energy_eq_mass
        (c := (0 : ℝ)) le_rfl pe kappa
      simp only [Pi.sub_apply]
      linarith
  simpa only [sub_zero] using htail

/-- Natural-number coefficient of the infinitesimal P-G188 tail flux. -/
def routePPrimeGammaApertureDefectFluxWeight (n : ℕ) : ℝ :=
  2 * Real.log n * routePPrimeGammaBaseCubicWeight n

/-- Prime labels and divisor depth are retained by the infinitesimal flux. -/
theorem routePPrimeGammaApertureDefectFluxWeight_valuation
    (pe : Nat.Primes × ℕ) :
    routePPrimeGammaApertureDefectFluxWeight (xiGammaEulerValuationNat pe) =
    routePPrimitiveBurnolApertureDefectFlux pe := by
  rw [routePPrimeGammaApertureDefectFluxWeight,
    routePPrimitiveBurnolApertureDefectFlux,
    routePPrimeGammaBaseCubicWeight_valuation]
  congr 2

/-- Quadratic Green profile selected by the first variation of P-G188's cubic source mass. -/
def ccmRoutePApertureTailFluxGreenLogProfile (h : ℝ) : ℝ :=
  Real.exp (-h / 2) / (2 * (max h (Real.log 2)) ^ (2 : ℕ))

/-- The quadratic flux profile on the compact CCM physical horizon. -/
def ccmRoutePApertureTailFluxGreenHorizonTest (a : ℝ) :
    C(CCMGuinandWeilHorizon, ℝ) := by
  refine ⟨fun omega => ccmRoutePApertureTailFluxGreenLogProfile
    (2 * a * (1 - omega.1)), ?_⟩
  unfold ccmRoutePApertureTailFluxGreenLogProfile
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro omega
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hmax : Real.log 2 ≤ max (2 * a * (1 - omega.1)) (Real.log 2) :=
      le_max_right _ _
    positivity

theorem ccmRoutePApertureTailFluxGreenLogProfile_log
    {n : ℕ} (hn : 2 ≤ n) :
    ccmRoutePApertureTailFluxGreenLogProfile (Real.log n) =
      Real.exp (-Real.log n / 2) / (2 * Real.log n ^ (2 : ℕ)) := by
  rw [ccmRoutePApertureTailFluxGreenLogProfile, max_eq_left]
  exact Real.strictMonoOn_log.monotoneOn
    (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (n : ℝ) ∈ Set.Ioi 0 by
      change 0 < (n : ℝ)
      exact_mod_cast (show 0 < n by omega))
    (by exact_mod_cast hn)

/-- Atomwise P-G188/CCM seam: the tail-cocycle flux is the literal critical-Mellin atom tested
against the quadratic Green profile. -/
theorem criticalMellinAtomWeight_mul_tailFluxGreenProfile
    {n : ℕ} (hn : 2 ≤ n) :
    criticalMellinAtomWeight n *
        ccmRoutePApertureTailFluxGreenLogProfile (Real.log n) =
      routePPrimeGammaApertureDefectFluxWeight n := by
  rw [ccmRoutePApertureTailFluxGreenLogProfile_log hn,
    routePPrimeGammaApertureDefectFluxWeight,
    routePPrimeGammaBaseCubicWeight, routePPrimeGammaCubicWeight,
    vonMangoldtInverseLogPowerWeight]
  rw [show 0 + 3 = 3 by omega]
  rw [← criticalMellinAtomWeight_mul_exp_neg_log_half
    (show 0 < n by omega)]
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  field_simp [hlog]
  ring

theorem ccmRoutePApertureTailFluxGreenHorizonTest_log
    {a : ℝ} (ha : 0 < a) {h : ℝ}
    (hh : h ∈ Set.Icc (0 : ℝ) (2 * a)) :
    ccmRoutePApertureTailFluxGreenHorizonTest a
        (ccmGuinandWeilLogToHorizon a h) =
      ccmRoutePApertureTailFluxGreenLogProfile h := by
  change ccmRoutePApertureTailFluxGreenLogProfile
      (2 * a * (1 - (ccmGuinandWeilLogToHorizon a h).1)) = _
  rw [ccmGuinandWeilLogToHorizon_coe_of_mem ha hh]
  congr 1
  field_simp [ha.ne']
  ring

/-- Every finite CCM prime functional on the flux profile is exactly the negative truncated
P-G188 infinitesimal defect flux. -/
theorem ccmGuinandWeilPrimeSourceFunctional_tailFluxGreen_eq
    {a : ℝ} (ha : 0 < a) :
    ccmGuinandWeilPrimeSourceFunctional a
        (ccmRoutePApertureTailFluxGreenHorizonTest a) =
      -∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        routePPrimeGammaApertureDefectFluxWeight n := by
  rw [ccmGuinandWeilPrimeSourceFunctional_apply]
  calc
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        -criticalMellinAtomWeight n *
          ccmRoutePApertureTailFluxGreenHorizonTest a
            (ccmGuinandWeilLogToHorizon a (Real.log n)) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        -routePPrimeGammaApertureDefectFluxWeight n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ccmRoutePApertureTailFluxGreenHorizonTest_log ha
          (ccmGuinandWeilPrimeLog_mem hn), neg_mul,
        criticalMellinAtomWeight_mul_tailFluxGreenProfile
          (Finset.mem_Icc.mp hn).1]
    _ = -∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        routePPrimeGammaApertureDefectFluxWeight n := by
      rw [Finset.sum_neg_distrib]

/-- Exact polar/prime fracture for the first-variation current. -/
theorem ccmGuinandWeilPolarPrimeSourceFunctional_tailFluxGreen_eq
    {a : ℝ} (ha : 0 < a) :
    ccmGuinandWeilPolarPrimeSourceFunctional ha
        (ccmRoutePApertureTailFluxGreenHorizonTest a) =
      ccmGuinandWeilPoleSourceFunctional ha
          (ccmRoutePApertureTailFluxGreenHorizonTest a) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          routePPrimeGammaApertureDefectFluxWeight n := by
  rw [ccmGuinandWeilPolarPrimeSourceFunctional, _root_.add_apply,
    ccmGuinandWeilPrimeSourceFunctional_tailFluxGreen_eq ha]
  ring

end

end RHTower
