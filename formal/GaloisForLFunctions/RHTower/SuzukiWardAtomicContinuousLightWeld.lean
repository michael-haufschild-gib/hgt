import GaloisForLFunctions.RHTower.SuzukiCauchyWallGammaSecantAssembly
import GaloisForLFunctions.RHTower.SuzukiScrewDisjointCrossCoupling
import GaloisForLFunctions.RHTower.SuzukiWallFieldLightConeKernelCompletion

/-!
# Atomic--continuous decomposition of the Gamma-completed Suzuki Ward wall

The polar counterterm in the completed finite-prime wall cancels exactly against the endpoint
counterterm in the polar secant.  On Suzuki's full unit-Riesz aperture, the remaining
polar--Gamma density is the negative regular screw kernel.  Thus the literal complex-height Ward
wall is exactly a finite positive prime wall minus a continuous positive screw wall.

This identifies the unresolved source comparison without replacing either side by an abstract
predicate: RH-strength cancellation is cancellation between two explicit positive masses.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower

/-- Suzuki's regular screw sign threshold lies strictly below the unit-Riesz base aperture. -/
theorem screwSignThreshold_lt_unitRieszSuzukiBase :
    screwSignThreshold < unitRieszSuzukiBase := by
  have hcubic : 0 < (3 / 2 : ℝ) ^ 3 - 3 / 2 - 1 := by norm_num
  have hroot : plasticRoot < (3 / 2 : ℝ) :=
    (cubic_pos_iff_plasticRoot_lt (by norm_num)).mp hcubic
  have hlog : Real.log plasticRoot < Real.log (3 / 2 : ℝ) :=
    Real.strictMonoOn_log plasticRoot_pos (by norm_num) hroot
  have hexp : (3 / 2 : ℝ) < Real.exp (1 / 2) := by
    nlinarith [Real.add_one_lt_exp (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  have hhalf : Real.log (3 / 2 : ℝ) < 1 / 2 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3 / 2)).mpr hexp
  rw [screwSignThreshold, unitRieszSuzukiBase]
  exact hlog.trans hhalf

/-- The regular screw kernel is strictly positive throughout Suzuki's unit-Riesz aperture. -/
theorem screwRegularKernel_pos_of_unitRieszSuzukiBase_le
    {h : ℝ} (hh : unitRieszSuzukiBase ≤ h) :
    0 < screwRegularKernel h := by
  have hpos : 0 < h := unitRieszSuzukiBase_pos.trans_le hh
  exact (screwRegularKernel_pos_iff hpos).mpr
    (screwSignThreshold_lt_unitRieszSuzukiBase.trans_le hh)

/-- Finite von-Mangoldt wall before the polar counterterm is inserted. -/
def suzukiUnitRieszPrimeWardWall (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 N,
    (ArithmeticFunction.vonMangoldt k / Real.sqrt N : ℂ) *
      (1 - suzukiCauchyWallPhaseComplex
        (-(Real.log N - Real.log k)) z)

/-- Continuous regular-screw wall on Suzuki's unit-Riesz aperture. -/
def suzukiUnitRieszRegularWardWall (H : ℝ) (z : ℂ) : ℂ :=
  ∫ h in unitRieszSuzukiBase..H,
    suzukiUnitRieszReporterWallSecant H h z *
      (screwRegularKernel h : ℂ)

/-- **Atomic--continuous Ward weld.**  The full prime--polar--Gamma wall is exactly the finite
prime wall minus the regular screw continuum, at every complex height. -/
theorem suzukiUnitRieszGammaCompletedWardWall_eq_prime_sub_regular
    (N : ℕ) (z : ℂ) :
    suzukiUnitRieszGammaCompletedWardWall (N + 2) z =
      suzukiUnitRieszPrimeWardWall (N + 2) z -
        suzukiUnitRieszRegularWardWall (Real.log ((N + 2 : ℕ) : ℝ)) z := by
  have hNat : 2 ≤ N + 2 := by omega
  have hNatPos : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
  have hH : unitRieszSuzukiBase ≤ Real.log ((N + 2 : ℕ) : ℝ) :=
    (unitRieszSuzukiBase_lt_log_of_two_le hNat).le
  have hexp : Real.exp (Real.log ((N + 2 : ℕ) : ℝ) / 2) =
      Real.sqrt ((N + 2 : ℕ) : ℝ) := by
    rw [← Real.log_sqrt hNatPos.le, Real.exp_log (Real.sqrt_pos.mpr hNatPos)]
  have hpolar : IntervalIntegrable
      (fun h : ℝ =>
        suzukiUnitRieszReporterWallSecant (Real.log ((N + 2 : ℕ) : ℝ)) h z *
          ((2 * Real.cosh (h / 2) : ℝ) : ℂ)) volume
      unitRieszSuzukiBase (Real.log ((N + 2 : ℕ) : ℝ)) := by
    apply Continuous.intervalIntegrable
    unfold suzukiUnitRieszReporterWallSecant suzukiCauchyWallPhaseComplex
      suzukiOscillatoryKernel
    fun_prop
  have hscrewContinuous : ContinuousOn
      (fun h : ℝ =>
        suzukiUnitRieszReporterWallSecant (Real.log ((N + 2 : ℕ) : ℝ)) h z *
          (screwRegularKernel h : ℂ))
      (uIcc unitRieszSuzukiBase (Real.log ((N + 2 : ℕ) : ℝ))) := by
    have hreporter : Continuous
        (fun h : ℝ =>
          suzukiUnitRieszReporterWallSecant (Real.log ((N + 2 : ℕ) : ℝ)) h z) := by
      unfold suzukiUnitRieszReporterWallSecant suzukiCauchyWallPhaseComplex
        suzukiOscillatoryKernel
      fun_prop
    apply hreporter.continuousOn.mul
    apply Complex.continuous_ofReal.comp_continuousOn
    apply continuousOn_screwRegularKernel.mono
    intro h hh
    rw [uIcc_of_le hH] at hh
    exact unitRieszSuzukiBase_pos.trans_le hh.1
  have hscrew : IntervalIntegrable
      (fun h : ℝ =>
        suzukiUnitRieszReporterWallSecant (Real.log ((N + 2 : ℕ) : ℝ)) h z *
          (screwRegularKernel h : ℂ)) volume
      unitRieszSuzukiBase (Real.log ((N + 2 : ℕ) : ℝ)) :=
    hscrewContinuous.intervalIntegrable
  have harchEq :
      (∫ h in unitRieszSuzukiBase..Real.log ((N + 2 : ℕ) : ℝ),
        suzukiUnitRieszReporterWallSecant (Real.log ((N + 2 : ℕ) : ℝ)) h z *
          (ccmPublishedArchimedeanDensity h : ℂ)) =
        (∫ h in unitRieszSuzukiBase..Real.log ((N + 2 : ℕ) : ℝ),
          suzukiUnitRieszReporterWallSecant (Real.log ((N + 2 : ℕ) : ℝ)) h z *
            ((2 * Real.cosh (h / 2) : ℝ) : ℂ)) -
        ∫ h in unitRieszSuzukiBase..Real.log ((N + 2 : ℕ) : ℝ),
          suzukiUnitRieszReporterWallSecant (Real.log ((N + 2 : ℕ) : ℝ)) h z *
            (screwRegularKernel h : ℂ) := by
    rw [← intervalIntegral.integral_sub hpolar hscrew]
    apply intervalIntegral.integral_congr
    intro h hh
    rw [uIcc_of_le hH] at hh
    have hhpos : 0 < h := unitRieszSuzukiBase_pos.trans_le hh.1
    change suzukiUnitRieszReporterWallSecant (Real.log ((N + 2 : ℕ) : ℝ)) h z *
        (ccmPublishedArchimedeanDensity h : ℂ) =
      suzukiUnitRieszReporterWallSecant (Real.log ((N + 2 : ℕ) : ℝ)) h z *
          ((2 * Real.cosh (h / 2) : ℝ) : ℂ) -
        suzukiUnitRieszReporterWallSecant (Real.log ((N + 2 : ℕ) : ℝ)) h z *
          (screwRegularKernel h : ℂ)
    have hdensity : ccmPublishedArchimedeanDensity h =
        2 * Real.cosh (h / 2) - screwRegularKernel h := by
      linarith [ccmPublishedArchimedeanDensity_sub_two_cosh_eq_neg_screwRegularKernel hhpos]
    rw [hdensity]
    push_cast
    ring
  rw [suzukiUnitRieszGammaCompletedWardWall,
    suzukiUnitRieszCompletedCauchyWallSymbolComplex,
    suzukiUnitRieszPolarWallSecant,
    suzukiUnitRieszArchWallSecant,
    suzukiUnitRieszPrimeWardWall,
    suzukiUnitRieszRegularWardWall, hexp, harchEq]
  ring

/-- Real continuous mass read at the lower Hardy point. -/
def suzukiUnitRieszRegularWardMass (H : ℝ) : ℝ :=
  ∫ h in unitRieszSuzukiBase..H,
    unitRieszSuzukiReporter H h * screwRegularKernel h

@[simp] theorem suzukiUnitRieszPrimeWardWall_neg_I
    (N : ℕ) :
    suzukiUnitRieszPrimeWardWall N (-I) =
      (unitRieszCoherentPrimeOutgoingCharge N : ℂ) := by
  rw [suzukiUnitRieszPrimeWardWall,
    unitRieszCoherentPrimeOutgoingCharge]
  simp only [suzukiCauchyWallPhaseComplex_neg_I]
  push_cast
  rfl

@[simp] theorem suzukiUnitRieszRegularWardWall_neg_I
    (H : ℝ) :
    suzukiUnitRieszRegularWardWall H (-I) =
      (suzukiUnitRieszRegularWardMass H : ℂ) := by
  rw [suzukiUnitRieszRegularWardWall,
    suzukiUnitRieszRegularWardMass]
  calc
    (∫ h in unitRieszSuzukiBase..H,
        suzukiUnitRieszReporterWallSecant H h (-I) *
          (screwRegularKernel h : ℂ)) =
      ∫ h in unitRieszSuzukiBase..H,
        ((unitRieszSuzukiReporter H h * screwRegularKernel h : ℝ) : ℂ) := by
          apply intervalIntegral.integral_congr
          intro h hh
          change suzukiUnitRieszReporterWallSecant H h (-I) *
              (screwRegularKernel h : ℂ) =
            ((unitRieszSuzukiReporter H h * screwRegularKernel h : ℝ) : ℂ)
          rw [suzukiUnitRieszReporterWallSecant_neg_I]
          push_cast
          rfl
    _ = _ := intervalIntegral.integral_ofReal

/-- The finite atomic mass is nonnegative at every nondegenerate natural aperture. -/
theorem unitRieszCoherentPrimeOutgoingCharge_nonneg_add_two
    (N : ℕ) :
    0 ≤ unitRieszCoherentPrimeOutgoingCharge (N + 2) := by
  rw [unitRieszCoherentPrimeOutgoingCharge_eq_energy_half (by omega),
    unitRieszCoherentPrimeEnergy]
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro k hk
    apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    apply div_nonneg
    · rw [unitExponentialCoherentDistanceSq]
      exact integral_nonneg fun s => sq_nonneg _
    · exact Real.sqrt_nonneg _
  · norm_num

/-- The continuous regular-screw mass is nonnegative on every Suzuki aperture. -/
theorem suzukiUnitRieszRegularWardMass_nonneg
    {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    0 ≤ suzukiUnitRieszRegularWardMass H := by
  rw [suzukiUnitRieszRegularWardMass]
  apply intervalIntegral.integral_nonneg hH
  intro h hh
  exact mul_nonneg (unitRieszSuzukiReporter_nonneg_of_mem hh.2)
    (screwRegularKernel_pos_of_unitRieszSuzukiBase_le hh.1).le

/-- At the lower Hardy point, Suzuki Green is the exact atomic--continuous mass imbalance. -/
theorem unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass
    (N : ℕ) :
    unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) =
      unitRieszCoherentPrimeOutgoingCharge (N + 2) -
        suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ)) := by
  have hwall :=
    suzukiUnitRieszGammaCompletedWardWall_eq_prime_sub_regular N (-I)
  rw [suzukiUnitRieszGammaCompletedWardWall_add_two_neg_I_eq_green,
    suzukiUnitRieszPrimeWardWall_neg_I,
    suzukiUnitRieszRegularWardWall_neg_I] at hwall
  exact_mod_cast hwall

/-- Exact positive-mass form of the Suzuki Ward source comparison. -/
theorem suzukiWardAtomicContinuousPositiveDecomposition
    (N : ℕ) :
    unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) =
        unitRieszCoherentPrimeOutgoingCharge (N + 2) -
          suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ)) ∧
      0 ≤ unitRieszCoherentPrimeOutgoingCharge (N + 2) ∧
      0 ≤ suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ)) := by
  refine ⟨unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass N,
    unitRieszCoherentPrimeOutgoingCharge_nonneg_add_two N, ?_⟩
  exact suzukiUnitRieszRegularWardMass_nonneg
    ((unitRieszSuzukiBase_lt_log_of_two_le (by omega : 2 ≤ N + 2)).le)

/-! ## Literal wall-light occurrence of the finite prime mass -/

private def suzukiUnitRieszPrimeReporterCell (N n : ℕ) : ℝ :=
  if n ∈ Finset.Icc 2 N then
    criticalMellinAtomWeight n *
      unitRieszSuzukiReporter (Real.log N) (Real.log n)
  else 0

private theorem suzukiUnitRieszPrimeReporterCell_sum
    {N : ℕ} (hN : 2 ≤ N) :
    (∑' n : ℕ, suzukiUnitRieszPrimeReporterCell N n) =
      unitRieszCoherentPrimeOutgoingCharge N := by
  rw [tsum_eq_sum (s := Finset.Icc 2 N) (by
    intro n hn
    simp [suzukiUnitRieszPrimeReporterCell, hn])]
  calc
    (∑ n ∈ Finset.Icc 2 N, suzukiUnitRieszPrimeReporterCell N n) =
        ∑ n ∈ Finset.Icc 2 N,
          criticalMellinAtomWeight n *
            unitRieszSuzukiReporter (Real.log N) (Real.log n) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [suzukiUnitRieszPrimeReporterCell, hn]
    _ = _ := unitRieszSuzuki_prime_sum hN

private theorem summable_suzukiUnitRieszPrimeReporterCell (N : ℕ) :
    Summable (suzukiUnitRieszPrimeReporterCell N) := by
  refine summable_of_ne_finset_zero (s := Finset.Icc 2 N) ?_
  intro n hn
  simp [suzukiUnitRieszPrimeReporterCell, hn]

private theorem suzukiUnitRieszPrimeReporterCell_support_primePower (N : ℕ) :
    Function.support (suzukiUnitRieszPrimeReporterCell N) ⊆
      {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra hpow
  have hzero : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
  exact hn (by simp [suzukiUnitRieszPrimeReporterCell,
    criticalMellinAtomWeight, hzero])

private theorem tsum_suzukiUnitRieszPrimeReporterCell_valuation
    (N : ℕ) :
    (∑' pe : Nat.Primes × ℕ,
      suzukiUnitRieszPrimeReporterCell N
        (xiGammaEulerValuationNat pe)) =
      ∑' n : ℕ, suzukiUnitRieszPrimeReporterCell N n := by
  have hs := summable_suzukiUnitRieszPrimeReporterCell N
  have hreindex := tsum_eq_tsum_primes_of_support_subset_prime_powers hs
    (suzukiUnitRieszPrimeReporterCell_support_primePower N)
  have hcomp : Summable (fun pe : Nat.Primes × ℕ =>
      suzukiUnitRieszPrimeReporterCell N
        (xiGammaEulerValuationNat pe)) :=
    hs.comp_injective xiGammaEulerValuationNat_injective_commonTest
  calc
    (∑' pe : Nat.Primes × ℕ,
        suzukiUnitRieszPrimeReporterCell N
          (xiGammaEulerValuationNat pe)) =
        ∑' p : Nat.Primes, ∑' e : ℕ,
          suzukiUnitRieszPrimeReporterCell N (p.1 ^ (e + 1)) := by
      simpa [xiGammaEulerValuationNat] using hcomp.tsum_prod
    _ = _ := hreindex.symm

/-- Reporter-weighted total wall-light energy below the natural aperture. -/
def suzukiUnitRieszReporterWeightedWallLightMass
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑' pe : Nat.Primes × ℕ,
    if xiGammaEulerValuationNat pe ≤ N then
      unitRieszSuzukiReporter (Real.log N)
          (Real.log (xiGammaEulerValuationNat pe)) *
        (normSq (suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2) +
          normSq (suzukiCriticalWallNegativeLightAmplitude t pe.1 pe.2))
    else 0

private theorem suzukiUnitRieszPrimeReporterCell_valuation_eq_wallLight
    (N : ℕ) (t : ℝ) (pe : Nat.Primes × ℕ) :
    suzukiUnitRieszPrimeReporterCell N
        (xiGammaEulerValuationNat pe) =
      if xiGammaEulerValuationNat pe ≤ N then
        unitRieszSuzukiReporter (Real.log N)
            (Real.log (xiGammaEulerValuationNat pe)) *
          (normSq (suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2) +
            normSq (suzukiCriticalWallNegativeLightAmplitude t pe.1 pe.2))
      else 0 := by
  have hval : 2 ≤ xiGammaEulerValuationNat pe := by
    rw [xiGammaEulerValuationNat]
    exact pe.1.property.two_le.trans (Nat.le_pow (by omega))
  by_cases hle : xiGammaEulerValuationNat pe ≤ N
  · rw [if_pos hle]
    simp only [suzukiUnitRieszPrimeReporterCell,
      if_pos (Finset.mem_Icc.mpr ⟨hval, hle⟩)]
    rw [normSq_suzukiCriticalWallLightAmplitudes_eq_vonMangoldt_div_sqrt,
      criticalMellinAtomWeight_eq_screwPrimeWeight (by omega),
      screwPrimeWeight]
    ring
  · rw [if_neg hle]
    simp [suzukiUnitRieszPrimeReporterCell, hle]

/-- **Prime source occurrence.**  At every height, the finite prime Ward mass is exactly total
reporter-weighted energy in the literal positive/negative wall-light plane. -/
theorem suzukiUnitRieszReporterWeightedWallLightMass_eq_primeOutgoingCharge
    {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    suzukiUnitRieszReporterWeightedWallLightMass N t =
      unitRieszCoherentPrimeOutgoingCharge N := by
  rw [suzukiUnitRieszReporterWeightedWallLightMass]
  calc
    (∑' pe : Nat.Primes × ℕ,
        if xiGammaEulerValuationNat pe ≤ N then
          unitRieszSuzukiReporter (Real.log N)
              (Real.log (xiGammaEulerValuationNat pe)) *
            (normSq (suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2) +
              normSq (suzukiCriticalWallNegativeLightAmplitude t pe.1 pe.2))
        else 0) =
      ∑' pe : Nat.Primes × ℕ,
        suzukiUnitRieszPrimeReporterCell N
          (xiGammaEulerValuationNat pe) := by
      apply tsum_congr
      intro pe
      exact (suzukiUnitRieszPrimeReporterCell_valuation_eq_wallLight N t pe).symm
    _ = ∑' n : ℕ, suzukiUnitRieszPrimeReporterCell N n :=
      tsum_suzukiUnitRieszPrimeReporterCell_valuation N
    _ = _ := suzukiUnitRieszPrimeReporterCell_sum hN

/-- Reporter-weighted positive-light mass below the natural aperture. -/
def suzukiUnitRieszReporterWeightedPositiveLightMass
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑' pe : Nat.Primes × ℕ,
    if xiGammaEulerValuationNat pe ≤ N then
      unitRieszSuzukiReporter (Real.log N)
          (Real.log (xiGammaEulerValuationNat pe)) *
        normSq (suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2)
    else 0

/-- Reporter-weighted negative-light mass below the natural aperture. -/
def suzukiUnitRieszReporterWeightedNegativeLightMass
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑' pe : Nat.Primes × ℕ,
    if xiGammaEulerValuationNat pe ≤ N then
      unitRieszSuzukiReporter (Real.log N)
          (Real.log (xiGammaEulerValuationNat pe)) *
        normSq (suzukiCriticalWallNegativeLightAmplitude t pe.1 pe.2)
    else 0

private theorem reporter_nonneg_of_valuation_le
    {N : ℕ} {pe : Nat.Primes × ℕ}
    (hle : xiGammaEulerValuationNat pe ≤ N) :
    0 ≤ unitRieszSuzukiReporter (Real.log N)
      (Real.log (xiGammaEulerValuationNat pe)) := by
  have hval : 0 < xiGammaEulerValuationNat pe := by
    have hval2 : 2 ≤ xiGammaEulerValuationNat pe := by
      rw [xiGammaEulerValuationNat]
      exact pe.1.property.two_le.trans (Nat.le_pow (by omega))
    omega
  apply unitRieszSuzukiReporter_nonneg_of_mem
  exact Real.log_le_log (by exact_mod_cast hval) (by exact_mod_cast hle)

private theorem summable_reporterWeightedWallLightTotal
    (N : ℕ) (t : ℝ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      if xiGammaEulerValuationNat pe ≤ N then
        unitRieszSuzukiReporter (Real.log N)
            (Real.log (xiGammaEulerValuationNat pe)) *
          (normSq (suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2) +
            normSq (suzukiCriticalWallNegativeLightAmplitude t pe.1 pe.2))
      else 0) := by
  have hs := (summable_suzukiUnitRieszPrimeReporterCell N).comp_injective
    xiGammaEulerValuationNat_injective_commonTest
  exact hs.congr fun pe =>
    suzukiUnitRieszPrimeReporterCell_valuation_eq_wallLight N t pe

private theorem summable_reporterWeightedPositiveLight
    (N : ℕ) (t : ℝ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      if xiGammaEulerValuationNat pe ≤ N then
        unitRieszSuzukiReporter (Real.log N)
            (Real.log (xiGammaEulerValuationNat pe)) *
          normSq (suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2)
      else 0) := by
  refine Summable.of_nonneg_of_le (fun pe => ?_) (fun pe => ?_)
    (summable_reporterWeightedWallLightTotal N t)
  · by_cases hle : xiGammaEulerValuationNat pe ≤ N
    · simp only [if_pos hle]
      exact mul_nonneg (reporter_nonneg_of_valuation_le hle)
        (Complex.normSq_nonneg _)
    · simp [hle]
  · by_cases hle : xiGammaEulerValuationNat pe ≤ N
    · simp only [if_pos hle]
      have hrep := reporter_nonneg_of_valuation_le hle
      have hneg := Complex.normSq_nonneg
        (suzukiCriticalWallNegativeLightAmplitude t pe.1 pe.2)
      nlinarith
    · simp [hle]

private theorem summable_reporterWeightedNegativeLight
    (N : ℕ) (t : ℝ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      if xiGammaEulerValuationNat pe ≤ N then
        unitRieszSuzukiReporter (Real.log N)
            (Real.log (xiGammaEulerValuationNat pe)) *
          normSq (suzukiCriticalWallNegativeLightAmplitude t pe.1 pe.2)
      else 0) := by
  refine Summable.of_nonneg_of_le (fun pe => ?_) (fun pe => ?_)
    (summable_reporterWeightedWallLightTotal N t)
  · by_cases hle : xiGammaEulerValuationNat pe ≤ N
    · simp only [if_pos hle]
      exact mul_nonneg (reporter_nonneg_of_valuation_le hle)
        (Complex.normSq_nonneg _)
    · simp [hle]
  · by_cases hle : xiGammaEulerValuationNat pe ≤ N
    · simp only [if_pos hle]
      have hrep := reporter_nonneg_of_valuation_le hle
      have hpos := Complex.normSq_nonneg
        (suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2)
      nlinarith
    · simp [hle]

/-- Total reporter-weighted wall energy splits exactly into its two completed light masses. -/
theorem suzukiUnitRieszReporterWeightedWallLightMass_eq_positive_add_negative
    (N : ℕ) (t : ℝ) :
    suzukiUnitRieszReporterWeightedWallLightMass N t =
      suzukiUnitRieszReporterWeightedPositiveLightMass N t +
        suzukiUnitRieszReporterWeightedNegativeLightMass N t := by
  rw [suzukiUnitRieszReporterWeightedWallLightMass,
    suzukiUnitRieszReporterWeightedPositiveLightMass,
    suzukiUnitRieszReporterWeightedNegativeLightMass,
    ← Summable.tsum_add (summable_reporterWeightedPositiveLight N t)
      (summable_reporterWeightedNegativeLight N t)]
  apply tsum_congr
  intro pe
  by_cases hle : xiGammaEulerValuationNat pe ≤ N
  · simp only [if_pos hle]
    ring
  · simp [hle]

/-- The finite prime outgoing charge is the sum of the two literal wall-light masses. -/
theorem unitRieszCoherentPrimeOutgoingCharge_eq_positiveLight_add_negativeLight
    {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    unitRieszCoherentPrimeOutgoingCharge N =
      suzukiUnitRieszReporterWeightedPositiveLightMass N t +
        suzukiUnitRieszReporterWeightedNegativeLightMass N t := by
  rw [← suzukiUnitRieszReporterWeightedWallLightMass_eq_positive_add_negative,
    suzukiUnitRieszReporterWeightedWallLightMass_eq_primeOutgoingCharge hN]

theorem suzukiUnitRieszReporterWeightedPositiveLightMass_nonneg
    (N : ℕ) (t : ℝ) :
    0 ≤ suzukiUnitRieszReporterWeightedPositiveLightMass N t := by
  rw [suzukiUnitRieszReporterWeightedPositiveLightMass]
  exact tsum_nonneg fun pe => by
    by_cases hle : xiGammaEulerValuationNat pe ≤ N
    · simp only [if_pos hle]
      exact mul_nonneg (reporter_nonneg_of_valuation_le hle)
        (Complex.normSq_nonneg _)
    · simp [hle]

theorem suzukiUnitRieszReporterWeightedNegativeLightMass_nonneg
    (N : ℕ) (t : ℝ) :
    0 ≤ suzukiUnitRieszReporterWeightedNegativeLightMass N t := by
  rw [suzukiUnitRieszReporterWeightedNegativeLightMass]
  exact tsum_nonneg fun pe => by
    by_cases hle : xiGammaEulerValuationNat pe ≤ N
    · simp only [if_pos hle]
      exact mul_nonneg (reporter_nonneg_of_valuation_le hle)
        (Complex.normSq_nonneg _)
    · simp [hle]

/-- At spectral center, the two light energies of every prime-power cell are equal. -/
theorem normSq_suzukiCriticalWallPositiveLightAmplitude_zero_eq_negative
    (p : Nat.Primes) (e : ℕ) :
    normSq (suzukiCriticalWallPositiveLightAmplitude 0 p e) =
      normSq (suzukiCriticalWallNegativeLightAmplitude 0 p e) := by
  rw [suzukiCriticalWallPositiveLightAmplitude,
    suzukiCriticalWallNegativeLightAmplitude]
  simp only [neg_zero]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- At spectral center, the reporter-weighted prime mass splits equally between the two light
channels. -/
theorem suzukiUnitRieszReporterWeightedPositiveLightMass_zero_eq_negative
    (N : ℕ) :
    suzukiUnitRieszReporterWeightedPositiveLightMass N 0 =
      suzukiUnitRieszReporterWeightedNegativeLightMass N 0 := by
  rw [suzukiUnitRieszReporterWeightedPositiveLightMass,
    suzukiUnitRieszReporterWeightedNegativeLightMass]
  apply tsum_congr
  intro pe
  by_cases hle : xiGammaEulerValuationNat pe ≤ N
  · simp only [if_pos hle]
    rw [normSq_suzukiCriticalWallPositiveLightAmplitude_zero_eq_negative]
  · simp [hle]

theorem suzukiUnitRieszReporterWeightedPositiveLightMass_zero_eq_prime_half
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiUnitRieszReporterWeightedPositiveLightMass N 0 =
      unitRieszCoherentPrimeOutgoingCharge N / 2 := by
  have hsum :=
    unitRieszCoherentPrimeOutgoingCharge_eq_positiveLight_add_negativeLight hN 0
  have heq := suzukiUnitRieszReporterWeightedPositiveLightMass_zero_eq_negative N
  linarith

theorem suzukiUnitRieszReporterWeightedNegativeLightMass_zero_eq_prime_half
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiUnitRieszReporterWeightedNegativeLightMass N 0 =
      unitRieszCoherentPrimeOutgoingCharge N / 2 := by
  rw [← suzukiUnitRieszReporterWeightedPositiveLightMass_zero_eq_negative]
  exact suzukiUnitRieszReporterWeightedPositiveLightMass_zero_eq_prime_half hN

/-- Each positive wall-light channel is exactly the positive sine split of its von-Mangoldt
mass.  This pointwise law exposes the phase leakage hidden by the total-light identity. -/
theorem normSq_suzukiCriticalWallPositiveLightAmplitude_eq_sine
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    normSq (suzukiCriticalWallPositiveLightAmplitude t p e) =
      (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ)) *
        (1 + Real.sin (t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) / 2 := by
  have hsum := normSq_suzukiCriticalWallLightAmplitudes_eq_vonMangoldt_div_sqrt
    t p e
  have hdiff := normSq_suzukiCriticalWallPositiveLightAmplitude_sub_negative
    t p e
  have hsquare := congrArg Complex.im
    (sq_suzukiCriticalWallField_eq_farHingeNumerator t p e)
  have him :
      ((suzukiCriticalWallField t p e) ^ 2).im =
        (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ)) *
            Real.sin (t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) := by
    rw [hsquare]
    have hkernel :
        (suzukiOscillatoryKernel (t : ℂ)
          (Real.log (xiGammaEulerValuationNat (p, e) : ℝ))).im =
            Real.sin (t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) := by
      simp only [suzukiOscillatoryKernel]
      rw [show
          (Real.log (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) * (I * (t : ℂ)) =
            ((t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ) : ℝ) : ℂ) * I by
        push_cast
        ring]
      rw [Complex.exp_mul_I]
      simp only [Complex.add_im, Complex.cos_ofReal_im, Complex.mul_im,
        Complex.sin_ofReal_re, Complex.I_im, Complex.sin_ofReal_im,
        Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    rw [Complex.mul_im, hkernel]
    norm_num
  rw [him] at hdiff
  linarith

/-- The continuum debt left after exact negative-light payment. -/
def suzukiUnitRieszLightCompletedRegularResidual
    (N : ℕ) (t : ℝ) : ℝ :=
  suzukiUnitRieszRegularWardMass (Real.log N) -
    suzukiUnitRieszReporterWeightedNegativeLightMass N t

/-- **Completed-light Ward residual law.**  Suzuki Green is positive light minus the regular-screw
residual left after exact negative-light payment. -/
theorem unitRieszSuzukiGreen_eq_positiveLight_sub_completedRegularResidual
    (N : ℕ) (t : ℝ) :
    unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) =
      suzukiUnitRieszReporterWeightedPositiveLightMass (N + 2) t -
        suzukiUnitRieszLightCompletedRegularResidual (N + 2) t := by
  rw [unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass,
    unitRieszCoherentPrimeOutgoingCharge_eq_positiveLight_add_negativeLight
      (by omega : 2 ≤ N + 2)]
  unfold suzukiUnitRieszLightCompletedRegularResidual
  ring

/-- Uniform boundedness of the explicit positive atomic--continuous Ward imbalance. -/
def SuzukiWardAtomicContinuousImbalanceBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
    |unitRieszCoherentPrimeOutgoingCharge (N + 2) -
      suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ))| ≤ B

/-- **Exact SP-E hard core.**  RH is equivalent to uniform cancellation between the finite
positive von-Mangoldt wall mass and the positive regular-screw continuum mass. -/
theorem riemannHypothesis_iff_suzukiWardAtomicContinuousImbalanceBounded :
    RiemannHypothesis ↔ SuzukiWardAtomicContinuousImbalanceBounded := by
  constructor
  · intro hRH
    obtain ⟨C, hPsi⟩ := riemannHypothesis_iff_suzukiExplicitScrewBounded.mp hRH
    have hC : 0 ≤ C :=
      (abs_nonneg (suzukiPsi 0)).trans (hPsi 0 (le_refl 0))
    let B : ℝ := 4 * C +
      2 * |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase|
    refine ⟨B, by dsimp only [B]; positivity, ?_⟩
    intro N
    rw [← unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass]
    exact abs_unitRieszSuzukiGreen_le_of_suzuki_bound hC hPsi
      ((unitRieszSuzukiBase_lt_log_of_two_le (by omega : 2 ≤ N + 2)).le)
  · rintro ⟨B, hB, himbalance⟩
    apply riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded.mpr
    let Q : ℝ := B + unitRieszSuzukiPolarUniformBound +
      unitRieszSuzukiArchUniformBound
    let B₀ : ℝ := 2 * Q
    have hPolar0 : 0 ≤ unitRieszSuzukiPolarUniformBound := by
      unfold unitRieszSuzukiPolarUniformBound
      positivity
    have hArch0 : 0 ≤ unitRieszSuzukiArchUniformBound := by
      unfold unitRieszSuzukiArchUniformBound
      exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        unitRieszSuzukiArchDenominator_pos.le
    have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
    refine ⟨B₀, by dsimp only [B₀]; positivity, ?_⟩
    intro M hM
    obtain ⟨N, rfl⟩ : ∃ N : ℕ, M = N + 2 := ⟨M - 2, by omega⟩
    have hH : unitRieszSuzukiBase ≤ Real.log ((N + 2 : ℕ) : ℝ) :=
      (unitRieszSuzukiBase_lt_log_of_two_le (by omega : 2 ≤ N + 2)).le
    have hGreen :
        |unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ))| ≤ B := by
      rw [unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass]
      exact himbalance N
    have hPolar := abs_unitRieszSuzukiPolarCorrection_le hH
    have hArch := abs_unitRieszSuzukiArchCorrection_le hH
    have hout := unitRieszSuzuki_outgoing_eq_green (by omega : 2 ≤ N + 2)
    have hcharge : |unitRieszCoherentCompletedOutgoingCharge (N + 2)| ≤ Q := by
      rw [hout]
      calc
        |unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) +
            unitRieszSuzukiPolarCorrection (Real.log ((N + 2 : ℕ) : ℝ)) -
            unitRieszSuzukiArchCorrection (Real.log ((N + 2 : ℕ) : ℝ))| ≤
            |unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ))| +
              |unitRieszSuzukiPolarCorrection (Real.log ((N + 2 : ℕ) : ℝ))| +
              |unitRieszSuzukiArchCorrection (Real.log ((N + 2 : ℕ) : ℝ))| := by
                have hsub := abs_sub
                  (unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) +
                    unitRieszSuzukiPolarCorrection (Real.log ((N + 2 : ℕ) : ℝ)))
                  (unitRieszSuzukiArchCorrection (Real.log ((N + 2 : ℕ) : ℝ)))
                have hadd := abs_add_le
                  (unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)))
                  (unitRieszSuzukiPolarCorrection (Real.log ((N + 2 : ℕ) : ℝ)))
                linarith
        _ ≤ Q := by dsimp only [Q]; linarith
    have hhalf := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half
      (by omega : 2 ≤ N + 2)
    have hres :
        criticalMellinChebyshevResolventSource (Real.log ((N + 2 : ℕ) : ℝ)) =
          2 * unitRieszCoherentCompletedOutgoingCharge (N + 2) := by
      linarith
    rw [hres, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hcharge (by norm_num)

end

end GaloisForLFunctions.RHTower
