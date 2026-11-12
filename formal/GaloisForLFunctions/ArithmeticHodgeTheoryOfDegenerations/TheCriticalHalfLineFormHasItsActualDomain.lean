import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateHasZeroFullEnergy
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePrimeFormIsQuadraticOnTheWeightedDomain
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFullGammaFormIsQuadraticOnItsIntegrableDomain
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UnrestrictedAtomicGardingFailsAndCollarGardingHolds

/-!
# The actual finite-energy half-line domain

The critical state supplies every domain condition from its defining bounds.
Scalar normalization then extends endpoint nonnegativity to all finite-energy
half-line profiles, with no unit-norm restriction.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis WindowTowerOfSpecZ

/-- Measurable half-line profiles with finite physical and full Gamma energies. -/
structure CriticalHalfLineEnergyDomain (F : ℝ → ℝ) : Prop where
  meas : Measurable F
  integrable : Integrable F
  sq : Integrable (fun u => F u ^ 2)
  exponential : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))
  support : ∀ u, 0 ≤ u → F u = 0
  gamma : Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r)

/-- The actual critical state lies in the full domain, including Gamma integrability. -/
theorem criticalHalfLineEnergyDomain_of_groundState {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) : CriticalHalfLineEnergyDomain F :=
  ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.1,
    integrable_gamma_of_criticalHalfLineGroundState hF⟩

/-- The physical data give the weighted prime-series domain. -/
theorem CriticalHalfLineEnergyDomain.weighted {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : WeightedTwo F :=
  (exponentialSourceMass_le_of_support (Y := 0) le_rfl hF.integrable.aestronglyMeasurable
    hF.sq hF.exponential (Eventually.of_forall fun u hu => hF.support u hu.le)).1

theorem CriticalHalfLineEnergyDomain.const_mul {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (c : ℝ) :
    CriticalHalfLineEnergyDomain (fun u => c * F u) := by
  refine ⟨measurable_const.mul hF.meas, hF.integrable.const_mul c, ?_, ?_, ?_,
    integrable_gamma_const_mul hF.gamma c⟩
  · apply (hF.sq.const_mul (c ^ 2)).congr
    exact Eventually.of_forall fun u => by dsimp only; ring
  · apply (hF.exponential.const_mul (c ^ 2)).congr
    exact Eventually.of_forall fun u => by dsimp only; ring
  · intro u hu
    rw [hF.support u hu, mul_zero]

/-- Every term of the literal full energy has the same quadratic scaling. -/
theorem criticalHalfLineFullEnergy_const_mul (R : ℝ) (F : ℝ → ℝ) (c : ℝ) :
    criticalHalfLineFullEnergy R (fun u => c * F u) = c ^ 2 * criticalHalfLineFullEnergy R F := by
  have he : (∫ u in Iio 0, (c * F u) ^ 2 * Real.exp (-(8 * u))) =
      c ^ 2 * ∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u)) := by
    simp_rw [mul_pow, mul_assoc]
    exact integral_const_mul _ _
  unfold criticalHalfLineFullEnergy
  rw [archForm_const_mul_unrestricted, primeSum_const_mul, coshHalfMoment_const_mul,
    sinhHalfMoment_const_mul, he]
  ring

/-- Endpoint nonnegativity holds on the whole actual finite-energy domain. -/
theorem criticalHalfLineFullEnergy_nonneg_on_domain
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    (hpolar : polarPaymentCriticalThreshold = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    0 ≤ criticalHalfLineFullEnergy W₀ F := by
  let m : ℝ := ∫ u, F u ^ 2
  let c : ℝ := 1 / (Real.sqrt m + 1)
  have hm : 0 ≤ m := integral_nonneg fun u => sq_nonneg _
  have hc : 0 < c := by dsimp only [c]; positivity
  have hs : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have hcEq : c * (Real.sqrt m + 1) = 1 := by
    dsimp only [c]
    field_simp
  have hcs0 : 0 ≤ c * Real.sqrt m := mul_nonneg hc.le hs
  have hcs1 : c * Real.sqrt m ≤ 1 := by nlinarith only [hc.le, hcEq]
  have hnorm : (∫ u, (c * F u) ^ 2) ≤ 1 := by
    calc
      _ = c ^ 2 * m := by simp_rw [mul_pow]; exact integral_const_mul _ _
      _ = (c * Real.sqrt m) ^ 2 := by rw [mul_pow, Real.sq_sqrt hm]
      _ ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hcs0 hcs1 2
  have hd := hF.const_mul c
  have hp := criticalHalfLineFullEnergy_nonneg_of_threshold_equality hW hthreshold hpolar
    hd.meas hd.integrable hd.sq hnorm hd.exponential hd.support hd.gamma
  rw [criticalHalfLineFullEnergy_const_mul] at hp
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hc)).mp hp

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
