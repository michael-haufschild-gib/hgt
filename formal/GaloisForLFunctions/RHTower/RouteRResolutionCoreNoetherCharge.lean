import GaloisForLFunctions.RHTower.RouteRResolutionCoreDefect
import GaloisForLFunctions.RHTower.XiSourceBoundaryOrientationConservation
import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# Resolution cores are conserved source--boundary orientation charge

The Route R resolution core is not an observer-chosen size.  This file identifies it with the
absolute transverse rate of the canonical Riemann source and with the multiplicity-normalized
Noether orientation charge already conserved across three presentations:

* rational nearby-cycle outer charge;
* completed Xi logarithmic-current residue;
* reflected prime-tail source entropy.

For an Xi support point `rho` of multiplicity `m`,

`|orientation charge| = (m / 2) * resolution core radius`.

Hence an off-line zero is exactly a charged completion defect with positive resolution core.
Global absence of this charge is equivalent to RH.
-/

open Complex Filter Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Multiplicity-weighted real Noether orientation charge of one Xi completion defect. -/
def routeRPrimeGammaXiNoetherOrientationCharge
    (rho : XiDivisorSupport) : ℝ :=
  (-(((rho : ℂ) - 1 / 2) *
    ((analyticOrderAt xi (rho : ℂ)).toNat : ℂ))).re

/-- Canonical source transverse rate is exactly centered horizontal grade. -/
theorem sourceCayleyTransverseRate_one_eq_centeredGrade (rho : ℂ) :
    sourceCayleyTransverseRate 1 rho = 2 * rho.re - 1 := by
  simp only [sourceCayleyTransverseRate, sub_re, one_re]
  ring

/-- The completion resolution core is the absolute canonical source transverse rate. -/
theorem routeRPrimeGammaXiResolutionCoreRadius_eq_abs_sourceCayleyTransverseRate
    (rho : XiDivisorSupport) :
    routeRPrimeGammaXiResolutionCoreRadius rho =
      |sourceCayleyTransverseRate 1 (rho : ℂ)| := by
  rw [routeRPrimeGammaXiResolutionCoreRadius,
    sourceCayleyTransverseRate_one_eq_centeredGrade]

/-- Exact charge/core calibration: multiplicity counts identical charged defect copies, while the
resolution core is the charge per copy in the canonical source clock. -/
theorem abs_routeRPrimeGammaXiNoetherOrientationCharge_eq
    (rho : XiDivisorSupport) :
    |routeRPrimeGammaXiNoetherOrientationCharge rho| =
      ((analyticOrderAt xi (rho : ℂ)).toNat : ℝ) / 2 *
        routeRPrimeGammaXiResolutionCoreRadius rho := by
  rw [routeRPrimeGammaXiNoetherOrientationCharge,
    centeredDivisorCharge_real_eq_neg_half_sourceCayleyRate,
    routeRPrimeGammaXiResolutionCoreRadius_eq_abs_sourceCayleyTransverseRate]
  rw [abs_mul, abs_div, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Conserved orientation charge vanishes exactly when the resolution core vanishes. -/
theorem routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_coreRadius_eq_zero
    (rho : XiDivisorSupport) :
    routeRPrimeGammaXiNoetherOrientationCharge rho = 0 ↔
      routeRPrimeGammaXiResolutionCoreRadius rho = 0 := by
  let m := (analyticOrderAt xi (rho : ℂ)).toNat
  have hmne : m ≠ 0 :=
    xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support rho)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hmne
  have hcal := abs_routeRPrimeGammaXiNoetherOrientationCharge_eq rho
  change |routeRPrimeGammaXiNoetherOrientationCharge rho| =
      (m : ℝ) / 2 * routeRPrimeGammaXiResolutionCoreRadius rho at hcal
  constructor
  · intro hcharge
    rw [hcharge, abs_zero] at hcal
    have hcoreNonneg : 0 ≤ routeRPrimeGammaXiResolutionCoreRadius rho := abs_nonneg _
    nlinarith
  · intro hcore
    rw [hcore, mul_zero] at hcal
    exact abs_eq_zero.mp hcal

/-- One physical Noether charge vanishes exactly on the critical line. -/
theorem routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_re_eq_half
    (rho : XiDivisorSupport) :
    routeRPrimeGammaXiNoetherOrientationCharge rho = 0 ↔
      (rho : ℂ).re = 1 / 2 :=
  (routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_coreRadius_eq_zero rho).trans
    (routeRPrimeGammaXiResolutionCoreRadius_eq_zero_iff rho)

/-- Nearby cycle, completed divisor current, reflected source tail, and completion core carry one
multiplicity-calibrated conserved charge. -/
theorem routeRPrimeGammaXiResolutionCore_noetherConservation
    (rho : XiDivisorSupport) :
    let m := (analyticOrderAt xi (rho : ℂ)).toNat
    Tendsto
        (fun w : ℂ =>
          w⁻¹ * (depthSuccessorNearbyCycle ((rho : ℂ) - 1 / 2) m w⁻¹ - 1))
        (𝓝[≠] 0)
        (𝓝 (-(((rho : ℂ) - 1 / 2) * (m : ℂ)))) ∧
      Tendsto
        (fun s : ℂ => (s - (rho : ℂ)) * xiExceptionalAffineDivisorCurrent s)
        (𝓝[≠] (rho : ℂ))
        (𝓝 (-(((rho : ℂ) - 1 / 2) * (m : ℂ)))) ∧
      |routeRPrimeGammaXiNoetherOrientationCharge rho| =
        (m : ℝ) / 2 * routeRPrimeGammaXiResolutionCoreRadius rho := by
  dsimp only
  exact ⟨(xiDepthNearby_sourceBoundaryOrientationConservation (rho : ℂ)).1,
    (xiDepthNearby_sourceBoundaryOrientationConservation (rho : ℂ)).2.1,
    abs_routeRPrimeGammaXiNoetherOrientationCharge_eq rho⟩

/-- Every physical completion defect has zero conserved orientation charge. -/
def RouteRPrimeGammaXiGlobalNoetherOrientationChargeFree : Prop :=
  ∀ rho : XiDivisorSupport,
    routeRPrimeGammaXiNoetherOrientationCharge rho = 0

/-- RH is global charge-free cofinal completion. -/
theorem routeRPrimeGammaXiGlobalNoetherOrientationChargeFree_iff_riemannHypothesis :
    RouteRPrimeGammaXiGlobalNoetherOrientationChargeFree ↔ RiemannHypothesis := by
  rw [← routeRPrimeGammaXiGloballyCofinallyExact_iff_riemannHypothesis]
  constructor
  · intro h rho
    exact (routeRPrimeGammaXiCofinallyExact_iff_re_eq_half rho).2
      ((routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_re_eq_half rho).1 (h rho))
  · intro h rho
    exact (routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_re_eq_half rho).2
      ((routeRPrimeGammaXiCofinallyExact_iff_re_eq_half rho).1 (h rho))

end

end RHTower
