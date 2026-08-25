import GaloisForLFunctions.RHTower.RouteRPrimeGammaExchangeableFormationWork
import GaloisForLFunctions.HTGeometry.PoissonSuperpositionSaturationProperness
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Route R Gamma defect as hidden formation history

Boolean occupancy saturates under independent Poisson superposition, so its
visible information vanishes.  The exact Poisson information chain rule moves
the surviving reflected Gamma defect into vertical formation history instead.

This file proves a cross-route bridge, not an RH producer: visible completion
can erase the defect while normalized hidden-history action retains exactly the
same zero radical as the physical Gamma Bockstein.  At an Xi divisor, vanishing
of this retained density is equivalent to critical-line placement.
-/

namespace RHTower

noncomputable section

open Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped NNReal

/-- Positive Poisson rate obtained from the forward physical Gamma orientation. -/
def routeRPrimeGammaForwardPoissonRate (t : ℝ) (p : Nat.Primes) : ℝ≥0 :=
  ⟨Real.exp (routeRPrimeGammaForwardFormationLaw t p 0),
    (Real.exp_pos _).le⟩

/-- Positive Poisson rate obtained from the reflected physical Gamma orientation. -/
def routeRPrimeGammaReflectedPoissonRate (t : ℝ) (p : Nat.Primes) : ℝ≥0 :=
  ⟨Real.exp (routeRPrimeGammaReflectedFormationLaw t p 0),
    (Real.exp_pos _).le⟩

theorem routeRPrimeGammaForwardPoissonRate_pos (t : ℝ) (p : Nat.Primes) :
    0 < routeRPrimeGammaForwardPoissonRate t p := by
  exact_mod_cast Real.exp_pos (routeRPrimeGammaForwardFormationLaw t p 0)

theorem routeRPrimeGammaReflectedPoissonRate_pos (t : ℝ) (p : Nat.Primes) :
    0 < routeRPrimeGammaReflectedPoissonRate t p := by
  exact_mod_cast Real.exp_pos (routeRPrimeGammaReflectedFormationLaw t p 0)

/-- Exponentiation retains the full reflected Gamma formation defect. -/
theorem routeRPrimeGammaPoissonRates_eq_iff (t : ℝ) (p : Nat.Primes) :
    routeRPrimeGammaForwardPoissonRate t p =
        routeRPrimeGammaReflectedPoissonRate t p ↔
      t = 0 := by
  constructor
  · intro hrate
    have hcoordinate :
        routeRPrimeGammaForwardFormationLaw t p 0 =
          routeRPrimeGammaReflectedFormationLaw t p 0 := by
      apply Real.exp_injective
      exact congrArg ((↑) : ℝ≥0 → ℝ) hrate
    apply (routeRPrimeGamma_threeSlotExchangeable_iff t p).mp
    rw [threeSlotExchangeable_iff]
    funext i
    fin_cases i
    exact hcoordinate
  · rintro rfl
    simp [routeRPrimeGammaForwardPoissonRate,
      routeRPrimeGammaReflectedPoissonRate,
      routeRPrimeGammaForwardFormationLaw,
      routeRPrimeGammaReflectedFormationLaw]

/-- Asymptotic density retained in formation history after occupancy saturation. -/
def routeRPrimeGammaPoissonHiddenHistoryDensity (t : ℝ) (p : Nat.Primes) : ℝ :=
  rateJeffreys (routeRPrimeGammaForwardPoissonRate t p)
    (routeRPrimeGammaReflectedPoissonRate t p)

/-- At every finite depth, total reflected information splits into visible occupancy and hidden
formation history. -/
theorem routeRPrimeGammaPoissonFormationConservation
    (t : ℝ) (p : Nat.Primes) {m : ℕ} (hm : 0 < m) :
    (m : ℝ) * routeRPrimeGammaPoissonHiddenHistoryDensity t p =
      formationBooleanWork
          (routeRPrimeGammaForwardPoissonRate t p)
          (routeRPrimeGammaReflectedPoissonRate t p) m +
        formationHistoryWork
          (routeRPrimeGammaForwardPoissonRate t p)
          (routeRPrimeGammaReflectedPoissonRate t p) m := by
  exact formation_conservation
    (routeRPrimeGammaForwardPoissonRate_pos t p)
    (routeRPrimeGammaReflectedPoissonRate_pos t p) hm

theorem routeRPrimeGammaPoissonHiddenHistoryDensity_eq_zero_iff
    (t : ℝ) (p : Nat.Primes) :
    routeRPrimeGammaPoissonHiddenHistoryDensity t p = 0 ↔ t = 0 := by
  rw [routeRPrimeGammaPoissonHiddenHistoryDensity,
    rateJeffreys_eq_zero_iff
      (routeRPrimeGammaForwardPoissonRate_pos t p)
      (routeRPrimeGammaReflectedPoissonRate_pos t p),
    routeRPrimeGammaPoissonRates_eq_iff]

theorem routeRPrimeGammaPoissonHiddenHistoryDensity_pos_iff
    (t : ℝ) (p : Nat.Primes) :
    0 < routeRPrimeGammaPoissonHiddenHistoryDensity t p ↔ t ≠ 0 := by
  constructor
  · intro hpos ht
    subst t
    exact hpos.ne' ((routeRPrimeGammaPoissonHiddenHistoryDensity_eq_zero_iff 0 p).2 rfl)
  · intro ht
    apply rateJeffreys_pos_of_ne
      (routeRPrimeGammaForwardPoissonRate_pos t p)
      (routeRPrimeGammaReflectedPoissonRate_pos t p)
    exact mt (routeRPrimeGammaPoissonRates_eq_iff t p).mp ht

/-- Visible occupancy loses every reflected Gamma defect at cofinal formation depth. -/
theorem tendsto_routeRPrimeGammaPoissonBooleanWork_zero
    (t : ℝ) (p : Nat.Primes) :
    Tendsto (fun m : ℕ => formationBooleanWork
      (routeRPrimeGammaForwardPoissonRate t p)
      (routeRPrimeGammaReflectedPoissonRate t p) m) atTop (nhds 0) := by
  exact tendsto_formationBooleanWork_zero
    (routeRPrimeGammaForwardPoissonRate_pos t p)
    (routeRPrimeGammaReflectedPoissonRate_pos t p)

/-- Normalized hidden-history action retains the complete reflected Gamma defect density. -/
theorem tendsto_routeRPrimeGammaPoissonHistoryWork_div
    (t : ℝ) (p : Nat.Primes) :
    Tendsto (fun m : ℕ => formationHistoryWork
      (routeRPrimeGammaForwardPoissonRate t p)
      (routeRPrimeGammaReflectedPoissonRate t p) m / (m : ℝ)) atTop
      (nhds (routeRPrimeGammaPoissonHiddenHistoryDensity t p)) := by
  exact tendsto_formationHistoryWork_div
    (routeRPrimeGammaForwardPoissonRate_pos t p)
    (routeRPrimeGammaReflectedPoissonRate_pos t p)

/-- Limiting hidden-history density and physical Bockstein have the same zero radical. -/
theorem routeRPrimeGammaPoissonHiddenHistoryDensity_eq_zero_iff_bockstein
    (t : ℝ) (p : Nat.Primes) :
    routeRPrimeGammaPoissonHiddenHistoryDensity t p = 0 ↔
      primeGammaCofinalBocksteinCoefficient t p = 0 := by
  rw [routeRPrimeGammaPoissonHiddenHistoryDensity_eq_zero_iff,
    primeGammaCofinalBocksteinCoefficient_eq_zero_iff]

/-- Xi specialization of the retained horizontal history density. -/
def routeRPrimeGammaXiPoissonHiddenHistoryDensity
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  routeRPrimeGammaPoissonHiddenHistoryDensity ((rho : ℂ).re - 1 / 2) p

/-- At an Xi divisor, hidden-history neutrality is exactly critical-line placement. -/
theorem routeRPrimeGammaXiPoissonHiddenHistoryDensity_eq_zero_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    routeRPrimeGammaXiPoissonHiddenHistoryDensity rho p = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [routeRPrimeGammaXiPoissonHiddenHistoryDensity,
    routeRPrimeGammaPoissonHiddenHistoryDensity_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-- An off-line Xi divisor retains strictly positive hidden-history density. -/
theorem routeRPrimeGammaXiPoissonHiddenHistoryDensity_pos_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    0 < routeRPrimeGammaXiPoissonHiddenHistoryDensity rho p ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  rw [routeRPrimeGammaXiPoissonHiddenHistoryDensity,
    routeRPrimeGammaPoissonHiddenHistoryDensity_pos_iff]
  constructor <;> intro h
  · intro hline
    apply h
    linarith
  · intro hzero
    apply h
    linarith

/-- Every Xi divisor has zero retained history density at one ordinary prime. -/
def RouteRPrimeGammaXiPoissonHistoryNeutral (p : Nat.Primes) : Prop :=
  ∀ rho : XiDivisorSupport,
    routeRPrimeGammaXiPoissonHiddenHistoryDensity rho p = 0

/-- Global history neutrality is exactly RH; visible occupancy saturation alone is unconditional. -/
theorem routeRPrimeGammaXiPoissonHistoryNeutral_iff_riemannHypothesis
    (p : Nat.Primes) :
    RouteRPrimeGammaXiPoissonHistoryNeutral p ↔ RiemannHypothesis := by
  constructor
  · intro hneutral
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hzero
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    exact (routeRPrimeGammaXiPoissonHiddenHistoryDensity_eq_zero_iff support p).mp
      (hneutral support)
  · intro hRH rho
    apply (routeRPrimeGammaXiPoissonHiddenHistoryDensity_eq_zero_iff rho p).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH rho

end

end RHTower
