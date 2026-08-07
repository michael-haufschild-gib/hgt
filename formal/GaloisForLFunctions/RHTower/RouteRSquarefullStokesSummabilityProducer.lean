import GaloisForLFunctions.RHTower.RouteRSquarefullTailGammaCartierIndex

/-!
# Route R squarefull Stokes summability producer

The level-two Euler activation boundary has an explicit primewise coefficient:
the local squarefull mass in one Gamma orientation minus the local squarefull
mass in the reflected orientation.  This file proves that the coefficient is
summable exactly on the balanced squarefull-tail locus.

This changes the remaining Route R producer burden from equality of two
singular tail probabilities to normality of one explicit diagonal boundary.
It does not prove that boundary summable at Xi divisor points; that remains the
independent pre-divisor rational-adelic/Euler--Gamma source theorem.
-/

open MeasureTheory ProbabilityTheory Set
open GaloisForLFunctions.HTGeometry
open scoped ENNReal

namespace RHTower

noncomputable section

/-! ## Local level-two boundary -/

/-- Real local mass of valuation depth at least two in the Euler activation
law at exponent `σ`. -/
def routeREulerSquarefullLocalMass (σ : ℝ) (p : Nat.Primes) : ℝ :=
  ((p : ℝ) ^ (-σ)) ^ 2 / (1 + (p : ℝ) ^ (-σ))

/-- The local coefficient is not a surrogate: it is exactly the real value of
the one-prime activation measure on the level-two event. -/
theorem diagonalActivationMeasure_squarefull_toReal_eq_localMass
    {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    (diagonalActivationMeasure (eulerActivationParameter hσ.le p)
        {k : ℕ | 2 ≤ k}).toReal =
      routeREulerSquarefullLocalMass σ p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.2.one_lt
  have hparam :
      ((eulerActivationParameter hσ.le p : unitInterval) : ℝ) ≠ 1 := by
    rw [eulerActivationParameter_coe]
    exact ne_of_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
  have hlocal :=
    diagonalActivationMeasure_Ici_succ
      (eulerActivationParameter hσ.le p) hparam 1
  norm_num at hlocal
  rw [eulerActivationParameter_coe] at hlocal
  rw [hlocal, ENNReal.toReal_ofReal]
  · rfl
  · positivity

/-- The local squarefull masses are summable precisely above the level-two
abscissa. -/
theorem summable_routeREulerSquarefullLocalMass_iff
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (routeREulerSquarefullLocalMass σ) ↔ 1 / 2 < σ := by
  have hlevel :=
    summable_diagonalActivationLevel_iff hσ (m := 2) (by norm_num)
  change
    Summable (fun p : Nat.Primes =>
      ((p : ℝ) ^ (-σ)) ^ 2 / (1 + (p : ℝ) ^ (-σ))) ↔
        1 / 2 < σ
  constructor
  · intro hsum
    have hgt := hlevel.mp hsum
    norm_num at hgt
    linarith
  · intro hhalf
    apply hlevel.mpr
    norm_num
    linarith

/-- Primewise Stokes boundary of the reflected level-two Euler activation
faces. -/
def routeREulerGammaSquarefullStokesCoefficient
    (σ : ℝ) (p : Nat.Primes) : ℝ :=
  routeREulerSquarefullLocalMass σ p -
    routeREulerSquarefullLocalMass (1 - σ) p

/-- Reflection reverses the orientation of the squarefull Stokes boundary. -/
theorem routeREulerGammaSquarefullStokesCoefficient_reflection
    (σ : ℝ) (p : Nat.Primes) :
    routeREulerGammaSquarefullStokesCoefficient (1 - σ) p =
      -routeREulerGammaSquarefullStokesCoefficient σ p := by
  change
    routeREulerSquarefullLocalMass (1 - σ) p -
        routeREulerSquarefullLocalMass (1 - (1 - σ)) p =
      -(routeREulerSquarefullLocalMass σ p -
        routeREulerSquarefullLocalMass (1 - σ) p)
  rw [show 1 - (1 - σ) = σ by ring]
  ring

/-- **Squarefull Stokes normality law.** In the open strip, the explicit
reflected local boundary is summable exactly at the central exponent. -/
theorem summable_routeREulerGammaSquarefullStokesCoefficient_iff
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    Summable (routeREulerGammaSquarefullStokesCoefficient σ) ↔
      σ = 1 / 2 := by
  have href : 0 < 1 - σ := sub_pos.mpr hσ1
  constructor
  · intro hboundary
    rcases lt_trichotomy σ (1 / 2) with hlt | heq | hgt
    · have hleftNot :
          ¬ Summable (routeREulerSquarefullLocalMass σ) := by
        rw [summable_routeREulerSquarefullLocalMass_iff hσ]
        linarith
      have hright :
          Summable (routeREulerSquarefullLocalMass (1 - σ)) :=
        (summable_routeREulerSquarefullLocalMass_iff href).2 (by linarith)
      apply (hleftNot ?_).elim
      have hadd := hboundary.add hright
      simpa only [routeREulerGammaSquarefullStokesCoefficient,
        sub_add_cancel] using hadd
    · exact heq
    · have hleft :
          Summable (routeREulerSquarefullLocalMass σ) :=
        (summable_routeREulerSquarefullLocalMass_iff hσ).2 hgt
      have hrightNot :
          ¬ Summable (routeREulerSquarefullLocalMass (1 - σ)) := by
        rw [summable_routeREulerSquarefullLocalMass_iff href]
        linarith
      apply (hrightNot ?_).elim
      have hsub := hleft.sub hboundary
      have hfun :
          (fun p : Nat.Primes =>
            routeREulerSquarefullLocalMass σ p -
              (routeREulerSquarefullLocalMass σ p -
                routeREulerSquarefullLocalMass (1 - σ) p)) =
            routeREulerSquarefullLocalMass (1 - σ) := by
        funext p
        ring
      rw [show routeREulerGammaSquarefullStokesCoefficient σ =
          fun p : Nat.Primes =>
            routeREulerSquarefullLocalMass σ p -
              routeREulerSquarefullLocalMass (1 - σ) p by rfl,
        hfun] at hsub
      exact hsub
  · rintro rfl
    have hzero :
        routeREulerGammaSquarefullStokesCoefficient (1 / 2) =
          fun _ : Nat.Primes => (0 : ℝ) := by
      funext p
      rw [routeREulerGammaSquarefullStokesCoefficient]
      norm_num
    rw [hzero]
    exact summable_zero

/-! ## Xi specialization and Route R endpoint bridge -/

/-- Explicit level-two diagonal Stokes coefficient at an Xi divisor point. -/
def routeREulerGammaSquarefullStokesCoefficientAtXi
    (rho : XiDivisorSupport) : Nat.Primes → ℝ :=
  routeREulerGammaSquarefullStokesCoefficient (rho : ℂ).re

/-- Normality of the explicit level-two diagonal boundary. -/
def RouteREulerGammaSquarefullStokesSummable
    (rho : XiDivisorSupport) : Prop :=
  Summable (routeREulerGammaSquarefullStokesCoefficientAtXi rho)

theorem routeREulerGammaSquarefullStokesSummable_iff_re_eq_half
    (rho : XiDivisorSupport) :
    RouteREulerGammaSquarefullStokesSummable rho ↔
      (rho : ℂ).re = 1 / 2 := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  exact summable_routeREulerGammaSquarefullStokesCoefficient_iff
    hstrip.1 hstrip.2

/-- Normality of the explicit diagonal Stokes boundary is exactly equality on
the squarefull-tail projection. -/
theorem routeREulerGammaSquarefullStokesSummable_iff_tailBalanced
    (rho : XiDivisorSupport) :
    RouteREulerGammaSquarefullStokesSummable rho ↔
      RouteREulerGammaSquarefullTailBalanced rho := by
  exact (routeREulerGammaSquarefullStokesSummable_iff_re_eq_half rho).trans
    (routeREulerGammaSquarefullTailBalanced_iff_re_eq_half rho).symm

/-- Coefficient-faithful comparison with the Route R Gamma--Cartier port. -/
theorem routeREulerGammaSquarefullStokesSummable_iff_port_eq_zero
    (rho : XiDivisorSupport) :
    RouteREulerGammaSquarefullStokesSummable rho ↔
      routeRTwoThreeGammaCartierTransportPort rho = 0 := by
  exact (routeREulerGammaSquarefullStokesSummable_iff_tailBalanced rho).trans
    (routeREulerGammaSquarefullTailBalanced_iff_port_eq_zero rho)

/-- Pointwise arithmetic-horizon globalization is now reduced to summability
of one explicit primewise source boundary. -/
theorem routeRTwoThreeGammaArithmeticCorona_global_eq_local_iff_squarefullStokesSummable
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaArithmeticSingularCoronaPhysicalLift rho) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho
            (routeRTwoThreeGammaArithmeticPacketPhysicalLift rho)) ↔
      RouteREulerGammaSquarefullStokesSummable rho := by
  exact
    (routeRTwoThreeGammaArithmeticCorona_global_eq_local_iff_squarefullTailBalanced rho).trans
      (routeREulerGammaSquarefullStokesSummable_iff_tailBalanced rho).symm

/-- Global arithmetic-horizon globalization is equivalent to normality of
the explicit diagonal squarefull Stokes boundary at every Xi divisor point. -/
theorem routeRTwoThreeGammaArithmeticCorona_globalization_iff_squarefullStokesSummable :
    (∀ rho : XiDivisorSupport,
      routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaArithmeticSingularCoronaPhysicalLift rho) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho
            (routeRTwoThreeGammaArithmeticPacketPhysicalLift rho))) ↔
      ∀ rho : XiDivisorSupport,
        RouteREulerGammaSquarefullStokesSummable rho := by
  exact forall_congr' fun rho =>
    routeRTwoThreeGammaArithmeticCorona_global_eq_local_iff_squarefullStokesSummable rho

end

end RHTower
