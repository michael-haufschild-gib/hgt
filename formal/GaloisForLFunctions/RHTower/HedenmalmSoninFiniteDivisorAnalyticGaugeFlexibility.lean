import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import GaloisForLFunctions.RHTower.HedenmalmSoninCartanGammaSixMassShell

/-!
# Finite-divisor analytic gauge flexibility

The discrete-divisor escape from the Sonin scalar cusp no-go has no finite-level rigidity.
Every finite subset of the literal Xi divisor admits an entire polynomial gauge with exactly the
prescribed two-sided escape-cancelling modulus.  More strongly, arbitrary complex values on every
finite Xi-support packet admit an entire interpolant.

Consequently no finite family of discrete analytic-gauge conditions can force the critical wall.
Any viable discrete survivor must impose genuinely cofinal compatibility, such as one uniform
growth/type budget independent of the finite packet.
-/

open Complex Real Set

noncomputable section

namespace RHTower

def xiFiniteSoninCancellingGaugePolynomial
    (S : Finset XiDivisorSupport) (c : ℝ) : Polynomial ℂ :=
  Lagrange.interpolate S xiSpectralPointSupport
    (fun rho => (soninEscapeCancellingGaugeModulus c
      (xiSpectralPointSupport rho).im : ℂ))

theorem analyticOnNhd_xiFiniteSoninCancellingGaugePolynomial
    (S : Finset XiDivisorSupport) (c : ℝ) :
    AnalyticOnNhd ℂ
      (fun z => (xiFiniteSoninCancellingGaugePolynomial S c).eval z)
      Set.univ := by
  exact AnalyticOnNhd.eval_polynomial _

theorem degree_xiFiniteSoninCancellingGaugePolynomial_lt
    (S : Finset XiDivisorSupport) (c : ℝ) :
    (xiFiniteSoninCancellingGaugePolynomial S c).degree < S.card := by
  exact Lagrange.degree_interpolate_lt _
    xiSpectralPointSupport_injective.injOn

theorem xiFiniteSoninCancellingGaugePolynomial_eval
    {S : Finset XiDivisorSupport} {c : ℝ}
    {rho : XiDivisorSupport} (hrho : rho ∈ S) :
    (xiFiniteSoninCancellingGaugePolynomial S c).eval
        (xiSpectralPointSupport rho) =
      (soninEscapeCancellingGaugeModulus c
        (xiSpectralPointSupport rho).im : ℂ) := by
  exact Lagrange.eval_interpolate_at_node _
    xiSpectralPointSupport_injective.injOn hrho

theorem norm_xiFiniteSoninCancellingGaugePolynomial_eval
    {S : Finset XiDivisorSupport} {c : ℝ}
    {rho : XiDivisorSupport} (hrho : rho ∈ S) :
    ‖(xiFiniteSoninCancellingGaugePolynomial S c).eval
        (xiSpectralPointSupport rho)‖ =
      soninEscapeCancellingGaugeModulus c
        (xiSpectralPointSupport rho).im := by
  rw [xiFiniteSoninCancellingGaugePolynomial_eval hrho]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  exact Real.exp_pos _

theorem xiFiniteSoninCancellingGaugePolynomial_eval_ne_zero
    {S : Finset XiDivisorSupport} {c : ℝ}
    {rho : XiDivisorSupport} (hrho : rho ∈ S) :
    (xiFiniteSoninCancellingGaugePolynomial S c).eval
        (xiSpectralPointSupport rho) ≠ 0 := by
  rw [xiFiniteSoninCancellingGaugePolynomial_eval hrho]
  exact_mod_cast (Real.exp_ne_zero _)

theorem exists_entire_exact_sonin_cancelling_gauge_on_finite_xi_support
    (S : Finset XiDivisorSupport) (c : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g Set.univ ∧
      ∀ rho ∈ S,
        ‖g (xiSpectralPointSupport rho)‖ =
          soninEscapeCancellingGaugeModulus c
            (xiSpectralPointSupport rho).im ∧
        g (xiSpectralPointSupport rho) ≠ 0 := by
  refine ⟨fun z => (xiFiniteSoninCancellingGaugePolynomial S c).eval z,
    analyticOnNhd_xiFiniteSoninCancellingGaugePolynomial S c, ?_⟩
  intro rho hrho
  exact ⟨norm_xiFiniteSoninCancellingGaugePolynomial_eval hrho,
    xiFiniteSoninCancellingGaugePolynomial_eval_ne_zero hrho⟩

theorem exists_entire_exact_geometric_sonin_cancelling_gauge_on_finite_xi_support
    (S : Finset XiDivisorSupport) {r : ℝ} {N : ℕ}
    (hr : 1 < r) (hN : 0 < N) :
    0 < (N : ℝ) * Real.log r ∧
      ∃ g : ℂ → ℂ,
        AnalyticOnNhd ℂ g Set.univ ∧
        ∀ rho ∈ S,
          ‖g (xiSpectralPointSupport rho)‖ =
            soninEscapeCancellingGaugeModulus
              ((N : ℝ) * Real.log r) (xiSpectralPointSupport rho).im ∧
          g (xiSpectralPointSupport rho) ≠ 0 := by
  have hc : 0 < (N : ℝ) * Real.log r :=
    mul_pos (Nat.cast_pos.mpr hN) (Real.log_pos hr)
  exact ⟨hc, exists_entire_exact_sonin_cancelling_gauge_on_finite_xi_support
    S ((N : ℝ) * Real.log r)⟩

theorem exists_entire_interpolant_on_finite_xi_support
    (S : Finset XiDivisorSupport) (target : XiDivisorSupport → ℂ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g Set.univ ∧
      ∀ rho ∈ S, g (xiSpectralPointSupport rho) = target rho := by
  let p : Polynomial ℂ :=
    Lagrange.interpolate S xiSpectralPointSupport target
  refine ⟨fun z => p.eval z, AnalyticOnNhd.eval_polynomial p, ?_⟩
  intro rho hrho
  exact Lagrange.eval_interpolate_at_node target
    xiSpectralPointSupport_injective.injOn hrho

end RHTower
