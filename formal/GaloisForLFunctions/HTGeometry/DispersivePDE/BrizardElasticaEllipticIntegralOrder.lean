import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaClosureBounds
import Mathlib.Tactic

/-!
# Order bounds for Brizard's complete elliptic integrals

Direct comparison with the constant integrand `1` separates the two Jacobi chambers.  In the
classical chamber `E ≤ π/2 ≤ K`; in the negative chamber the inequalities reverse.  These are
closed analytic statements, require no numerical elliptic-function evaluation, and give a simple
global upper bound for the classical knot-closure scale.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem classical_completeEIntegrand_le_one (m : ClassicalModulus) (θ : ℝ) :
    completeEIntegrand m θ ≤ 1 := by
  have hrad : 0 < 1 - (m : ℝ) * Real.sin θ ^ (2 : ℕ) :=
    subcriticalRadicand_pos (classicalAsSubcritical m) θ
  have hprod : 0 ≤ (m : ℝ) * Real.sin θ ^ (2 : ℕ) :=
    mul_nonneg m.property.1.le (sq_nonneg _)
  rw [completeEIntegrand, Real.sqrt_le_iff]
  exact ⟨zero_le_one, by nlinarith⟩

theorem classical_one_le_completeKIntegrand (m : ClassicalModulus) (θ : ℝ) :
    1 ≤ completeKIntegrand m θ := by
  have hrad : 0 < 1 - (m : ℝ) * Real.sin θ ^ (2 : ℕ) :=
    subcriticalRadicand_pos (classicalAsSubcritical m) θ
  have hs : 0 < Real.sqrt (1 - (m : ℝ) * Real.sin θ ^ (2 : ℕ)) :=
    Real.sqrt_pos.mpr hrad
  rw [completeKIntegrand, one_le_inv₀ hs, Real.sqrt_le_iff]
  exact ⟨zero_le_one, by
    have hprod : 0 ≤ (m : ℝ) * Real.sin θ ^ (2 : ℕ) :=
      mul_nonneg m.property.1.le (sq_nonneg _)
    nlinarith⟩

theorem negative_completeKIntegrand_le_one (m : NegativeModulus) (θ : ℝ) :
    completeKIntegrand m θ ≤ 1 := by
  have hrad : 0 < 1 - (m : ℝ) * Real.sin θ ^ (2 : ℕ) :=
    subcriticalRadicand_pos (negativeAsSubcritical m) θ
  have hs : 0 < Real.sqrt (1 - (m : ℝ) * Real.sin θ ^ (2 : ℕ)) :=
    Real.sqrt_pos.mpr hrad
  rw [completeKIntegrand, inv_le_one₀ hs, Real.one_le_sqrt]
  have hprod : (m : ℝ) * Real.sin θ ^ (2 : ℕ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg m.property.le (sq_nonneg _)
  linarith

theorem negative_one_le_completeEIntegrand (m : NegativeModulus) (θ : ℝ) :
    1 ≤ completeEIntegrand m θ := by
  rw [completeEIntegrand, Real.one_le_sqrt]
  have hprod : (m : ℝ) * Real.sin θ ^ (2 : ℕ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg m.property.le (sq_nonneg _)
  linarith

theorem completeEllipticE_classical_le_pi_div_two (m : ClassicalModulus) :
    completeEllipticE m ≤ Real.pi / 2 := by
  have hEcont : Continuous (completeEIntegrand m) := by
    simpa [classicalAsSubcritical] using
      continuous_completeEIntegrand (classicalAsSubcritical m)
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    (hEcont.intervalIntegrable _ _)
    ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable _ _)
    (fun θ _ => classical_completeEIntegrand_le_one m θ)
  simpa [completeEllipticE, completeEIntegrand] using h

theorem pi_div_two_le_completeEllipticK_classical (m : ClassicalModulus) :
    Real.pi / 2 ≤ completeEllipticK m := by
  have hKcont : Continuous (completeKIntegrand m) := by
    simpa [classicalAsSubcritical] using
      continuous_completeKIntegrand (classicalAsSubcritical m)
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable _ _)
    (hKcont.intervalIntegrable _ _)
    (fun θ _ => classical_one_le_completeKIntegrand m θ)
  simpa [completeEllipticK, completeKIntegrand] using h

theorem completeEllipticK_negative_le_pi_div_two (m : NegativeModulus) :
    completeEllipticK m ≤ Real.pi / 2 := by
  have hKcont : Continuous (completeKIntegrand m) := by
    simpa [negativeAsSubcritical] using
      continuous_completeKIntegrand (negativeAsSubcritical m)
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    (hKcont.intervalIntegrable _ _)
    ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable _ _)
    (fun θ _ => negative_completeKIntegrand_le_one m θ)
  simpa [completeEllipticK, completeKIntegrand] using h

theorem pi_div_two_le_completeEllipticE_negative (m : NegativeModulus) :
    Real.pi / 2 ≤ completeEllipticE m := by
  have hEcont : Continuous (completeEIntegrand m) := by
    simpa [negativeAsSubcritical] using
      continuous_completeEIntegrand (negativeAsSubcritical m)
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable _ _)
    (hEcont.intervalIntegrable _ _)
    (fun θ _ => negative_one_le_completeEIntegrand m θ)
  simpa [completeEllipticE, completeEIntegrand] using h

theorem completeEllipticE_le_K_classical (m : ClassicalModulus) :
    completeEllipticE m ≤ completeEllipticK m :=
  (completeEllipticE_classical_le_pi_div_two m).trans
    (pi_div_two_le_completeEllipticK_classical m)

theorem completeEllipticK_le_E_negative (m : NegativeModulus) :
    completeEllipticK m ≤ completeEllipticE m :=
  (completeEllipticK_negative_le_pi_div_two m).trans
    (pi_div_two_le_completeEllipticE_negative m)

theorem closureQ_classical_le_one_add_modulus (m : ClassicalModulus) :
    closureQ m ≤ 1 + (m : ℝ) := by
  have hK : 0 < completeEllipticK m := completeEllipticK_classical_pos m
  have hratio : completeEllipticE m / completeEllipticK m ≤ 1 := by
    exact (div_le_one hK).2 (completeEllipticE_le_K_classical m)
  rw [closureQ]
  have hrewrite : 2 * completeEllipticE m / completeEllipticK m =
      2 * (completeEllipticE m / completeEllipticK m) := by ring
  rw [hrewrite]
  linarith

theorem closureQ_classical_lt_two (m : ClassicalModulus) : closureQ m < 2 :=
  lt_of_le_of_lt (closureQ_classical_le_one_add_modulus m) (by linarith [m.property.2])

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
