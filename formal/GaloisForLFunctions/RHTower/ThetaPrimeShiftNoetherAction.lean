import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherVariation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiable complete prime action and its arithmetic Ward identity

Bounded continuous local scalings give an entire action in the complex
variation parameter. The derivative is justified by an integrable bound
on every local parameter ball. At zero it equals the complete arithmetic
Noether exchange. Adding a constant to the local scaling profile leaves
the action unchanged, realizing its global reciprocal symmetry.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace RHTower.ThetaSourceWard

def thetaPrimeProfileIncrement (chi : ℝ →ᵇ ℂ) (p : ℕ × ℝ) : ℂ :=
  chi (p.2 + Real.log p.1) - chi p.2

theorem continuous_thetaPrimeProfileIncrement (chi : ℝ →ᵇ ℂ) :
    Continuous (thetaPrimeProfileIncrement chi) := by
  have hl : Continuous (fun n : ℕ => Real.log n) := continuous_of_discreteTopology
  exact (chi.continuous.comp (continuous_snd.add (hl.comp continuous_fst))).sub
    (chi.continuous.comp continuous_snd)

theorem norm_thetaPrimeProfileIncrement_le (chi : ℝ →ᵇ ℂ) (p : ℕ × ℝ) :
    ‖thetaPrimeProfileIncrement chi p‖ ≤ 2 * ‖chi‖ := by
  exact (norm_sub_le _ _).trans (by
    linarith [chi.norm_coe_le_norm (p.2 + Real.log p.1), chi.norm_coe_le_norm p.2])

theorem norm_exp_thetaPrimeProfileIncrement_le (chi : ℝ →ᵇ ℂ) (e : ℂ) (p : ℕ × ℝ) :
    ‖Complex.exp (e * thetaPrimeProfileIncrement chi p)‖ ≤
      Real.exp (‖e‖ * (2 * ‖chi‖)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  exact (Complex.re_le_norm _).trans (by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_thetaPrimeProfileIncrement_le chi p) (norm_nonneg e))

def thetaPrimeLocalAction (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) (e : ℂ) : ℂ :=
  ∫ p, Complex.exp (e * thetaPrimeProfileIncrement chi p) * thetaPrimeLinkDensity S T p
    ∂thetaPrimeLinkMeasure

theorem integrable_thetaPrimeLocalAction (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) (e : ℂ) :
    Integrable (fun p => Complex.exp (e * thetaPrimeProfileIncrement chi p) *
      thetaPrimeLinkDensity S T p) thetaPrimeLinkMeasure :=
  (integrable_thetaPrimeLinkDensity S T).bdd_mul
    (Complex.continuous_exp.comp (continuous_const.mul
      (continuous_thetaPrimeProfileIncrement chi))).aestronglyMeasurable
    (Eventually.of_forall (norm_exp_thetaPrimeProfileIncrement_le chi e))

/-- The exponential action is the literal prime action on reciprocally rescaled fields. -/
theorem thetaPrimeLocalAction_density (S T : ThetaSource) (chi : ℝ →ᵇ ℂ)
    (e : ℂ) (n : ℕ) (x : ℝ) :
    Complex.exp (e * thetaPrimeProfileIncrement chi (n, x)) * thetaPrimeLinkDensity S T (n, x) =
      primeShiftActionDensity n
        (fun y => Complex.exp (-(e * chi y)) * (T.k y : ℂ))
        (fun y => Complex.exp (e * chi y) * (S.k y : ℂ)) x := by
  have he : e * thetaPrimeProfileIncrement chi (n, x) =
      -(e * chi x) + e * chi (x + Real.log n) := by
    unfold thetaPrimeProfileIncrement
    ring
  rw [he, Complex.exp_add]
  unfold thetaPrimeLinkDensity primeShiftActionDensity
  ring

/-- Derivative of the entire complete prime action, with differentiation under the integral proved. -/
theorem hasDerivAt_thetaPrimeLocalAction (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) (e : ℂ) :
    HasDerivAt (thetaPrimeLocalAction S T chi)
      (∫ p, thetaPrimeProfileIncrement chi p *
        Complex.exp (e * thetaPrimeProfileIncrement chi p) * thetaPrimeLinkDensity S T p
          ∂thetaPrimeLinkMeasure) e := by
  let C : ℝ := 2 * ‖chi‖ * Real.exp ((‖e‖ + 1) * (2 * ‖chi‖))
  have hbound (p : ℕ × ℝ) (u : ℂ) (hu : u ∈ Metric.ball e 1) :
      ‖thetaPrimeProfileIncrement chi p * Complex.exp (u * thetaPrimeProfileIncrement chi p) *
        thetaPrimeLinkDensity S T p‖ ≤ C * ‖thetaPrimeLinkDensity S T p‖ := by
    have hu' : ‖u - e‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hu
    have hun : ‖u‖ ≤ ‖e‖ + 1 := by
      have h := norm_add_le (u - e) e
      rw [sub_add_cancel] at h
      linarith
    have hexp : ‖Complex.exp (u * thetaPrimeProfileIncrement chi p)‖ ≤
        Real.exp ((‖e‖ + 1) * (2 * ‖chi‖)) :=
      (norm_exp_thetaPrimeProfileIncrement_le chi u p).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hun (by positivity)))
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (norm_thetaPrimeProfileIncrement_le chi p) hexp
        (norm_nonneg _) (by positivity)) (norm_nonneg _)
  have hd (p : ℕ × ℝ) (u : ℂ) :
      HasDerivAt (fun z : ℂ => Complex.exp (z * thetaPrimeProfileIncrement chi p) *
          thetaPrimeLinkDensity S T p)
        (thetaPrimeProfileIncrement chi p * Complex.exp (u * thetaPrimeProfileIncrement chi p) *
          thetaPrimeLinkDensity S T p) u := by
    convert! (((hasDerivAt_id u).mul_const (thetaPrimeProfileIncrement chi p)).cexp).mul_const
      (thetaPrimeLinkDensity S T p) using 1
    simp only [id_eq]
    ring
  have hcont (u : ℂ) : Continuous (fun p =>
      Complex.exp (u * thetaPrimeProfileIncrement chi p) * thetaPrimeLinkDensity S T p) :=
    (Complex.continuous_exp.comp
      (continuous_const.mul (continuous_thetaPrimeProfileIncrement chi))).mul
        (continuous_thetaPrimeLinkDensity S T)
  have hderiv : Continuous (fun p => thetaPrimeProfileIncrement chi p *
      Complex.exp (e * thetaPrimeProfileIncrement chi p) * thetaPrimeLinkDensity S T p) :=
    ((continuous_thetaPrimeProfileIncrement chi).mul (Complex.continuous_exp.comp
      (continuous_const.mul (continuous_thetaPrimeProfileIncrement chi)))).mul
        (continuous_thetaPrimeLinkDensity S T)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u p => Complex.exp (u * thetaPrimeProfileIncrement chi p) * thetaPrimeLinkDensity S T p)
    (F' := fun u p => thetaPrimeProfileIncrement chi p *
      Complex.exp (u * thetaPrimeProfileIncrement chi p) * thetaPrimeLinkDensity S T p)
    (bound := fun p => C * ‖thetaPrimeLinkDensity S T p‖) (μ := thetaPrimeLinkMeasure)
    (Metric.ball_mem_nhds e one_pos)
    (Eventually.of_forall fun u => (hcont u).aestronglyMeasurable)
    (integrable_thetaPrimeLocalAction S T chi e) hderiv.aestronglyMeasurable
    (Eventually.of_forall hbound)
    ((integrable_thetaPrimeLinkDensity S T).norm.const_mul C)
    (Eventually.of_forall fun p u _ => hd p u)).2

theorem hasDerivAt_thetaPrimeLocalAction_zero (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    HasDerivAt (thetaPrimeLocalAction S T chi) (thetaPrimeLocalResponse S T chi) 0 := by
  simpa only [zero_mul, Complex.exp_zero, mul_one, thetaPrimeProfileIncrement,
    thetaPrimeLocalResponse] using hasDerivAt_thetaPrimeLocalAction S T chi 0

/-- The actual theta action differentiates to the literal Gamma/pole exchange. -/
theorem hasDerivAt_thetaPrimeLocalAction_actual (chi : ℝ →ᵇ ℂ) :
    HasDerivAt (thetaPrimeLocalAction thetaCuspTiltSource thetaCuspTiltSource chi)
      (∫ x : ℝ, chi x * thetaNoetherExchange x) 0 := by
  rw [← thetaPrimeLocalResponse_actual]
  exact hasDerivAt_thetaPrimeLocalAction_zero _ _ chi

/-- Global reciprocal scaling is the constant-profile gauge symmetry of the full action. -/
theorem thetaPrimeLocalAction_add_const (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) (c e : ℂ) :
    thetaPrimeLocalAction S T (chi + BoundedContinuousFunction.const ℝ c) e =
      thetaPrimeLocalAction S T chi e := by
  simp [thetaPrimeLocalAction, thetaPrimeProfileIncrement]

end RHTower.ThetaSourceWard
