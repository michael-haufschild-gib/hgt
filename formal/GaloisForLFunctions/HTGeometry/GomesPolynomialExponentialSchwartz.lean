import GaloisForLFunctions.HTGeometry.GomesPolynomialExpDerivatives
import GaloisForLFunctions.HTGeometry.GomesPolynomialExpRapidDecay

/-!
# Schwartz polynomial exponential families

All finite polynomial profiles yield Schwartz functions, with arbitrary polynomial
amplitudes. This supplies the analytic carrier needed for the experimental tensor
half-density interpretation of the shared polynomial dilaton connection.
-/

noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Every polynomial amplitude against a finite polynomial exponential is Schwartz. -/
def gomesPolynomialAmplitudeSchwartz (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) : 𝓢(ℝ, ℝ) where
  toFun := fun x => Q.eval x * Real.exp (P.val.eval x)
  smooth' := (gomesPolynomialExp_contDiff P.val Q).of_le le_top
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := gomesPolynomialExp_weighted_bounded P (gomesPolynomialExpJet P.val n Q) k
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, gomesPolynomialExp_iteratedDeriv]
    exact hC x

/-- The construction retains the exact unnormalized polynomial amplitude. -/
theorem gomesPolynomialAmplitudeSchwartz_apply (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) (x : ℝ) :
    gomesPolynomialAmplitudeSchwartz P Q x = Q.eval x * Real.exp (P.val.eval x) := rfl

/-- Differentiation is realized inside Schwartz space by the polynomial connection. -/
theorem gomesPolynomialAmplitudeSchwartz_deriv (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) :
    SchwartzMap.derivCLM ℝ ℝ (gomesPolynomialAmplitudeSchwartz P Q) =
      gomesPolynomialAmplitudeSchwartz P (Q.derivative + P.val.derivative * Q) := by
  ext x
  exact (gomesPolynomialExp_hasDerivAt P.val Q x).deriv

/-- The Schwartz realization preserves amplitude superposition. -/
theorem gomesPolynomialAmplitudeSchwartz_add (P : GomesFinitePolynomialProfile) (Q R : ℝ[X]) :
    gomesPolynomialAmplitudeSchwartz P (Q + R) =
      gomesPolynomialAmplitudeSchwartz P Q + gomesPolynomialAmplitudeSchwartz P R := by
  ext x
  change (Q + R).eval x * _ = Q.eval x * _ + R.eval x * _
  rw [eval_add, add_mul]

/-- Real amplitude scaling agrees with Schwartz scalar multiplication. -/
theorem gomesPolynomialAmplitudeSchwartz_scale (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) (c : ℝ) :
    gomesPolynomialAmplitudeSchwartz P (C c * Q) = c • gomesPolynomialAmplitudeSchwartz P Q := by
  ext x
  change (C c * Q).eval x * _ = c * (Q.eval x * _)
  rw [eval_mul, eval_C, mul_assoc]

/-- Every polynomial observable is absolutely integrable against a finite polynomial density. -/
theorem gomesPolynomialAmplitude_integrable (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) :
    Integrable (fun x => Q.eval x * Real.exp (P.val.eval x)) :=
  (gomesPolynomialAmplitudeSchwartz P Q).integrable

/-- The corresponding absolute polynomial moment is finite. -/
theorem gomesPolynomialAmplitude_abs_integrable (P : GomesFinitePolynomialProfile) (Q : ℝ[X]) :
    Integrable (fun x => |Q.eval x| * Real.exp (P.val.eval x)) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
    (gomesPolynomialAmplitude_integrable P Q).norm

/-- A polynomial exponential is Schwartz exactly when its density has finite mass. -/
theorem gomesPolynomialExponential_schwartz_iff (H : ℝ[X]) :
    (∃ f : 𝓢(ℝ, ℝ), ∀ x, f x = Real.exp (H.eval x)) ↔
      IsFiniteMeasure (gomesDilatonMeasure H) := by
  constructor
  · rintro ⟨f, hf⟩
    rw [gomesDilatonMeasure_finite_iff_integrable]
    exact f.integrable.congr (Eventually.of_forall hf)
  · intro h
    refine ⟨gomesPolynomialAmplitudeSchwartz ⟨H, h⟩ 1, fun x => ?_⟩
    simp only [gomesPolynomialAmplitudeSchwartz_apply, eval_one, one_mul]

/-- The coefficient criterion completely classifies pure polynomial exponentials in Schwartz space. -/
theorem gomesPolynomialExponential_schwartz_polynomial_iff (H : ℝ[X]) :
    (∃ f : 𝓢(ℝ, ℝ), ∀ x, f x = Real.exp (H.eval x)) ↔
      0 < H.natDegree ∧ Even H.natDegree ∧ H.leadingCoeff < 0 := by
  rw [gomesPolynomialExponential_schwartz_iff, gomesDilatonMeasure_finite_polynomial_iff]

end GaloisForLFunctions.HTGeometry
