import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateHasIndefiniteFiniteProbeMatrices
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.TranslationDuality

/-!
# Forward differences of the actual tail-probe moments

Translation of the moment index is multiplication by a power of the bounded
coordinate `exp(u+T)`. The Coleman translation identity therefore turns a
forward difference into the exact multiplier `exp(n(u+T))-1` on the actual
state density. Polynomial tests and their squares retain all signed terms.
-/

noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators Classical
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticHarmonicAnalysis.Coleman

/-- Forward difference at displacement `n` of the damped tail moments. -/
def tailProbeDifference (F : ℝ → ℝ) (T : ℝ) (n k : ℕ) : ℝ :=
  tailProbeMoment F T (n + k) - tailProbeMoment F T k

/-- Every polynomial in the bounded tail coordinate is integrable against the damped density. -/
theorem integrable_tailProbePolynomial {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (T : ℝ) (P : ℝ[X]) : Integrable
      (fun u => P.eval (Real.exp (u + T)) * (F u * Real.exp (10 * (u + T))))
      (volume.restrict (Iio (-T))) := by
  have h := integrable_finsetSum P.support (fun n _ =>
    (integrable_tailProbeMonomial hF T n).const_mul (P.coeff n))
  simpa only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul, mul_assoc] using h

/-- The tail moment functional is the literal polynomial integral of the state. -/
theorem momentFunctional_tailProbeMoment {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (T : ℝ) (P : ℝ[X]) :
    _root_.HTGeometry.momentFunctional (tailProbeMoment F T) P =
      ∫ u in Iio (-T), P.eval (Real.exp (u + T)) * (F u * Real.exp (10 * (u + T))) := by
  rw [_root_.HTGeometry.momentFunctional_eq_support_sum]
  simp_rw [tailProbeMoment_eq_coordinate, ← integral_const_mul]
  rw [← integral_finsetSum _ (fun n _ =>
    (integrable_tailProbeMonomial hF T n).const_mul (P.coeff n))]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul, mul_assoc]

/-- Forward differences insert the exact exponential difference into every polynomial test. -/
theorem momentFunctional_tailProbeDifference {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (T : ℝ) (n : ℕ) (P : ℝ[X]) :
    _root_.HTGeometry.momentFunctional (tailProbeDifference F T n) P =
      ∫ u in Iio (-T), (Real.exp ((n : ℝ) * (u + T)) - 1) *
        P.eval (Real.exp (u + T)) * (F u * Real.exp (10 * (u + T))) := by
  change _root_.HTGeometry.momentFunctional
    (fun k => tailProbeMoment F T (n + k) - tailProbeMoment F T k) P = _
  rw [← momentFunctional_translation_difference, momentFunctional_tailProbeMoment hF]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X_pow,
    Polynomial.eval_one, ← Real.exp_nat_mul]

/-- The corresponding finite Hankel test retains the signed state density exactly. -/
theorem tailProbeDifference_square {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (T : ℝ) (n : ℕ) (P : ℝ[X]) :
    _root_.HTGeometry.momentFunctional (tailProbeDifference F T n) (P ^ 2) =
      ∫ u in Iio (-T), (Real.exp ((n : ℝ) * (u + T)) - 1) *
        (P.eval (Real.exp (u + T))) ^ 2 * (F u * Real.exp (10 * (u + T))) := by
  rw [momentFunctional_tailProbeDifference hF]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [_root_.Polynomial.eval_pow (p := P) (x := Real.exp (u + T)) 2]

/-- The actual critical state, when it exists, satisfies every tail-difference identity. -/
theorem riemannHypothesis_or_tailProbeDifferences :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ (T : ℝ) (n : ℕ) (P : ℝ[X]),
        _root_.HTGeometry.momentFunctional (tailProbeDifference F T n) (P ^ 2) =
          ∫ u in Iio (-T), (Real.exp ((n : ℝ) * (u + T)) - 1) *
            (P.eval (Real.exp (u + T))) ^ 2 * (F u * Real.exp (10 * (u + T))) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, fun T n P =>
      tailProbeDifference_square (criticalHalfLineEnergyDomain_of_groundState hF) T n P⟩

#print axioms integrable_tailProbePolynomial
#print axioms momentFunctional_tailProbeDifference
#print axioms tailProbeDifference_square
#print axioms riemannHypothesis_or_tailProbeDifferences

end GaloisForLFunctions.ExclusionOfTheCriticalState
