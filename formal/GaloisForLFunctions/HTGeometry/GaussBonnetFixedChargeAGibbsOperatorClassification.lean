import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeALinearJetObservables
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQuarticOperatorClassification

/-!
# Sharp asymptotic odd differential operators of actual Gibbs energy

For the actual aligned normalized Gibbs family, a*D^5+b*D^3+c*D
converges to zero at every angle exactly when (b,c)=(20a,64a).
The same coefficient condition is equivalent to uniform convergence
to zero. Thus the critical operator ratios are necessary as well as
sufficient; lower odd order cannot replace them nontrivially.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsOddOperator (w φ τ l₁ l₂ a b c ψ : ℝ) : ℝ :=
  egbFixedChargeALinearJetObservable a b c 5 3 1
    (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ

theorem egbFixedChargeAGibbsOddOperator_pointwise_classification (w φ l₁ l₂ a b c : ℝ) :
    (∀ ψ : ℝ, Tendsto (fun τ => egbFixedChargeAGibbsOddOperator w φ τ l₁ l₂ a b c ψ)
      atBot (𝓝 (0 : ℝ))) ↔ b = 20 * a ∧ c = 64 * a := by
  constructor
  · intro h
    apply (egbFixedChargeAQuarticProfile_odd_operator_classification a b c).mp
    intro ψ
    have hl := (egbFixedChargeALinearJetObservable_uniform_limit w φ l₁ l₂ a b c 5 3 1).tendsto_at ψ
    exact tendsto_nhds_unique hl (h ψ)
  · intro h
    have hc := (egbFixedChargeAQuarticProfile_odd_operator_classification a b c).mpr h
    have hz : egbFixedChargeALinearJetObservable a b c 5 3 1 (fun x : ℝ => cos x ^ 4) = fun _ => 0 :=
      funext hc
    have hl := egbFixedChargeALinearJetObservable_uniform_limit w φ l₁ l₂ a b c 5 3 1
    rw [hz] at hl
    intro ψ
    exact hl.tendsto_at ψ

theorem egbFixedChargeAGibbsOddOperator_uniform_classification (w φ l₁ l₂ a b c : ℝ) :
    TendstoUniformly (fun τ ψ => egbFixedChargeAGibbsOddOperator w φ τ l₁ l₂ a b c ψ)
      (fun _ => (0 : ℝ)) atBot ↔ b = 20 * a ∧ c = 64 * a := by
  constructor
  · intro h
    exact (egbFixedChargeAGibbsOddOperator_pointwise_classification w φ l₁ l₂ a b c).mp
      (fun ψ => h.tendsto_at ψ)
  · intro h
    have hc := (egbFixedChargeAQuarticProfile_odd_operator_classification a b c).mpr h
    have hz : egbFixedChargeALinearJetObservable a b c 5 3 1 (fun x : ℝ => cos x ^ 4) = fun _ => 0 :=
      funext hc
    have hl := egbFixedChargeALinearJetObservable_uniform_limit w φ l₁ l₂ a b c 5 3 1
    rw [hz] at hl
    exact hl

theorem egbFixedChargeAGibbs_third_order_uniform_obstruction (w φ l₁ l₂ b c : ℝ) :
    TendstoUniformly (fun τ ψ =>
      b * iteratedDeriv 3 (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ +
      c * iteratedDeriv 1 (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (fun _ => (0 : ℝ)) atBot ↔ b = 0 ∧ c = 0 := by
  simpa only [egbFixedChargeAGibbsOddOperator, egbFixedChargeALinearJetObservable,
    zero_mul, zero_add, mul_zero] using
    egbFixedChargeAGibbsOddOperator_uniform_classification w φ l₁ l₂ 0 b c

end GaloisForLFunctions.HTGeometry
