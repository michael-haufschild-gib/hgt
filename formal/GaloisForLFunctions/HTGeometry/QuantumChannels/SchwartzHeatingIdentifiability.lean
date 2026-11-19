import GaloisForLFunctions.HTGeometry.QuantumChannels.SchwartzJumpHeating
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.CubicHeatingReadout

/-!
# Which dephasing dynamics can Schwartz heating distinguish?

A bank of real momentum polynomials gives the same position-square heating
operator as another bank exactly when their squared derivatives have the
same sum. A single polynomial is determined up to sign and translation.
For cubic banks one separated finite-probe reading resolves the operator's
remaining ambiguity.
-/

noncomputable section
open Polynomial Finset
namespace GaloisForLFunctions.PolynomialJump.Schwartz
open ExclusionOfTheCriticalState.ProbeWalk
variable {k l : ℕ}

/-- The heating observable of a whole bank on Schwartz space. -/
def bankHeating (F : Fin k → ℝ[X]) : Op :=
  ∑ i, dissipator ((F i).map Complex.ofRealHom) (Q^2)

/-- Real polynomial multiplying the momentum representation of the heating. -/
def realSymbol (F : Fin k → ℝ[X]) : ℝ[X] := ∑ i, (F i).derivative^2

theorem bank_symbol (F : Fin k → ℝ[X]) :
    bankHeating F = momentum ((realSymbol F).map Complex.ofRealHom) := by
  simp only [bankHeating,realSymbol,position_heating,derivative_map,Polynomial.map_sum,
    Polynomial.map_pow,map_sum]

/-- Equality of operator heating is equivalent to a pointwise real polynomial identity. -/
theorem bank_heating_iff (F : Fin k → ℝ[X]) (G : Fin l → ℝ[X]) :
    bankHeating F = bankHeating G ↔
      ∀ t : ℝ, ∑ i, ((F i).derivative.eval t)^2 = ∑ i, ((G i).derivative.eval t)^2 := by
  rw [bank_symbol,bank_symbol,momentum_injective.eq_iff,
    (Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective).eq_iff]
  constructor
  · intro h t
    simpa only [realSymbol,eval_finsetSum,eval_pow] using congrArg (Polynomial.eval t) h
  · intro h
    exact Polynomial.funext fun t => by simpa only [realSymbol,eval_finsetSum,eval_pow] using h t

/-- Single-channel heating has exactly the global sign and constant-offset ambiguities
for every degree. -/
theorem single_heating_iff (f g : ℝ[X]) :
    bankHeating (fun _ : Fin 1 => f) = bankHeating (fun _ : Fin 1 => g) ↔
      ∃ a : ℝ, f=g+C a ∨ f= -g+C a := by
  rw [bank_heating_iff]
  simp only [Fin.sum_univ_one]
  constructor
  · intro h
    have hs : f.derivative^2 = g.derivative^2 := Polynomial.funext fun t => by simpa only [eval_pow] using h t
    have hz : (f.derivative-g.derivative)*(f.derivative+g.derivative) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp hz with hd | hd
    · have hc := eq_C_of_derivative_eq_zero (p := f-g) (by simpa only [map_sub] using hd)
      exact ⟨_,Or.inl (by rw [← hc]; abel)⟩
    · have hc := eq_C_of_derivative_eq_zero (p := f+g) (by simpa only [map_add] using hd)
      exact ⟨_,Or.inr (by rw [← hc]; abel)⟩
  · rintro ⟨a,h | h⟩ <;> rw [h] <;> simp [derivative_C]

/-- The polynomial represented by a cubic probe jump. -/
def cubicPolynomial (f : CubicHeating.Jump) : ℝ[X] := C f.a*X+C f.b*X^2+C f.c*X^3

private theorem eval_slope (f : CubicHeating.Jump) (t : ℝ) :
    (cubicPolynomial f).derivative.eval t = CubicHeating.slope f t := by
  simp [cubicPolynomial,CubicHeating.slope,derivative_mul,derivative_X_pow]
  <;> ring

private theorem cubic_heating_iff (F : Fin k → CubicHeating.Jump) (G : Fin l → CubicHeating.Jump) :
    bankHeating (cubicPolynomial ∘ F) = bankHeating (cubicPolynomial ∘ G) ↔
      CubicHeating.heat F = CubicHeating.heat G := by
  rw [bank_heating_iff,funext_iff]
  simp only [Function.comp_apply,eval_slope,CubicHeating.heat]

/-- Identical position-square heating operators coexist with strictly separated
dephasing rates at all distinct momenta. -/
theorem indistinguishable_operator_heating :
    ∃ (F : Fin 1 → CubicHeating.Jump) (G : Fin 2 → CubicHeating.Jump),
      bankHeating (cubicPolynomial ∘ F) = bankHeating (cubicPolynomial ∘ G) ∧
      ∀ x y, CubicHeating.rate F x y-CubicHeating.rate G x y=(x-y)^4/24 := by
  obtain ⟨F,G,he,h⟩ := CubicHeating.cubic_counterexample
  exact ⟨F,G,(cubic_heating_iff F G).mpr he,h⟩

/-- All cubic probe evolutions can be distinguished by the operator heating
together with any one off-diagonal rate. -/
theorem operator_and_pair_recover (F : Fin k → CubicHeating.Jump) (G : Fin l → CubicHeating.Jump)
    (p : {z : ℝ × ℝ // z.1 ≠ z.2}) :
    bankHeating (cubicPolynomial ∘ F) = bankHeating (cubicPolynomial ∘ G) →
      (CubicHeating.rate F p.val.1 p.val.2 = CubicHeating.rate G p.val.1 p.val.2 ↔
        CubicHeating.rate F = CubicHeating.rate G) :=
  fun he => CubicHeating.single_rate_recovery F G p ((cubic_heating_iff F G).mp he)

#print axioms bank_heating_iff
#print axioms single_heating_iff
#print axioms indistinguishable_operator_heating
#print axioms operator_and_pair_recover
end GaloisForLFunctions.PolynomialJump.Schwartz
