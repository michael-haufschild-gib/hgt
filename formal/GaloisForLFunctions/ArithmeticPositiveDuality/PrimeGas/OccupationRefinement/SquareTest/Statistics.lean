import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Profiles

/-! # Recognizing independent routing from three conditional probabilities -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest

open Real

/-- Probability of routing two indistinguishable particles independently with the same transmission. -/
def independent (a b c : ℝ) := ∃ t ∈ Set.Ioo (0:ℝ) 1, a=t^2 ∧ b=2*t*(1-t) ∧ c=(1-t)^2

/-- The middle mass and the two endpoints detect binomiality with unknown transmission. -/
theorem independent_iff {a b c : ℝ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (total : a+b+c=1) :
    independent a b c ↔ b^2=4*a*c := by
  constructor
  · rintro ⟨t,_,rfl,rfl,rfl⟩
    ring
  · intro eqn
    have A := sq_sqrt ha.le
    have C := sq_sqrt hc.le
    have sqB : b^2=(2*sqrt a*sqrt c)^2 := by
      calc b^2 = 4*a*c := eqn
           _ = (2*sqrt a*sqrt c)^2 := by rw [mul_pow,mul_pow,A,C]; ring
    have B := (sq_eq_sq₀ hb.le (by positivity : 0≤2*sqrt a*sqrt c)).mp sqB
    have squared : (sqrt a+sqrt c)^2=(1:ℝ)^2 := by
      rw [add_sq,A,C,←B,one_pow]
      exact total
    have norm := (sq_eq_sq₀ (add_nonneg (sqrt_nonneg a) (sqrt_nonneg c)) zero_le_one).mp squared
    have diff : 1-sqrt a=sqrt c := by linarith only [norm]
    have unit : sqrt a<1 := by linarith only [norm,sqrt_pos.mpr hc]
    exact ⟨sqrt a,⟨sqrt_pos.mpr ha,unit⟩,A.symm,by rw [diff,B],by rw [diff,C]⟩

#print axioms independent_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest
