import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Partition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest.Frequencies

/-! # Conditional routing of a single prime square identifies the physical heat duration -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities

open CoassociativeSplitting SquareTest

/-- Experimental rates for a prime ray of the emitted/surviving instrument. -/
def recorded (s : ℂ) (t gain left right : Duration) (p : Nat.Primes) (j k : ℕ) :=
  gain.val*left.val^j*right.val^k*
    ‖kernel s (emit t.val) (survive t.val) (rayState p j) (rayState p k)‖^2

private theorem recorded_ray (s : ℂ) (t gain left right : Duration) (p : Nat.Primes) :
    recorded s t gain left right p=rate s (emit t.val p.val) (survive t.val p.val) gain.val left.val right.val p := by
  funext j k
  simp only [recorded,rate,kernel,amplitude]
  change _ * ‖Complex.exp (s*(Real.log (branch (emit t.val) (survive t.val) (p.val^j) (p.val^k)):ℂ))‖^2=_
  rw [branch_on_ray]
  rfl

def binomialRead (s : ℂ) (t gain left right : Duration) (p : Nat.Primes) :=
  let f := frequency (recorded s t gain left right p)
  independent (f 2 0) (f 1 1) (f 0 2)

theorem recorded_odds (s : ℂ) (t gain left right : Duration) (p : Nat.Primes) :
    squareOdds (frequency (recorded s t gain left right p))=(4:ℝ)^(2*s.re) := by
  rw [recorded_ray]
  exact frequency_odds s ⟨_,emit_pos t.property p⟩ ⟨_,survive_pos t.val p⟩ gain left right p

theorem binomial_iff_conserving (s : ℂ) (t gain left right : Duration) (p : Nat.Primes) :
    binomialRead s t gain left right p ↔ isometric (kernel s (emit t.val) (survive t.val)) := by
  rw [binomialRead,recorded_ray]
  have he := emit_pos t.property p
  have hs := survive_pos t.val p
  have measure := independent_iff_isometric s ⟨_,he⟩ ⟨_,hs⟩ gain left right p
  exact measure.trans ((isometry_iff s he hs).trans (conserving_iff s (emit_pos t.property) (survive_pos t.val)).symm)

/-- With target heat parameter fixed, conditional data determine the unique
duration realizing it by a conserving no-emission measurement. -/
theorem observed_duration (z : TracePoint) (t gain left right : Duration) (p : Nat.Primes) :
    binomialRead (z.val/(t.val:ℂ)) t gain left right p ↔ t.val=2*z.val.re := by
  rw [binomial_iff_conserving,conserving_iff _ (emit_pos t.property) (survive_pos t.val),
    Complex.div_ofReal_re,div_eq_iff t.property.ne']
  constructor <;> intro h <;> linarith only [h]

#print axioms binomial_iff_conserving
#print axioms recorded_odds
#print axioms observed_duration

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities
