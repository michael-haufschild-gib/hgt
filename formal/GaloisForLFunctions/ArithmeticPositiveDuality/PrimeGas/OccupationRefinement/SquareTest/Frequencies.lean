import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest.Rigidity

/-! # The exact real exponent from conditional frequencies -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest

/-- Conditioning all three outcomes on the observed total preserves the full odds ratio. -/
theorem conditioned_odds (r : ℕ → ℕ → ℝ) (a : 0<r 2 0) (b : 0<r 1 1) (c : 0<r 0 2) :
    squareOdds (frequency r)=squareOdds r := by
  have pos : 0<total r := add_pos (add_pos a b) c
  simp only [squareOdds,frequency,div_pow,div_mul_div_comm,←sq]
  field_simp [pos.ne',a.ne',c.ne']

theorem frequency_odds (s : ℂ) (u v gain left right : Set.Ioi (0:ℝ)) (p : Nat.Primes) :
    squareOdds (frequency (rate s u.val v.val gain.val left.val right.val p))=(4:ℝ)^(2*s.re) := by
  have pos := rate_pos s u v gain left right p
  rw [conditioned_odds _ (pos 2 0) (pos 1 1) (pos 0 2),square_odds s u v gain left right]

#print axioms conditioned_odds
#print axioms frequency_odds

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest
