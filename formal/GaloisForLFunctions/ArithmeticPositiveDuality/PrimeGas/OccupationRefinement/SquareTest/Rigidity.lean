import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest.Statistics
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest.Odds
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Isometry

/-! # Independent routing on one prime square detects isometry of the whole gas -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest

open Real CoassociativeSplitting

def total (r : ℕ → ℕ → ℝ) := r 2 0+r 1 1+r 0 2

def frequency (r : ℕ → ℕ → ℝ) (j k : ℕ) := r j k/total r

theorem conditioned_test (r : ℕ → ℕ → ℝ) (ha : 0<r 2 0) (hb : 0<r 1 1) (hc : 0<r 0 2) :
    independent (frequency r 2 0) (frequency r 1 1) (frequency r 0 2) ↔ squareOdds r=4 := by
  have pos : 0<total r := add_pos (add_pos ha hb) hc
  have normalized : frequency r 2 0+frequency r 1 1+frequency r 0 2=1 := by
    simp only [frequency,←add_div]
    exact div_self pos.ne'
  rw [independent_iff (a:=frequency r 2 0) (b:=frequency r 1 1) (c:=frequency r 0 2)
    (div_pos ha pos) (div_pos hb pos) (div_pos hc pos) normalized,
    squareOdds,div_eq_iff (mul_ne_zero ha.ne' hc.ne')]
  simp only [frequency,div_pow]
  constructor <;> intro eqn
  · field_simp [pos.ne'] at eqn
    linarith only [eqn]
  · field_simp [pos.ne']
    linarith only [eqn]

/-- After conditioning the three rates to sum to one, a binomial law
on any single doubled prime is equivalent to isometry on all integer states. -/
theorem independent_iff_isometric (s : ℂ) (u v gain left right : Set.Ioi (0:ℝ)) (p : Nat.Primes) :
    let r := rate s u.val v.val gain.val left.val right.val p
    independent (frequency r 2 0) (frequency r 1 1) (frequency r 0 2) ↔
      isometric (amplitude s u.val v.val) := by
  dsimp only
  have pos := rate_pos s u v gain left right p
  rw [conditioned_test _ (pos 2 0) (pos 1 1) (pos 0 2),square_odds s u v gain left right,
    isometry_iff s u.property v.property]
  have inject := (strictMono_rpow_of_base_gt_one (by norm_num : 1<(4:ℝ))).injective
  calc (4:ℝ)^(2*s.re)=4 ↔ (4:ℝ)^(2*s.re)=(4:ℝ)^(1:ℝ) := by rw [rpow_one]
       _ ↔ 2*s.re=1 := inject.eq_iff
       _ ↔ _ := by constructor <;> intro h <;> linarith only [h]

theorem thermometer (s : ℂ) (u v gain left right : Set.Ioi (0:ℝ)) (p : Nat.Primes) :
    log (squareOdds (rate s u.val v.val gain.val left.val right.val p))/log 4=2*s.re := by
  rw [square_odds s u v gain left right,log_rpow (by norm_num : 0<(4:ℝ))]
  exact mul_div_cancel_right₀ _ (log_pos (by norm_num : 1<(4:ℝ))).ne'

#print axioms conditioned_test
#print axioms independent_iff_isometric
#print axioms thermometer

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest
