import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Channels

/-! # Calibration-free determination of the exponent on a single prime square -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest

open Real

/-- Integer occupation with exactly k copies of the given prime. -/
def rayState (p : Nat.Primes) (k : ℕ) : ℕ+ := ⟨p.val^k,pow_pos p.property.pos _⟩

/-- Born rate with common gain and independent per-particle detection efficiencies. -/
def rate (s : ℂ) (u v gain left right : ℝ) (p : Nat.Primes) (j k : ℕ) :=
  gain*left^j*right^k*‖amplitude s u v (rayState p j) (rayState p k)‖^2

theorem rate_formula (s : ℂ) {u v : ℝ} (hu : 0<u) (hv : 0<v) (gain left right : ℝ)
    (p : Nat.Primes) (j k : ℕ) :
    rate s u v gain left right p j k = gain*left^j*right^k*(binomial u v j k)^(2*s.re) := by
  rw [rate,norm_sq s hu hv]
  change _* (probability u v (p.val^j) (p.val^k))^(2*s.re)=_
  rw [prime_ray hu hv]

theorem rate_pos (s : ℂ) (u v gain left right : Set.Ioi (0:ℝ)) (p : Nat.Primes) (j k : ℕ) :
    0<rate s u.val v.val gain.val left.val right.val p j k := by
  rw [rate,norm_sq s u.property v.property]
  exact mul_pos (mul_pos (mul_pos gain.property (pow_pos left.property _)) (pow_pos right.property _))
    (rpow_pos_of_pos (probability_pos u.property v.property _ _) _)

def squareOdds (r : ℕ → ℕ → ℝ) := (r 1 1)^2/(r 2 0*r 0 2)

private theorem cancel_gain {g l r a c : ℝ} (hg : 0<g) (hl : 0<l) (hr : 0<r)
    (ha : 0<a) (hc : 0<c) (b : ℝ) :
    (g*l*r*b)^2/((g*l^2*a)*(g*r^2*c))=b^2/(a*c) := by
  field_simp [hg.ne',hl.ne',hr.ne',ha.ne',hc.ne']

private theorem power_ratio (x : ℝ) {a b c : ℝ} (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    (b^x)^2/(a^x*c^x)=(b^2/(a*c))^x := by
  rw [sq,sq,div_rpow (mul_nonneg hb.le hb.le) (mul_nonneg ha.le hc.le),
    mul_rpow hb.le hb.le,mul_rpow ha.le hc.le]

/-- Two copies measure the exponent even if both output efficiencies and
the relative capacities are unknown. -/
theorem square_odds (s : ℂ) (u v gain left right : Set.Ioi (0:ℝ)) (p : Nat.Primes) :
    squareOdds (rate s u.val v.val gain.val left.val right.val p)=(4:ℝ)^(2*s.re) := by
  let t := u.val/(u.val+v.val)
  let d := v.val/(u.val+v.val)
  have ht : 0<t := div_pos u.property (add_pos u.property v.property)
  have hd : 0<d := div_pos v.property (add_pos u.property v.property)
  have a : binomial u.val v.val 2 0=t^2 := by simp [binomial,t]
  have b : binomial u.val v.val 1 1=2*(t*d) := by norm_num [binomial,t,d,Nat.choose_succ_succ]
  have c : binomial u.val v.val 0 2=d^2 := by simp [binomial,d]
  have base : (2*(t*d))^2/(t^2*d^2)=(4:ℝ) :=
    (div_eq_iff (mul_ne_zero (pow_ne_zero _ ht.ne') (pow_ne_zero _ hd.ne'))).mpr (by ring)
  simp only [squareOdds,rate_formula s u.property v.property,a,b,c,pow_zero,pow_one,mul_one]
  rw [cancel_gain gain.property left.property right.property
    (rpow_pos_of_pos (pow_pos ht 2) _) (rpow_pos_of_pos (pow_pos hd 2) _),
    power_ratio _ (pow_pos ht 2) (mul_pos (by norm_num) (mul_pos ht hd)) (pow_pos hd 2),base]

#print axioms rate_formula
#print axioms square_odds

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest
