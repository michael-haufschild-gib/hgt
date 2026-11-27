import GaloisForLFunctions.PNTPlus.Consequences
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Phase density along the tail of the elementary prime spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum

open Filter Real Set

/-- A narrow multiplicative prime interval yields a prescribed angular
window arbitrarily far out in the elementary energy spectrum. -/
theorem phase_window (t θ η : ℝ) (ht : 0 < t) (hη : 0 < η) (N : ℕ) :
    ∃ (p : Nat.Primes) (m : ℕ), N < p.val ∧
      0 < t*log p.val-(θ+(m : ℝ)*(2*π)) ∧ t*log p.val-(θ+(m : ℝ)*(2*π)) < η := by
  let width := exp (η/t)-1
  have hw : 0 < width := sub_pos.mpr (one_lt_exp_iff.mpr (div_pos hη ht))
  obtain ⟨A,hA⟩ := eventually_atTop.mp (prime_between hw)
  let R := max A (N : ℝ)
  obtain ⟨m,hm⟩ := exists_nat_gt ((t*R-θ)/(2*π))
  have lift := (div_lt_iff₀ two_pi_pos).mp hm
  let v := (θ+(m : ℝ)*(2*π))/t
  have large : R < v := (lt_div_iff₀ ht).mpr (by linarith only [lift])
  have past : R < exp v := large.trans_le (by linarith only [add_one_le_exp v])
  obtain ⟨p,hp,low,high⟩ := hA (exp v) ((le_max_left _ _).trans past.le)
  have cut : (N : ℝ)<(p : ℝ) := (le_max_right _ _).trans_lt (past.trans low)
  have bottom := log_lt_log (exp_pos v) low
  rw [log_exp] at bottom
  have width_eq : 1+width=exp (η/t) := by dsimp only [width]; ring
  rw [width_eq,←exp_add] at high
  have top := log_lt_log (Nat.cast_pos.mpr hp.pos) high
  rw [log_exp] at top
  have cancel : v*t=θ+(m : ℝ)*(2*π) := div_mul_cancel₀ _ ht.ne'
  have b := mul_lt_mul_of_pos_right bottom ht
  have u := mul_lt_mul_of_pos_right top ht
  rw [add_mul,div_mul_cancel₀ _ ht.ne',cancel] at u
  rw [cancel] at b
  exact ⟨⟨p,hp⟩,m,by exact_mod_cast cut,by linarith only [b],by linarith only [u]⟩

/-- Elementary radial normalization leaves the absolute cosine of the prime phase. -/
def strength (p : Nat.Primes) (t : ℝ) := |cos (t*log p.val)|

theorem strength_le (p : Nat.Primes) (t : ℝ) : strength p t ≤ 1 := abs_cos_le_one _

/-- At each nonzero height every normalized reading between zero and
one is approached by primes above every prescribed energy cutoff. -/
theorem tail_approximates (t r : ℝ) (ht : t≠0) (hr : r ∈ Icc (0 : ℝ) 1)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Nat.Primes, N < p.val ∧ |strength p t-r| < ε := by
  let θ := arccos r
  have ct : cos θ=r := cos_arccos (by linarith only [hr.1]) hr.2
  obtain ⟨p,m,cut,lo,hi⟩ := phase_window |t| θ ε (abs_pos.mpr ht) hε N
  have approx := abs_cos_sub_cos_le (|t| *log p.val) (θ+(m : ℝ)*(2*π))
  rw [cos_add_nat_mul_two_pi,ct,abs_of_pos lo] at approx
  have evenPhase : cos (|t| *log p.val)=cos (t*log p.val) := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,neg_mul,cos_neg]
  rw [evenPhase] at approx
  have bound := abs_abs_sub_abs_le_abs_sub (cos (t*log p.val)) r
  rw [abs_of_nonneg hr.1] at bound
  exact ⟨p,cut,bound.trans_lt (approx.trans_lt hi)⟩

theorem near_one (t c : ℝ) (hc : c < 1) (N : ℕ) :
    ∃ p : Nat.Primes, N < p.val ∧ c < strength p t := by
  by_cases hz : t=0
  · obtain ⟨p,large,prime⟩ := Nat.exists_infinite_primes (N+1)
    exact ⟨⟨p,prime⟩,large,by simpa only [hz,strength,zero_mul,cos_zero,abs_one] using hc⟩
  · obtain ⟨p,cut,near⟩ := tail_approximates t 1 hz ⟨zero_le_one,le_rfl⟩ N (1-c) (sub_pos.mpr hc)
    exact ⟨p,cut,by linarith only [(abs_lt.mp near).1]⟩

/-- The entire tail has unit optimal gain at every physical height. -/
theorem tail_supremum (t : ℝ) (N : ℕ) :
    IsLUB {x : ℝ | ∃ p : Nat.Primes, N < p.val ∧ x=strength p t} 1 := by
  constructor
  · rintro _ ⟨p,_,rfl⟩; exact strength_le p t
  · intro c bound
    by_contra! small
    obtain ⟨p,cut,high⟩ := near_one t c small N
    exact high.not_ge (bound (show strength p t ∈ {x : ℝ | ∃ q : Nat.Primes, N < q.val ∧
      x=strength q t} from ⟨p,cut,rfl⟩))

#print axioms phase_window
#print axioms strength_le
#print axioms tail_approximates
#print axioms near_one
#print axioms tail_supremum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum
