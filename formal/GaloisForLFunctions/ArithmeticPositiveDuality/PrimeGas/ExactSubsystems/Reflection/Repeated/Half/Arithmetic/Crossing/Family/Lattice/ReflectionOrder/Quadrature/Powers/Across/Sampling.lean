import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Recurrence
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Thermal

/-! # Sampling finite harmonic blocks on the prime torus -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across

open Finset Set Real Filter
open scoped Topology

variable {F : Finset Nat.Primes} [Nonempty F] {J : F → Type*}
  [∀ p, Fintype (J p)] [∀ p, Nonempty (J p)]

/-- Weighted maximum at independently chosen phases. Each harmonic
belongs to the single circle of its elementary prime. -/
def score (k : (p : F) → J p → ℕ+) (w : (p : F) → J p → ℝ) (θ : F → ℝ) :=
  peak fun p => peak fun i => w p i * |cos ((k p i : ℝ)*θ p)|

/-- Every independent angular score is approximated, with bounded gaps,
by the same score at a single physical height. -/
theorem score_returns (k : (p : F) → J p → ℕ+) (w : (p : F) → J p → ℝ)
    (θ : F → ℝ) (ε : ℝ) (hε : 0<ε) :
    ∃ L : ℝ, 0<L ∧ ∀ T : ℝ, ∃ t ∈ Set.Icc T (T+L),
      |score k w (fun p => t*log p.val.val)-score k w θ|<ε := by
  let f (z : F → ℂ) := peak fun p => peak fun i => w p i * |((z p)^(k p i).val).re|
  have cont : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply peak_limit
    intro p
    apply peak_limit
    intro i
    exact (continuous_const.mul (Complex.continuous_re.comp
      ((continuous_apply p).pow (k p i).val)).abs).continuousAt
  have eval (a : F → ℝ) : f (fun p => unitPhase (a p))=score k w a := by
    simp only [f,score,real_power]
  simpa only [eval] using returns F θ f cont ε hε

/-- Taking the infimum over actual heights gives the same lower bounds
as allowing all elementary phases to vary independently. -/
theorem all_heights (k : (p : F) → J p → ℕ+) (w : (p : F) → J p → ℝ) (K : ℝ) :
    (∀ t : ℝ, K ≤ score k w (fun p => t*log p.val.val)) ↔ ∀ θ, K ≤ score k w θ := by
  constructor
  · intro bound θ
    by_contra! fail
    obtain ⟨L,_,visit⟩ := score_returns k w θ (K-score k w θ) (sub_pos.mpr fail)
    obtain ⟨t,_,near⟩ := visit 0
    have lt := (abs_lt.mp near).2
    linarith only [bound t,lt]
  · exact fun bound t => bound _

#print axioms score_returns
#print axioms all_heights

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across
