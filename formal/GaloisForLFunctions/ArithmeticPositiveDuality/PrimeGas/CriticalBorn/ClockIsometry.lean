import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.OccupationNorm
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Classification

/-! # Norm recovery on the powers of a single prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Real
open GaloisForLFunctions.HTGeometry
open scoped Topology

/-- At prime clock time log p, the kth occupation of a prime q is read
as the kth power of its elementary phase. -/
theorem power_reading (p q : Nat.Primes) (k : ℕ) :
    heat ((log p.val : ℂ)*Complex.I) ((label (Finsupp.single q 1))^k) =
      (phase (log q.val) p.val : ℂ)^k := by
  have single : heat ((log p.val : ℂ)*Complex.I) (label (Finsupp.single q 1)) =
      (phase (log q.val) p.val : ℂ) := by
    rw [heat,energy,label_one_quantum,phase,Circle.coe_exp]
    congr 1
    push_cast
    ring
  induction k with
  | zero => simp [heat,energy]
  | succ k ih => rw [pow_succ,pow_succ,heat_mul,ih,single]

/-- All coherent preparations on the powers of any one prime recover
their Hilbert norm exactly at the unique composition isometry exponent. -/
theorem one_prime_norm_iff (q : Nat.Primes) (σ : ℝ) :
    (∀ d : ℕ →₀ ℂ, Tendsto (fun N => ‖synthesis (bornLaw σ (log q.val) N) d‖^2) atTop
      (𝓝 (‖finsuppCoefficientL2 d‖^2))) ↔ σ = 1/2 := by
  have ht := (log_pos (show (1:ℝ)<q.val by exact_mod_cast q.property.one_lt)).ne'
  exact (haar_iff_occupation_norms _).symm.trans (haar_iff_half σ ht)

theorem one_prime_norm_iff_split (q : Nat.Primes) (s : ℂ) :
    (∀ d : ℕ →₀ ℂ, Tendsto (fun N => ‖synthesis (bornLaw s.re (log q.val) N) d‖^2) atTop
      (𝓝 (‖finsuppCoefficientL2 d‖^2))) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x :=
  (one_prime_norm_iff q s.re).trans (split_isometric_iff s).symm

#print axioms power_reading
#print axioms one_prime_norm_iff
#print axioms one_prime_norm_iff_split

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
