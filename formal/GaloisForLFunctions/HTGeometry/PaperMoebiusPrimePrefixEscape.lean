import GaloisForLFunctions.HTGeometry.PaperMoebiusPrimeEnergy
import Mathlib.Data.Nat.Prime.Infinite

/-!+# Finite-prefix escape of the literal prime-core Möbius action

The proven additive action at time one retains precisely the coefficients divisible
by its prime. Choosing a prime beyond the cutoff annihilates the entire finite
Laplace pencil and Gamma-Hankel energy, although the source is nonzero at that prime.
The prime depends on the cutoff; these identities do not supply a cofinal bound
for one fixed arithmetic source.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower Filter

noncomputable section

/-- Time one annihilates every coefficient strictly below the chosen prime. -/
theorem paperMoebiusPrimeTransport_time_one_below (p : Nat.Primes)
    (n : Fin (p : ℕ)) : paperMoebiusPrimeTransport p 1 n = 0 := by
  by_cases hn : (n : ℕ) = 0
  · simp [hn]
  have hndiv : ¬(p : ℕ) ∣ (n : ℕ) := fun h =>
    (not_le_of_gt n.isLt) (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h)
  simp [paperMoebiusPrimeTransport_apply, hndiv]

/-- The first surviving coefficient is exactly minus one, not an unproved tail. -/
theorem paperMoebiusPrimeTransport_time_one_prime (p : Nat.Primes) :
    paperMoebiusPrimeTransport p 1 p = -1 := by
  simp [paperMoebiusPrimeTransport_apply, ArithmeticFunction.moebius_apply_prime p.property]

/-- A prime beyond each cutoff, selected from infinitude without prime computation. -/
def paperEscapingPrime (N : ℕ) : Nat.Primes :=
  ⟨(Nat.exists_infinite_primes (N + 1)).choose,
    (Nat.exists_infinite_primes (N + 1)).choose_spec.2⟩

theorem paperEscapingPrime_gt (N : ℕ) : N < (paperEscapingPrime N : ℕ) :=
  (Nat.exists_infinite_primes (N + 1)).choose_spec.1

/-- Every coefficient through the requested cutoff vanishes. -/
theorem paperMoebiusEscapingPrime_coefficient (N : ℕ) (n : Fin (N + 1)) :
    paperMoebiusPrimeTransport (paperEscapingPrime N) 1 n = 0 :=
  paperMoebiusPrimeTransport_time_one_below _
    ⟨n, lt_of_le_of_lt (Nat.le_of_lt_succ n.isLt) (paperEscapingPrime_gt N)⟩

/-- The escaping family never becomes the zero arithmetic function. -/
theorem paperMoebiusEscapingPrime_ne_zero (N : ℕ) :
    paperMoebiusPrimeTransport (paperEscapingPrime N) 1 ≠ 0 := by
  intro h
  have hp := paperMoebiusPrimeTransport_time_one_prime (paperEscapingPrime N)
  rw [h] at hp
  simp at hp

private theorem realTransport_prefix_zero (p : Nat.Primes) (N : Fin (p : ℕ)) (n : ℕ)
    (hn : n ∈ Finset.range N) :
    paperMoebiusPrimeRealTransport p 1 n = 0 := by
  have h := paperMoebiusPrimeTransport_time_one_below p
    ⟨n + 1, lt_of_le_of_lt (Nat.succ_le_of_lt (Finset.mem_range.mp hn)) N.isLt⟩
  simpa [paperMoebiusPrimeRealTransport] using congrArg Complex.re h

/-- Any cutoff below the retained prime has an identically zero Laplace pencil. -/
theorem paperMoebiusPrimeTransport_time_one_laplace_below (p : Nat.Primes)
    (N : Fin (p : ℕ)) (x : ℝ) :
    finiteRealLaplacePencil (paperMoebiusPrimeRealTransport p 1) N x = 0 := by
  unfold finiteRealLaplacePencil
  exact Finset.sum_eq_zero fun n hn => by rw [realTransport_prefix_zero p N n hn, zero_mul]

/-- Any cutoff below the retained prime has zero full Gamma-Hankel energy. -/
theorem paperMoebiusPrimeTransport_time_one_energy_below (p : Nat.Primes)
    (N : Fin (p : ℕ)) (r : ℝ) : paperMoebiusPrimeEnergy p 1 N r = 0 := by
  unfold paperMoebiusPrimeEnergy finiteGammaHankelEnergy
  rw [mul_eq_zero]
  right
  exact Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun n _ => by
    rw [realTransport_prefix_zero p N m hm, zero_mul, zero_div]

/-- The actual finite Laplace pencil vanishes at every real argument. -/
theorem paperMoebiusEscapingPrime_laplace (N : ℕ) (x : ℝ) :
    finiteRealLaplacePencil (paperMoebiusPrimeRealTransport (paperEscapingPrime N) 1)
      N x = 0 :=
  paperMoebiusPrimeTransport_time_one_laplace_below _ ⟨N, paperEscapingPrime_gt N⟩ x

/-- The full finite energy, with all mixed terms retained, vanishes at every exponent. -/
theorem paperMoebiusEscapingPrime_energy (N : ℕ) (r : ℝ) :
    paperMoebiusPrimeEnergy (paperEscapingPrime N) 1 N r = 0 :=
  paperMoebiusPrimeTransport_time_one_energy_below _ ⟨N, paperEscapingPrime_gt N⟩ r

/-- Each fixed coefficient is eventually zero, despite every source being nonzero. -/
theorem paperMoebiusEscapingPrime_eventually_zero (n : ℕ) :
    ∀ᶠ N in atTop, paperMoebiusPrimeTransport (paperEscapingPrime N) 1 n = 0 := by
  filter_upwards [eventually_ge_atTop n] with N hN
  exact paperMoebiusEscapingPrime_coefficient N ⟨n, Nat.lt_succ_of_le hN⟩

end

end GaloisForLFunctions.HTGeometry
