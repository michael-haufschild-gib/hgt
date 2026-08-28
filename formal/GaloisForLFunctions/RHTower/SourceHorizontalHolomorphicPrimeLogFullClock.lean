import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicPrimeLogZeroCondensation

/-!
# Full prime-log zero clock of the holomorphic SC packet

The zero-condensation module selects the first positive noncentral zero of each terminal-prime
Bockstein.  This companion records the complete integer clock proved on paper: every signed
prime Bockstein vanishes at `k π i / log p`, and every finite packet inherits the clock of its
terminal prime.  The selected moving zero is the `k = 1` member.
-/

namespace RHTower

open Complex

noncomputable section

/-- Integer `π i / log p` clock point of one holomorphic signed prime Bockstein. -/
def preDivisorHolomorphicPrimeClockPoint (k : ℤ) (p : Nat.Primes) : ℂ :=
  Complex.ofReal (Real.pi / Real.log (p.1 : ℝ)) * (k : ℂ) * Complex.I

/-- Every signed prime Bockstein vanishes on its complete integer `π i / log p` clock. -/
theorem preDivisorHolomorphicPrimeBockstein_clock
    (k : ℤ) (p : Nat.Primes) :
    preDivisorHolomorphicPrimeBockstein
      (preDivisorHolomorphicPrimeClockPoint k p) p = 0 := by
  have hlog : Real.log (p.1 : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast p.2.one_lt
  have harg :
      (Real.log (p.1 : ℝ) : ℂ) * preDivisorHolomorphicPrimeClockPoint k p =
        (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    rw [preDivisorHolomorphicPrimeClockPoint]
    calc
      (Real.log (p.1 : ℝ) : ℂ) *
          (Complex.ofReal (Real.pi / Real.log (p.1 : ℝ)) * (k : ℂ) * Complex.I) =
          Complex.ofReal
            (Real.log (p.1 : ℝ) * (Real.pi / Real.log (p.1 : ℝ))) *
              (k : ℂ) * Complex.I := by
            rw [Complex.ofReal_mul]
            ring
      _ = (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
        rw [mul_div_cancel₀ _ hlog]
        ring
  have hperiod :
      Complex.exp (-((k : ℂ) * ((Real.pi : ℂ) * Complex.I))) =
        Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
    calc
      Complex.exp (-((k : ℂ) * ((Real.pi : ℂ) * Complex.I))) =
          Complex.exp
            ((k : ℂ) * ((Real.pi : ℂ) * Complex.I) +
              ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
            congr 1
            push_cast
            ring
      _ = Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I)) *
          Complex.exp (((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
            rw [Complex.exp_add]
      _ = Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
            rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [preDivisorHolomorphicPrimeBockstein, harg, hperiod, sub_self, mul_zero]

/-- The selected moving zero is exactly the positive `k = 1` terminal-prime clock point. -/
theorem preDivisorHolomorphicPrimeClockPoint_one_terminal (m : ℕ) :
    preDivisorHolomorphicPrimeClockPoint 1
        (preDivisorRiggedPrimeHolomorphicTerminalPrime m) =
      preDivisorRiggedPrimeHolomorphicClockPoint m := by
  simp [preDivisorHolomorphicPrimeClockPoint,
    preDivisorRiggedPrimeHolomorphicClockPoint,
    preDivisorRiggedPrimeHolomorphicClockRate]

/-- Every finite SC packet inherits the complete integer clock of its terminal prime. -/
theorem preDivisorRiggedPrimeHolomorphicPacket_clock
    (m : ℕ) (k : ℤ) :
    preDivisorRiggedPrimeHolomorphicPacket m
      (preDivisorHolomorphicPrimeClockPoint k
        (preDivisorRiggedPrimeHolomorphicTerminalPrime m)) = 0 := by
  rw [preDivisorRiggedPrimeHolomorphicPacket]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last (m + 1)))
  simpa [preDivisorRiggedPrimeHolomorphicTerminalPrime] using
    preDivisorHolomorphicPrimeBockstein_clock k
      (preDivisorRiggedPrimeHolomorphicTerminalPrime m)

end

end RHTower
