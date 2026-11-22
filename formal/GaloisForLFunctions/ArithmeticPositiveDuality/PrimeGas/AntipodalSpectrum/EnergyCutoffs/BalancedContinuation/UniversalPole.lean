import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedContinuation.PartitionPoles
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.JointPrimeReading

/-!
# The unique pole common to the balanced partitions

At primes two and three simultaneous scale returns give the vacuum values
of both elementary heat amplitudes. Their joint injectivity fixes the real
critical temperature at every refinement.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation

private theorem prime_log_radix (p : Nat.Primes) (j : ℕ) :
    (logRadix (primeHalfTurnClock p) j).val = (2:ℝ)^j * energy ⟨p.val,p.property.pos⟩ := by
  change energy (tailRadix (primeHalfTurnClock p) j) = _
  induction j with
  | zero => rw [prime_half_turn_radix,pow_zero,one_mul]
  | succ j ih => rw [tailRadix_succ,pow_two,energy_mul,ih,pow_succ]; ring

private def scaledParameter (j : ℕ) (s : ℂ) := (2:ℂ)^(j+1)*(s-((1/2:ℝ):ℂ))

private theorem prime_return (p : Nat.Primes) (j : ℕ) (s : {z : ℂ // -(1/2) < z.re})
    (hp : meromorphicOrderAt (continuation (primeHalfTurnClock p) j) s.val < 0) :
    heat (scaledParameter j s.val) ⟨p.val,p.property.pos⟩ = 1 := by
  obtain ⟨k,hk,_⟩ := (pole_locus (primeHalfTurnClock p) j s).mp hp
  have he := (scaleFactor_zero_iff (logRadix (primeHalfTurnClock p) j) s.val).mpr ⟨k,hk⟩
  rw [scaleFactor,sub_eq_zero,prime_log_radix,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat] at he
  refine Eq.trans ?_ he.symm
  rw [heat,scaledParameter,pow_succ]
  congr 1
  ring

private theorem all_real_poles (t : ExceptionalTime) (j : ℕ) :
    meromorphicOrderAt (continuation t j) ((1/2:ℝ):ℂ) < 0 := by
  have hp := first_clock_poles t j ⟨0,Or.inl rfl⟩
  have hpoint : point t j 0 = ((1/2:ℝ):ℂ) := by apply Complex.ext <;> simp [clockPoint]
  rw [hpoint] at hp
  rw [hp]
  exact WithTop.coe_lt_coe.mpr (by norm_num : (-1:ℤ) < 0)

/-- Simultaneous poles at prime-two and prime-three clocks characterize the real half-temperature. -/
theorem two_prime_common_pole (j : ℕ) (s : {z : ℂ // -(1/2) < z.re}) :
    (meromorphicOrderAt (continuation (primeHalfTurnClock ⟨2,Nat.prime_two⟩) j) s.val < 0 ∧
     meromorphicOrderAt (continuation (primeHalfTurnClock ⟨3,Nat.prime_three⟩) j) s.val < 0) ↔
      s.val = ((1/2:ℝ):ℂ) := by
  constructor
  · rintro ⟨h₂,h₃⟩
    have a : heat (scaledParameter j s.val) 2 = 1 := prime_return ⟨2,Nat.prime_two⟩ j s h₂
    have b : heat (scaledParameter j s.val) 3 = 1 := prime_return ⟨3,Nat.prime_three⟩ j s h₃
    have hz : scaledParameter j s.val = 0 := by
      apply two_prime_heat_injective
      change (heat (scaledParameter j s.val) 2,heat (scaledParameter j s.val) 3) = (heat 0 2,heat 0 3)
      rw [a,b]
      simp [heat]
    change (2:ℂ)^(j+1)*(s.val-((1/2:ℝ):ℂ)) = 0 at hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ two_ne_zero))
  · intro he
    rw [he]
    exact ⟨all_real_poles _ j,all_real_poles _ j⟩

/-- The unique pole in the continuation half-plane observed by every exceptional clock. -/
theorem universal_balanced_pole (j : ℕ) (s : {z : ℂ // -(1/2) < z.re}) :
    (∀ t : ExceptionalTime, meromorphicOrderAt (continuation t j) s.val < 0) ↔
      s.val = ((1/2:ℝ):ℂ) := by
  constructor
  · intro hall
    exact (two_prime_common_pole j s).mp ⟨hall _,hall _⟩
  · intro he t
    rw [he]
    exact all_real_poles t j

#print axioms two_prime_common_pole
#print axioms universal_balanced_pole

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation
