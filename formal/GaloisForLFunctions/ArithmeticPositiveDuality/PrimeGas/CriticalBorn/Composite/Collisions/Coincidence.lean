import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Conditional

/-! # Independent prime replicas conditioned on a common outcome -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions

open Finset Real

/-- Power sum of elementary Born probabilities. Positive r counts the copies. -/
def coincidence (r : ℕ) (a : ℝ) (N : ℕ) := ∑ p, (Ordinary.primeProbability a N p)^r

/-- After the first prime is chosen, exactly the constant remaining tuple
retains the same label in every copy. -/
theorem coincidence_event (m : ℕ) (a : ℝ) (N : ℕ) :
    (∑ p : PrimeAt N, ∑ u : Fin m → PrimeAt N, if u=(fun _ => p) then
      Ordinary.primeProbability a N p*_root_.RHTower.tupleWeight (Ordinary.primeProbability a N) u else 0)=
      coincidence (m+1) a N := by
  classical
  simp [coincidence,_root_.RHTower.tupleWeight,pow_succ']

/-- Taking the r-th power of an elementary weight multiplies its inverse
temperature by r. The power index contains the shift by one. -/
def replicaIndex (r : ℕ) (a : ℝ) := 1+(r:ℝ)*(a-1)

theorem packet_power {r : ℕ} (hr : 0<r) (a : ℝ) (N n : ℕ) :
    (packetTerm a N n)^r=packetTerm (replicaIndex r a) N n := by
  by_cases h : n∈primes (cutoff N)
  · have hp := (Nat.cast_pos.mpr (Nat.mem_primesBelow.mp h).2.pos : 0<(n:ℝ))
    rw [packetTerm,if_pos h,packetTerm,if_pos h,rpow_def_of_pos hp,rpow_def_of_pos hp,←exp_nat_mul]
    congr 1
    unfold replicaIndex
    ring
  · simp only [packetTerm,if_neg h,zero_pow hr.ne']

private theorem in_packet (a : ℝ) (N : ℕ) (p : PrimeAt N) :
    Ordinary.primeProbability a N p=finiteProbability a N p.val := by
  rw [Ordinary.primeProbability,finiteProbability,packetTerm,if_pos p.property,
    rpow_def_of_pos (Nat.cast_pos.mpr (Nat.mem_primesBelow.mp p.property).2.pos),mul_comm]
  rfl

theorem coincidence_eq {r : ℕ} (hr : 0<r) (a : ℝ) (N : ℕ) :
    coincidence r a N=powerMass (replicaIndex r a) N/(powerMass a N)^r := by
  have term (p : PrimeAt N) : (Ordinary.primeProbability a N p)^r=
      (p.val:ℝ)^(replicaIndex r a-1)/(powerMass a N)^r := by
    rw [in_packet,finiteProbability,div_pow,packet_power hr,packetTerm,if_pos p.property]
  simp only [coincidence,term,←sum_div]
  exact congrArg (fun x : ℝ => x/(powerMass a N)^r)
    (sum_coe_sort (primes (cutoff N)) (fun p : ℕ => (p:ℝ)^(replicaIndex r a-1)))

/-- Conditional label probability after all r replicas read the same prime. -/
def conditional (r : ℕ) (a : ℝ) (N n : ℕ) := (finiteProbability a N n)^r/coincidence r a N

theorem conditional_eq {r : ℕ} (hr : 0<r) (a : ℝ) (N n : ℕ) :
    conditional r a N n=finiteProbability (replicaIndex r a) N n := by
  change (packetTerm a N n/powerMass a N)^r/coincidence r a N=
    packetTerm (replicaIndex r a) N n/powerMass (replicaIndex r a) N
  rw [div_pow,packet_power hr,coincidence_eq hr,div_div_div_cancel_right₀ (pow_ne_zero r (powerMass_pos a N).ne')]

#print axioms coincidence_event
#print axioms packet_power
#print axioms coincidence_eq
#print axioms conditional_eq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions
