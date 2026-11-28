import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement.Support

/-! # Marginal weights of the two physical Schmidt branches -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement

open Finset Real Collisions

def vacuumWeight (s : ℂ) (N : ℕ) (z : SplitParameter) := probability 1 s N (fun _ => z) 1

theorem vacuum_pos (s : ℂ) (N : ℕ) (z : SplitParameter) : 0<vacuumWeight s N z := by
  rw [vacuumWeight,probability_eq,pow_one]
  exact div_pos (powerMass_pos _ _) (powerMass_pos _ _)

private theorem prime_sum (b : ℝ) (N : ℕ) : ∑ p : PrimeAt N, finiteProbability b N p.val=1 := by
  have term (p : PrimeAt N) : finiteProbability b N p.val=(p.val:ℝ)^(b-1)/powerMass b N := by
    rw [finiteProbability,packetTerm,if_pos p.property]
  simp only [term,←sum_div]
  rw [sum_coe_sort (primes (cutoff N)) (fun p : ℕ => (p:ℝ)^(b-1))]
  exact div_self (powerMass_pos b N).ne'

theorem row_mass (s : ℂ) (N : ℕ) (z : SplitParameter) : mass (vacuumRow s N z)=vacuumWeight s N z := by
  have term (p : PrimeAt N) : ‖vacuumRow s N z p‖^2=
      finiteProbability (1-2*s.re-1) N p.val*vacuumWeight s N z := by
    change ‖splitIsometry z (retained 1 s N (fun _ => z) 0) (1,primeLabel p)‖^2=_
    rw [retained_step 1 s N (fun _ => z) 0]
    apply (div_eq_iff (vacuum_pos s N z).ne').mp
    simpa only [zero_add,vacuumWeight,Nat.cast_one] using posterior s N p (fun _ => z) 1
  simp only [mass,term,←sum_mul,prime_sum,one_mul]

private theorem prepared_mass (s : ℂ) (N : ℕ) (z : SplitParameter) :
    ∑ p : PrimeAt N, ‖prepared s N z (primeLabel p)‖^2=1 := by
  have term (p : PrimeAt N) : ‖prepared s N z (primeLabel p)‖^2=
      finiteProbability (1-2*s.re) N p.val := by
    simpa only [prepared,initial_mass,div_one,Nat.cast_zero,sub_zero] using posterior s N p (fun _ => z) 0
  simp only [term,prime_sum]

/-- The vacuum row carries one of the p residue outcomes on shell p. -/
private theorem counted_row (s : ℂ) (N : ℕ) (z : SplitParameter) (p : PrimeAt N) :
    (p.val:ℝ)*‖vacuumRow s N z p‖^2=‖prepared s N z (primeLabel p)‖^2 := by
  have unit : (p.val:ℝ)*‖heat z.val (primeLabel p)‖^2=1 := by
    change ((primeLabel p).val:ℝ)*‖heat z.val (primeLabel p)‖^2=1
    rw [←shellMass_eq,shellMass,z.property,show (1:ℝ)-2*(1/2)=0 by ring,zero_mul,exp_zero]
  rw [vacuumRow,output,vacuum_apply,norm_mul,mul_pow,←mul_assoc,unit,one_mul]

/-- The column carries the remaining p−1 residues of prime order. -/
private theorem counted_column (s : ℂ) (N : ℕ) (z : SplitParameter) (p : PrimeAt N) :
    ‖vacuumColumn s N z p‖^2=((p.val:ℝ)-1)*‖vacuumRow s N z p‖^2 := by
  have hp := (Nat.mem_primesBelow.mp p.property).2
  have tot : ((primeLabel p).val.totient:ℝ)=(p.val:ℝ)-1 := by
    change (p.val.totient:ℝ)=_
    rw [Nat.totient_prime hp,Nat.cast_sub hp.pos,Nat.cast_one]
  change ‖channel z.val (primeLabel p*1) (primeLabel p).val * prepared s N z (primeLabel p*1)‖^2=_
  rw [mul_one,norm_mul,mul_pow,channel_norm_sq,tot,vacuumRow,output,vacuum_apply,norm_mul,mul_pow,mul_assoc]

theorem column_mass (s : ℂ) (N : ℕ) (z : SplitParameter) : mass (vacuumColumn s N z)=1-vacuumWeight s N z := by
  have total : mass (vacuumRow s N z)+mass (vacuumColumn s N z)=1 := by
    rw [mass,mass,←sum_add_distrib,←prepared_mass s N z]
    refine sum_congr rfl fun p _ => ?_
    rw [counted_column,←counted_row s N z p]
    ring
  rw [row_mass] at total
  linarith only [total]

theorem vacuum_le_half (s : ℂ) (N : ℕ) (z : SplitParameter) : vacuumWeight s N z≤1/2 := by
  have twice : 2*mass (vacuumRow s N z)≤1 := by
    rw [mass,mul_sum,←prepared_mass s N z]
    refine sum_le_sum fun p _ => ?_
    rw [←counted_row s N z p]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mem_primesBelow.mp p.property).2.two_le) (sq_nonneg _)
  rw [row_mass] at twice
  linarith only [twice]

#print axioms row_mass
#print axioms column_mass
#print axioms vacuum_le_half

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement
