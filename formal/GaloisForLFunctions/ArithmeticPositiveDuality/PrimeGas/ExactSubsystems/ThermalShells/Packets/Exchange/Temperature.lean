import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange.Gibbs

/-! # Strict energy discrimination by prime collisions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange

open Finset Real

def primeEnergy (p : Nat.Primes) := energy (quantum p)

private theorem primeEnergy_injective : Function.Injective primeEnergy := by
  intro p q h
  have he := congrArg exp h
  simp only [primeEnergy,energy,quantum,label_one_quantum,exp_log (Nat.cast_pos.mpr p.property.pos),
    exp_log (Nat.cast_pos.mpr q.property.pos)] at he
  exact Subtype.ext (Nat.cast_injective he)

private theorem atom_exp (b : ℝ) (p : Nat.Primes) : atom b p=exp (-(b*primeEnergy p)) := by
  simp only [atom,weight,primeEnergy,neg_mul]

/-- Cross-multiplied difference between one-prime energy means at b and 2b. -/
def cross (S : Finset Nat.Primes) (b : ℝ) :=
  firstMoment S b primeEnergy*singleZ S (2*b)-firstMoment S (2*b) primeEnergy*singleZ S b

private def kernel (b : ℝ) (p q : Nat.Primes) :=
  atom b p*atom b q*((b*primeEnergy p-b*primeEnergy q)*(atom b q-atom b p))

private theorem gap_pos {x y : ℝ} (h : x ≠ y) :
    0 < (x-y)*(exp (-y)-exp (-x)) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr h) (sub_neg.mpr (exp_lt_exp.mpr (neg_lt_neg h)))
  · exact mul_pos (sub_pos.mpr h) (sub_pos.mpr (exp_lt_exp.mpr (neg_lt_neg h)))

private theorem kernel_pos {b : ℝ} {p q : Nat.Primes} (h : b*primeEnergy p ≠ b*primeEnergy q) :
    0 < kernel b p q := by
  unfold kernel
  rw [atom_exp,atom_exp]
  exact mul_pos (mul_pos (exp_pos _) (exp_pos _)) (gap_pos h)

private theorem kernel_nonneg (b : ℝ) (p q : Nat.Primes) : 0 ≤ kernel b p q := by
  by_cases h : b*primeEnergy p=b*primeEnergy q
  · simp only [kernel,h,sub_self,zero_mul,mul_zero,le_refl]
  · exact (kernel_pos h).le

private theorem covariance_sum (S : Finset Nat.Primes) (b : ℝ) :
    (∑ p ∈ S,∑ q ∈ S,kernel b p q) = 2*(b*cross S b) := by
  calc _ = b*(∑ p ∈ S,∑ q ∈ S,
               ((atom b p*primeEnergy p)*atom b q^2 - (atom b p^2*primeEnergy p)*atom b q -
                atom b p*(atom b q^2*primeEnergy q) + atom b p^2*(atom b q*primeEnergy q))) := by
             rw [mul_sum]
             apply sum_congr rfl
             intro p _
             rw [mul_sum]
             apply sum_congr rfl
             intro q _
             unfold kernel
             ring
       _ = _ := by
             simp only [sum_add_distrib,sum_sub_distrib,sum_separable,cross,firstMoment,singleZ,doubled_atom]
             ring

/-- Distinct prime energies make temperature discrimination strict at every nonzero b. -/
theorem strict_cross {S : Finset Nat.Primes} (hs : S.Nontrivial) {b : ℝ} (hb : b≠0) :
    0 < b*cross S b := by
  obtain ⟨p,hp,q,hq,hpq⟩ := hs
  have hk := kernel_pos (b:=b) (p:=p) (q:=q)
    (fun h => hpq (primeEnergy_injective (mul_left_cancel₀ hb h)))
  have i := single_le_sum (s:=S) (f:=kernel b p) (fun r _ => kernel_nonneg b p r) hq
  have j := single_le_sum (s:=S) (f:=fun r => ∑ v ∈ S,kernel b r v)
    (fun r _ => sum_nonneg fun v _ => kernel_nonneg b r v) hp
  have hh := hk.trans_le (i.trans j)
  rw [covariance_sum] at hh
  exact (mul_pos_iff_of_pos_left two_pos).mp hh

#print axioms strict_cross

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange
