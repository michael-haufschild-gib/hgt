import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution.Packet

/-! # Vacuum dominance far from the critical line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution

open Filter Finset Real
open scoped Topology

private theorem packet_lt (p : Nat.Primes) (i : States p) : packet p i < 27 := by
  let f (k : ℕ) : ℕ := if k<27 then 0 else 1
  have total : (∑ j, f (packet p j))=0 := by rw [packet_sum]; simp [f]
  have le := single_le_sum (f := fun j => f (packet p j)) (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [total] at le
  by_contra h
  simp only [f,if_neg h] at le
  omega

/-- Only the vacuum survives when the reflection difference is divided
by the exponential of the greatest absolute centered energy. -/
theorem vacuum_limit (p q : Nat.Primes) :
    Tendsto (fun d => exp (-(27/2*log q.val)*d)*reading p q d) atTop (𝓝 (-(p.val : ℝ))) := by
  let L := log q.val
  have hL : 0<L := log_pos_prime q
  let f (k : ℕ) (d : ℝ) := exp (((k : ℝ)-27)*L*d)-exp ((-(k : ℝ))*L*d)
  have decay (c : ℝ) (hc : c<0) : Tendsto (fun d : ℝ => exp (c*d)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc)
  have term (k : ℕ) (hk : k<27) : Tendsto (f k) atTop (𝓝 (if k=0 then -1 else 0)) := by
    have hreal : (k : ℝ)<27 := by exact_mod_cast hk
    have left := decay _ (mul_neg_of_neg_of_pos (sub_neg.mpr hreal) hL)
    by_cases hz : k=0
    · subst k
      simpa only [f,Nat.cast_zero,neg_zero,zero_mul,exp_zero,if_true,sub_zero,zero_sub] using
        left.sub (tendsto_const_nhds (x := (1 : ℝ)))
    · have hp : 0<(k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
      simpa only [f,if_neg hz,sub_self] using
        left.sub (decay _ (mul_neg_of_neg_of_pos (neg_neg_of_pos hp) hL))
  have total := tendsto_finsetSum univ (fun i _ => term (packet p i) (packet_lt p i))
  have vac : (∑ i, (if packet p i=0 then (-1 : ℝ) else 0))= -(p.val : ℝ) := by
    rw [packet_sum p (fun k => if k=0 then (-1 : ℝ) else 0)]
    norm_num
  rw [vac] at total
  apply total.congr' (Eventually.of_forall fun d => ?_)
  rw [(readings p q d).1,oddTrace,mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [oddTerm,mul_sub,←exp_add,spectrum,centered_occupation,f,L]
  congr 1 <;> congr 1 <;> ring

/-- The absolute value reading diverges along the positive damping ray. -/
theorem reading_unbounded (p q : Nat.Primes) :
    Tendsto (fun d => |reading p q d|) atTop atTop := by
  let b := 27/2*log q.val
  have hb : 0<b := mul_pos (by norm_num) (log_pos_prime q)
  have hp : 0<(p.val : ℝ) := Nat.cast_pos.mpr p.property.pos
  have lim : Tendsto (fun d => exp (-b*d)*|reading p q d|) atTop (𝓝 (p.val : ℝ)) := by
    simpa only [b,abs_mul,abs_of_pos (exp_pos _),abs_neg,abs_of_pos hp] using (vacuum_limit p q).abs
  have growth : Tendsto (fun d : ℝ => exp (b*d)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  apply (growth.atTop_mul_pos hp lim).congr' (Eventually.of_forall fun d => ?_)
  rw [←mul_assoc,←exp_add,neg_mul,add_neg_cancel,exp_zero,one_mul]

#print axioms vacuum_limit
#print axioms reading_unbounded

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution
