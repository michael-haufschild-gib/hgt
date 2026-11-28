import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Branch

/-! # Which prime remains after repeated vacuum outputs -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum

open Real Collisions

private theorem single_multiplicity {x : ℝ} (p : PrimeAt x) :
    multiplicity 1 x (primeLabel p)=1 := by
  have h := Ordinary.multiplicity_injective (fun _ : Fin 1 => p)
    (fun i j _ => Subsingleton.elim i j)
  simpa [productLabel] using h

/-- A successful vacuum observation lowers the elementary power index by
one. This identifies the posterior on actual prime coordinates. -/
theorem posterior (s : ℂ) (N : ℕ) (p : PrimeAt N) (z : ℕ → SplitParameter) (j : ℕ) :
    ‖retained 1 s N z j (primeLabel p)‖^2 / probability 1 s N z j=
      finiteProbability (1-2*s.re-(j:ℝ)) N p.val := by
  have ix : 1-2*(s+shift z j).re=1-2*s.re-(j:ℝ) := by rw [Complex.add_re,shift_re]; ring
  rw [probability_eq,pow_one]
  change ‖(‖wave 1 s N‖:ℂ)⁻¹ * wave 1 (s+shift z j) N (primeLabel p)‖^2 / _=_
  rw [norm_mul,mul_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),inv_pow,
    wave_mass,rawWave_sq,pow_one,wave_apply,single_multiplicity,Nat.cast_one,sqrt_one,Complex.ofReal_one,
    one_mul,Ordinary.heat_square,ix,finiteProbability,packetTerm,if_pos p.property,
    rpow_def_of_pos (Nat.cast_pos.mpr (Nat.mem_primesBelow.mp p.property).2.pos),
    mul_comm (log (p.val:ℝ)) (1-2*s.re-(j:ℝ)-1)]
  change _ * exp ((1-2*s.re-(j:ℝ)-1)*log (p.val:ℝ)) / _ = _
  field_simp [(powerMass_pos (1-2*s.re) N).ne',(powerMass_pos (1-2*s.re-(j:ℝ)) N).ne']

/-- At critical input the one-particle apparatus reproduces the common
prime distribution of j+1 independent coincident preparations exactly. -/
theorem posterior_replica (s : SplitParameter) (N : ℕ) (p : PrimeAt N) (z : ℕ → SplitParameter) (j : ℕ) :
    ‖retained 1 s.val N z j (primeLabel p)‖^2 / probability 1 s.val N z j=
      conditional (j+1) 0 N p.val := by
  rw [posterior,s.property,show (1:ℝ)-2*(1/2)=0 by ring,zero_sub,conditional_eq (Nat.succ_pos j)]
  congr 1
  unfold replicaIndex
  push_cast
  ring

#print axioms posterior
#print axioms posterior_replica

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum
