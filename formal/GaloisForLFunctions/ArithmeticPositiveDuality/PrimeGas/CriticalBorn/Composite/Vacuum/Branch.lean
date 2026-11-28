import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Coincidence

/-! # The vacuum output of the isometric divisor split -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum

open Real

abbrev SplitParameter := {z : ℂ // z.re=1/2}

/-- Complex heat accumulated along a sequence of vacuum outcomes. -/
def shift (z : ℕ → SplitParameter) : ℕ → ℂ
  | 0 => 0
  | j+1 => shift z j+(z j).val

theorem shift_re (z : ℕ → SplitParameter) (j : ℕ) : (shift z j).re=(j:ℝ)/2 := by
  induction j with
  | zero => simp [shift]
  | succ j ih => rw [shift,Complex.add_re,ih,(z j).property,Nat.cast_succ]; ring

/-- The order-one fiber has degeneracy one. On this output the physical
isometry acts on every input coefficient by its original heat multiplier. -/
theorem vacuum_apply (z : SplitParameter) (f : Gas) (n : ℕ+) :
    splitIsometry z f (1,n)=heat z.val n*f n := by
  change channel z.val (1*n) 1*f (1*n)=_
  simp only [one_mul,channel,Nat.totient_one,Nat.cast_one,Real.sqrt_one,Complex.ofReal_one]

/-- Unnormalized branch after j successive vacuum observations. The initial
state in the m-excitation sector is normalized before the first split. -/
def retained (m : ℕ) (s : ℂ) (x : ℝ) (z : ℕ → SplitParameter) (j : ℕ) : Gas :=
  ((‖wave m s x‖:ℂ)⁻¹) • wave m (s+shift z j) x

theorem retained_step (m : ℕ) (s : ℂ) (x : ℝ) (z : ℕ → SplitParameter) (j : ℕ) (n : ℕ+) :
    splitIsometry (z j) (retained m s x z j) (1,n)=retained m s x z (j+1) n := by
  rw [vacuum_apply]
  change heat (z j).val n*((‖wave m s x‖:ℂ)⁻¹*wave m (s+shift z j) x n)=
    (‖wave m s x‖:ℂ)⁻¹*wave m (s+shift z (j+1)) x n
  rw [shift,←add_assoc,wave_apply,wave_apply,heat_add (s+shift z j) (z j).val]
  ring

def probability (m : ℕ) (s : ℂ) (x : ℝ) (z : ℕ → SplitParameter) (j : ℕ) :=
  ‖retained m s x z j‖^2

/-- All consecutive vacuum probabilities on actual integer product shells
factor into powers of the single-excitation mass ratio. -/
theorem probability_eq (m : ℕ) (s : ℂ) (x : ℝ) (z : ℕ → SplitParameter) (j : ℕ) :
    probability m s x z j=(powerMass (1-2*s.re-(j:ℝ)) x / powerMass (1-2*s.re) x)^m := by
  rw [probability,retained,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),
    mul_pow,inv_pow,wave_mass,wave_mass,rawWave_sq,rawWave_sq,Complex.add_re,shift_re,
    show 1-2*(s.re+(j:ℝ)/2)=1-2*s.re-(j:ℝ) by ring,div_pow]
  ring

theorem initial_mass (m : ℕ) (s : ℂ) (x : ℝ) (z : ℕ → SplitParameter) :
    probability m s x z 0=1 := by
  rw [probability_eq,Nat.cast_zero,sub_zero,div_self (powerMass_pos _ _).ne',one_pow]

/-- At critical input, m consecutive vacuum outputs on one excitation
give the same selected prime weights as coincidence of m+1 independent copies. -/
theorem vacuum_replica (s : SplitParameter) (z : ℕ → SplitParameter) (N j : ℕ) :
    probability 1 s.val N z j=(powerMass 0 N)^j*Collisions.coincidence (j+1) 0 N := by
  rw [probability_eq,s.property,show (1:ℝ)-2*(1/2)=0 by ring,zero_sub,pow_one,
    Collisions.coincidence_eq (Nat.succ_pos j)]
  rw [show Collisions.replicaIndex (j+1) 0= -(j:ℝ) by unfold Collisions.replicaIndex; push_cast; ring,pow_succ]
  field_simp [(powerMass_pos 0 N).ne']

#print axioms vacuum_apply
#print axioms retained_step
#print axioms probability_eq
#print axioms initial_mass
#print axioms vacuum_replica

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum
