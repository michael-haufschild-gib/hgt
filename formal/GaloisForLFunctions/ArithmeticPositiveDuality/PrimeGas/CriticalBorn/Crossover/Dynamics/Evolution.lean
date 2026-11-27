import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics.Phase
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.EqualTime

/-! # Hamiltonian clock on the two limiting transition amplitudes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics

open Filter Real Finset
open scoped ComplexConjugate Topology

private theorem heat_product (a b u v : ℝ) (n : ℕ+) :
    heat (indexParameter b v) n * conj (heat (indexParameter a u) n) =
      ((((n:ℕ):ℝ)^((a+b)/2-1):ℝ):ℂ)*clockPhase (u-v) (energy n) := by
  have pp : 0<((n:ℕ):ℝ) := Nat.cast_pos.mpr n.pos
  rw [heat,heat,←Complex.exp_conj,←Complex.exp_add,rpow_def_of_pos pp,Complex.ofReal_exp,
    clockPhase,←Complex.exp_add]
  congr 1
  simp only [indexParameter,energy,map_mul,map_neg,map_add,Complex.conj_ofReal,Complex.conj_I,
    Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

/-- The finite clock Gram pairing is a phase expectation in the wave
with the midpoint tilt, multiplied by its mass. -/
theorem phase_gram (c d t h k : ℝ) {N : ℕ} (hN : 2≤N) :
    inner ℂ (windowWave c (t+h/log N) N) (windowWave d (t+k/log N) N) =
      (powerMass (drift ((c+d)/2) N/log N) N:ℂ)*phaseAverage (drift ((c+d)/2) N/log N) (h-k) N := by
  let a := drift c N/log N
  let b := drift d N/log N
  let m := drift ((c+d)/2) N/log N
  have idx : (a+b)/2=m := by unfold a b m drift displacement; ring
  rw [phaseAverage_eq,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (powerMass_pos _ _).ne')]
  let f (p : ℕ) := (((p:ℝ)^(m-1):ℝ):ℂ)*clockPhase (h-k) (energyFraction N p)
  change (∑ p : ↥(primes (cutoff N)), rawWave (indexParameter b (t+k/log N)) N p *
    conj (rawWave (indexParameter a (t+h/log N)) N p)) = ∑ p ∈ primes (cutoff N), f p
  rw [←(primes (cutoff N)).sum_attach f]
  simp only [←Finset.univ_eq_attach]
  apply sum_congr rfl
  intro p _
  let n : ℕ+ := ⟨p.val,(Nat.mem_primesBelow.mp p.property).2.pos⟩
  change heat (indexParameter b (t+k/log N)) n * conj (heat (indexParameter a (t+h/log N)) n) =
    (((p.val:ℝ)^(m-1):ℝ):ℂ)*clockPhase (h-k) (energyFraction N p.val)
  rw [heat_product,idx,energyFraction_on_prime hN p.property]
  congr 1
  unfold clockPhase
  have shift : (t+h/log N-(t+k/log N))*energy n = (h-k)*(log p.val/log N) := by
    change (t+h/log N-(t+k/log N))*log p.val=_
    ring
  rw [shift]

/-- In units of the upper energy, the harmonic amplitude is stationary
and the terminal amplitude evolves by the scalar phase exp(−ih). -/
theorem effective_clock (c d t h k : ℝ) :
    Tendsto (fun N : ℕ => inner ℂ (windowWave c (t+h/log N) N) (windowWave d (t+k/log N) N) /
      (log (log N):ℂ)) atTop (𝓝 (1+(exp ((c+d)/2):ℂ)*clockPhase (h-k) 1)) := by
  let m := (c+d)/2
  have mass := Complex.continuous_ofReal.continuousAt.tendsto.comp (transition_masses m).1
  have both := mass.mul (phase_response m (h-k))
  have id : ((1+exp m:ℝ):ℂ)*(((Bulk.bulkWeight m:ℝ):ℂ)+
      (1-((Bulk.bulkWeight m:ℝ):ℂ))*clockPhase (h-k) 1) =
      1+(exp m:ℂ)*clockPhase (h-k) 1 := by
    change ((1+exp m:ℝ):ℂ)*(((1/(1+exp m):ℝ):ℂ)+(1-((1/(1+exp m):ℝ):ℂ))*_) = _
    have den : (1:ℂ)+(exp m:ℂ)≠0 := by
      rw [←Complex.ofReal_one,←Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    simp only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_one]
    field_simp [den]
    ring
  rw [id] at both
  apply both.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [phase_gram c d t h k hN]
  change ((powerMass (drift m N/log N) N/log (log N):ℝ):ℂ)*phaseAverage _ _ _=_
  rw [Complex.ofReal_div]
  ring

#print axioms phase_gram
#print axioms effective_clock

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics
