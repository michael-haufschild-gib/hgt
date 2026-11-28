import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Limits

/-! # Energy of the occupied prime power after replica coincidence -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions

open Filter Real Crossover
open scoped Topology

theorem power_energy {x : ℝ} (p : PrimeAt x) (r : ℕ) :
    energy (primeLabel p^r)=(r:ℝ)*log p.val := by
  induction r with
  | zero => simp [energy]
  | succ r ih =>
    rw [pow_succ,energy_mul,ih,Nat.cast_succ,add_mul,one_mul]
    rfl

/-- Conditional on equal elementary labels, the energy of their actual
product divided by log N tends to zero in probability for all r≥2. -/
theorem energy_tail (k : ℕ) (c : ℝ) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun N : ℕ => ∑' n : ℕ,
      if ε≤((k+2:ℕ):ℝ)*log n/log N then conditional (k+2) (index c N) N n else 0) atTop (𝓝 0) := by
  let b N := replicaIndex (k+2) (index c N)
  let f (N n : ℕ) := if ε≤((k+2:ℕ):ℝ)*log n/log N then packetTerm (b N) N n else 0
  have each (n : ℕ) : Tendsto (fun N => f N n) atTop (𝓝 0) := by
    have small := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop (((k+2:ℕ):ℝ)*log (n:ℝ))
    apply tendsto_const_nhds.congr'
    filter_upwards [small.eventually_lt_const hε] with N hN
    exact (if_neg (not_le.mpr hN) : f N n=0).symm
  have d : Tendsto b atTop (𝓝 (1-((k+2:ℕ):ℝ))) := replica_index_limit (k+2) c
  have cut : 1-((k+2:ℕ):ℝ)< -(1/2:ℝ) := by
    push_cast
    linarith only [(Nat.cast_nonneg k : 0≤(k:ℝ))]
  have major : Summable (fun n : ℕ => (n:ℝ)^((-(1/2:ℝ))-1)) :=
    summable_nat_rpow.mpr (by norm_num)
  have dom : ∀ᶠ N in atTop, ∀ n, ‖f N n‖ ≤ (n:ℝ)^((-(1/2:ℝ))-1) := by
    filter_upwards [d.eventually_le_const cut] with N hN n
    unfold f
    split_ifs
    · exact dominate hN N n
    · rw [norm_zero]; exact rpow_nonneg (Nat.cast_nonneg _) _
  have numer := tendsto_tsum_of_dominated_convergence major each dom
  rw [tsum_zero] at numer
  have frac := numer.div (moving_mass (replicated_negative k) d) (primeTotal_pos (replicated_negative k)).ne'
  rw [zero_div] at frac
  apply frac.congr
  intro N
  change (∑' n, f N n)/powerMass (b N) N = _
  rw [←tsum_div_const]
  refine tsum_congr fun n => ?_
  change (if ε≤((k+2:ℕ):ℝ)*log n/log N then packetTerm (b N) N n else 0)/powerMass (b N) N=_
  split_ifs <;> simp only [conditional_eq (by omega : 0<k+2),finiteProbability,b,zero_div]

#print axioms power_energy
#print axioms energy_tail

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions
