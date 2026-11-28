import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Coincidence
import GaloisForLFunctions.RHTower.PrimeZetaAbelRepresentation

/-! # Measuring the prime zeta sums by replica coincidences -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions

open Filter Real Crossover
open scoped Topology

def index (c : ℝ) (N : ℕ) := drift c N/log N

/-- Relate the cutoff power index to the prime zeta exponent. -/
theorem total_eq_primeZeta (s : ℝ) : primeTotal (1-s)=_root_.RHTower.primeZeta s := by
  rw [primeTotal,show 1-s-1= -s by ring]
  exact _root_.RHTower.tsum_primeIndicatorRpow

theorem replica_index_limit (r : ℕ) (c : ℝ) :
    Tendsto (fun N => replicaIndex r (index c N)) atTop (𝓝 (1-(r:ℝ))) := by
  have h := (((Ordinary.index_limit c).sub_const 1).const_mul (r:ℝ)).const_add 1
  rw [show (1:ℝ)+(r:ℝ)*(0-1)=1-r by ring] at h
  exact h

theorem replicated_negative (k : ℕ) : 1-((k+2:ℕ):ℝ)<0 := by
  exact sub_neg.mpr (by exact_mod_cast (show 1<k+2 by omega))

/-- The mass-normalized coincidence probability of every nontrivial
number of copies recovers the corresponding prime zeta value. -/
theorem mass_scaled (k : ℕ) (c : ℝ) : Tendsto (fun N : ℕ =>
    (powerMass (index c N) N)^(k+2)*coincidence (k+2) (index c N) N) atTop
      (𝓝 (_root_.RHTower.primeZeta ((k+2:ℕ):ℝ))) := by
  rw [←total_eq_primeZeta]
  apply (moving_mass (replicated_negative k) (replica_index_limit (k+2) c)).congr
  intro N
  rw [coincidence_eq (by omega : 0<k+2)]
  field_simp [(powerMass_pos (index c N) N).ne']

/-- Exact harmonic normalization of the measured coincidence rates. -/
theorem collision_limit (k : ℕ) (c : ℝ) :
    Tendsto (fun N : ℕ => (log (log N))^(k+2)*coincidence (k+2) (index c N) N) atTop
      (𝓝 (_root_.RHTower.primeZeta ((k+2:ℕ):ℝ)/(1+exp c)^(k+2))) := by
  rw [←total_eq_primeZeta]
  have h := (moving_mass (replicated_negative k) (replica_index_limit (k+2) c)).div
    ((transition_masses c).1.pow (k+2)) (by positivity)
  apply h.congr'
  filter_upwards [logEnergy_growth.eventually_gt_atTop 0] with N hL
  change powerMass (replicaIndex (k+2) (index c N)) N/(powerMass (index c N) N/log (log N))^(k+2)=_
  rw [coincidence_eq (by omega : 0<k+2),div_pow]
  field_simp [(powerMass_pos (index c N) N).ne',(show 0<log (log (N:ℝ)) from hL).ne']

/-- After coincidence the common label has cutoff-independent limiting
law proportional to p raised to the negative number of copies. -/
theorem conditional_limit (k : ℕ) (c : ℝ) :
    Tendsto (fun N => ∑' n, |conditional (k+2) (index c N) N n-
      infiniteProbability (1-((k+2:ℕ):ℝ)) n|) atTop (𝓝 0) := by
  simpa only [conditional_eq (by omega : 0<k+2)] using
    normalized_l1 (replicated_negative k) (replica_index_limit (k+2) c)

#print axioms mass_scaled
#print axioms collision_limit
#print axioms conditional_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions
