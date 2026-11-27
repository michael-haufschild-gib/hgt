import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Bulk.Occupation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Transition

/-! # Harmonic bulk and terminal mass in the reflection window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Bulk

open Filter Real
open scoped Topology

/-- Fraction of harmonic bulk surviving the positive tilt. -/
def bulkWeight (c : ℝ) : unitInterval :=
  ⟨1/(1+exp c),by positivity,by
    rw [div_le_one (by positivity)]
    linarith only [(exp_pos c).le]⟩

private theorem lower_harmonic {u : ℝ} (hu : 0<u) :
    Tendsto (fun N : ℕ => powerMass 0 (interiorCutoff u N) / log (log N)) atTop (𝓝 u) := by
  have h := (harmonic_mass_ratio.comp (interior_growth hu)).mul_const u
  rw [one_mul] at h
  apply h.congr'
  filter_upwards [logEnergy_growth.eventually_gt_atTop 0] with N hL
  change powerMass 0 (interiorCutoff u N)/log (log (interiorCutoff u N))*u=_
  have id : log (log (interiorCutoff u N)) = u*log (log N) := by
    simp only [interiorCutoff,logEnergyCutoff,log_exp]
  rw [id]
  field_simp [hu.ne',(show 0<log (log N) from hL).ne']

private theorem lower_mass {u : ℝ} (hu : 0<u) {a : ℕ → ℝ}
    (h : Tendsto (fun N : ℕ => powerMass (a N) (interiorCutoff u N)/powerMass 0 (interiorCutoff u N))
      atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => powerMass (a N) (interiorCutoff u N)/log (log N)) atTop (𝓝 u) := by
  have lim := h.mul (lower_harmonic hu)
  rw [one_mul] at lim
  apply lim.congr
  intro N
  field_simp [(powerMass_pos 0 _).ne']

private theorem probability_limit {a : ℕ → ℝ} {m u : ℝ} (hm : 0 < m) (hu : 0<u) (hu' : u<1)
    (lo : Tendsto (fun N : ℕ => powerMass (a N) (interiorCutoff u N)/log (log N)) atTop (𝓝 u))
    (hi : Tendsto (fun N : ℕ => powerMass (a N) N/log (log N)) atTop (𝓝 m)) :
    Tendsto (fun N => cdf (positionLaw (a N) N) u) atTop (𝓝 (u/m)) := by
  apply (lo.div hi hm.ne').congr'
  filter_upwards [position_cdf_eq a hu hu',logEnergy_growth.eventually_gt_atTop 0] with N hF hL
  rw [hF]
  change (_/log (log N))/(powerMass (a N) N/log (log N)) = _
  field_simp [(show 0<log (log N) from hL).ne',(powerMass_pos (a N) N).ne']

/-- The wave favoring large elementary excitations acquires terminal mass.
The reflected wave retains the uniform logarithmic-energy law. -/
theorem reflected_energy_laws (c : ℝ) :
    Tendsto (fun N : ℕ => positionLaw (drift c N/log N) N) atTop (𝓝 (bulkAndEndpoint (bulkWeight c))) ∧
    Tendsto (fun N : ℕ => positionLaw (-(drift c N)/log N) N) atTop (𝓝 uniformPosition) := by
  obtain ⟨pos,neg⟩ := transition_masses c
  constructor
  · apply weak_of_interior_cdf
    intro u hu hu'
    rw [mixture_cdf _ hu hu']
    have h := probability_limit (by positivity) hu hu'
      (lower_mass hu (interior_tilts c hu hu').1) pos
    have eq : (bulkWeight c:ℝ)*u = u/(1+exp c) := by change 1/(1+exp c)*u=_; ring
    rw [eq]
    exact h
  · apply weak_of_interior_cdf
    intro u hu hu'
    rw [uniform_cdf hu hu']
    simpa only [div_one] using probability_limit one_pos hu hu'
      (lower_mass hu (interior_tilts c hu hu').2) neg

/-- Quantum fidelity measures the surviving uniform bulk fraction. -/
theorem fidelity_eq_bulk_fraction (c t : ℝ) :
    Tendsto (fun N : ℕ => reflectedFidelity (transitionParameter c t N) N) atTop (𝓝 (bulkWeight c:ℝ)) :=
  logistic_fidelity c t

#print axioms reflected_energy_laws
#print axioms fidelity_eq_bulk_fraction

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Bulk
