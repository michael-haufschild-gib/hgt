import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin.Chart
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics.Evolution
import GaloisForLFunctions.HTGeometry.NormalizedPureStateInfidelity
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinFidelity

/-! # Projective spin fidelity of the elementary transition waves -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin

open Filter Real Dynamics
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.SchafferExl
open scoped Topology ComplexConjugate

/-- Squared overlap of the two physical prime waves after normalization. -/
def transitionProbability (c d t h k : ℝ) (N : ℕ) :=
  normalizedPureStateFidelity (windowWave c (t+h/log N) N) (windowWave d (t+k/log N) N)

/-- Squared projective Gram entry for the bulk and terminal amplitudes. -/
def profile (c d h k : ℝ) :=
  ‖1+(exp ((c+d)/2):ℂ)*clockPhase (h-k) 1‖^2/((1+exp c)*(1+exp d))

private theorem wave_mass (c u : ℝ) (N : ℕ) :
    ‖windowWave c u N‖^2=powerMass (drift c N/log N) N := by
  rw [windowWave,rawWave_sq]
  have e : 1-2*(indexParameter (drift c N/log N) u).re=drift c N/log N := by
    simp only [indexParameter,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im]
    ring
  rw [e]

theorem probability_limit (c d t h k : ℝ) :
    Tendsto (transitionProbability c d t h k) atTop (𝓝 (profile c d h k)) := by
  have lim := ((effective_clock c d t h k).norm.pow 2).div
    ((transition_masses c).1.mul (transition_masses d).1) (by positivity)
  apply lim.congr'
  filter_upwards [logEnergy_growth.eventually_gt_atTop 0] with N hL
  change ‖inner ℂ (windowWave c (t+h/log N) N) (windowWave d (t+k/log N) N)/(log (log N):ℂ)‖^2/
    ((powerMass (drift c N/log N) N/log (log N))*(powerMass (drift d N/log N) N/log (log N)))=_
  rw [transitionProbability,normalizedPureStateFidelity,wave_mass,wave_mass,norm_div,Complex.norm_real,
    Real.norm_of_nonneg (show 0≤log (log N) from hL.le),div_pow]
  field_simp [(show 0<log (log N) from hL).ne',(powerMass_pos (drift c N/log N) N).ne',
    (powerMass_pos (drift d N/log N) N).ne']

theorem profile_spin (c d h k : ℝ) : profile c d h k =
    finitePureStateFidelity (spinChartSpinor (coordinate c h)) (spinChartSpinor (coordinate d k)) := by
  rw [finitePureStateFidelity,finiteComplexInner_spinChartSpinor,coordinate_kernel]
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,spinChartScale_sq,
    coordinate_norm_sq,profile,div_eq_mul_inv,mul_inv_rev]
  ring

/-- The limiting transition probability equals the spinor fidelity,
or equivalently one minus the squared chordal distance of its chart points. -/
theorem chordal_fidelity (c d t h k : ℝ) :
    Tendsto (transitionProbability c d t h k) atTop
      (𝓝 (1-_root_.Bottcher.chordalDist (coordinate c h) (coordinate d k)^2)) := by
  rw [←spinChartSpinor_fidelity,←profile_spin]
  exact probability_limit c d t h k

/-- Any pair of nonpolar spin coordinates is physically realized by
prime waves at a common base time. -/
theorem realize_spin_pair {z w : ℂ} (hz : z≠0) (hw : w≠0) (t : ℝ) :
    ∃ c d h k : ℝ, coordinate c h=z ∧ coordinate d k=w ∧
      Tendsto (transitionProbability c d t h k) atTop
        (𝓝 (finitePureStateFidelity (spinChartSpinor z) (spinChartSpinor w))) := by
  have coords {v : ℂ} (hv : v≠0) : v∈Set.range (fun x : ℝ × ℝ => coordinate x.1 x.2) := by
    rw [coordinate_range]
    exact hv
  obtain ⟨⟨c,h⟩,rfl⟩ := coords hz
  obtain ⟨⟨d,k⟩,rfl⟩ := coords hw
  exact ⟨c,d,h,k,rfl,rfl,profile_spin c d h k ▸ probability_limit c d t h k⟩

#print axioms probability_limit
#print axioms chordal_fidelity
#print axioms realize_spin_pair

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin
