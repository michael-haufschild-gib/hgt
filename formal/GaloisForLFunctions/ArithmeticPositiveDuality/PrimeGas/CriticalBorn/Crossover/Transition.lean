import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Quadrature
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Continuum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.FidelityMass
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.ElementaryWave

/-! # Logistic transition of reflected elementary heat states -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover

open Filter Real
open scoped Topology

private def L (N : ℕ) := log (log N)

private theorem positive_correction (c : ℝ) :
    Tendsto (fun N => tiltCorrection (drift c N) N / L N) atTop (𝓝 (exp c)) := by
  have w := (displacement_growth c).comp logEnergy_growth
  have main := (continuum_edge.comp w).mul ((edge_ratio c).comp logEnergy_growth)
  rw [one_mul] at main
  have err := (positive_remainder c).div_atTop logEnergy_growth
  have lim := main.add err
  rw [add_zero] at lim
  apply lim.congr'
  filter_upwards [w.eventually_gt_atTop 0,logEnergy_growth.eventually_gt_atTop 0] with N hw hL
  change 0<drift c N at hw
  change 0<L N at hL
  change (_root_.RHTower.logIntegralCompare (drift c N)*drift c N/exp (drift c N))*
    (exp (drift c N)/(drift c N*L N))+
    (tiltCorrection (drift c N) N-_root_.RHTower.logIntegralCompare (drift c N))/L N=_
  field_simp [hw.ne',hL.ne',(exp_pos _).ne']
  ring

private theorem negative_correction (c : ℝ) :
    Tendsto (fun N => tiltCorrection (-(drift c N)) N / L N) atTop (𝓝 0) := by
  have w := (displacement_growth c).comp logEnergy_growth
  have absLim : Tendsto (fun N => _root_.RHTower.logIntegralCompare (-(drift c N))/L N)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((displacement_small c).comp logEnergy_growth)
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [w.eventually_ge_atTop 0,logEnergy_growth.eventually_gt_atTop 0] with N hw hL
      rw [Real.norm_eq_abs,abs_div,abs_of_pos (show 0<L N from hL)]
      exact div_le_div_of_nonneg_right (negative_continuum_bound (show 0≤drift c N from hw))
        (show 0<L N from hL).le
  have h := ((negative_remainder c).div_atTop logEnergy_growth).add absLim
  rw [add_zero] at h
  apply h.congr
  intro N
  change (tiltCorrection (-(drift c N)) N-_root_.RHTower.logIntegralCompare (-(drift c N)))/L N+
    _root_.RHTower.logIntegralCompare (-(drift c N))/L N=_
  ring

/-- Physical real part in the transition window, centered and scaled by
the maximum elementary energy. Clock time remains arbitrary. -/
def transitionParameter (c t : ℝ) (N : ℕ) : ℂ :=
  ((1/2 + (drift c N/log N)/2 : ℝ):ℂ) + (t:ℂ)*Complex.I

/-- Only the tilt favoring large elementary energies acquires an
additional mass comparable with the entire harmonic packet. -/
theorem transition_masses (c : ℝ) :
    Tendsto (fun N : ℕ => powerMass (drift c N/log N) N / log (log N)) atTop (𝓝 (1+exp c)) ∧
    Tendsto (fun N : ℕ => powerMass (-(drift c N)/log N) N / log (log N)) atTop (𝓝 1) := by
  have H : Tendsto (fun N : ℕ => powerMass 0 N / L N) atTop (𝓝 1) :=
    harmonic_mass_ratio.comp tendsto_natCast_atTop_atTop
  have pos := (positive_correction c).add H
  have neg := (negative_correction c).add H
  rw [add_comm (exp c) 1] at pos
  rw [zero_add] at neg
  exact ⟨pos.congr (fun N => by simp only [tiltCorrection,L,←add_div,sub_add_cancel]),
    neg.congr (fun N => by simp only [tiltCorrection,L,←add_div,sub_add_cancel])⟩

private theorem measured (c t : ℝ) (N : ℕ) :
    reflectedFidelity (transitionParameter c t N) N = (powerMass 0 N)^2 /
      (powerMass (-(drift c N)/log N) N * powerMass (drift c N/log N) N) := by
  simp only [reflectedFidelity_eq,transitionParameter,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,
    Complex.ofReal_im,neg_zero,add_zero]
  rw [show 1-2*(1/2+(drift c N/log N)/2) = -(drift c N)/log N by ring,neg_div,neg_neg]

/-- At real displacement (log L + log log L + c)/(2 log N), with
L = log log N, the reflected transition probability tends to 1/(1+exp c). -/
theorem logistic_fidelity (c t : ℝ) :
    Tendsto (fun N : ℕ => reflectedFidelity (transitionParameter c t N) N) atTop (𝓝 (1/(1+exp c))) := by
  have H : Tendsto (fun N : ℕ => powerMass 0 N / L N) atTop (𝓝 1) :=
    harmonic_mass_ratio.comp tendsto_natCast_atTop_atTop
  obtain ⟨pos,neg⟩ := transition_masses c
  have den := neg.mul pos
  rw [one_mul] at den
  have lim := (H.pow 2).div den (by positivity)
  rw [one_pow] at lim
  apply lim.congr'
  filter_upwards [logEnergy_growth.eventually_gt_atTop 0] with N hL
  rw [measured]
  change (powerMass 0 N/L N)^2 / ((powerMass (-(drift c N)/log N) N/L N)*
    (powerMass (drift c N/log N) N/L N)) = _
  field_simp [(show 0<L N from hL).ne',(powerMass_pos (-(drift c N)/log N) N).ne',
    (powerMass_pos (drift c N/log N) N).ne']

#print axioms logistic_fidelity
#print axioms transition_masses

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover
