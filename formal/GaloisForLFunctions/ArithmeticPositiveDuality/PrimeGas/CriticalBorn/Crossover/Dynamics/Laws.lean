import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics.Measurement
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Bulk.Coexistence
import Mathlib.Probability.Distributions.Bernoulli

/-! # Two-point distribution of elementary energy at the transition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics

open Filter Real MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology

/-- Two-point probability law giving weight r to x. -/
def twoPoint {X : Type*} [MeasurableSpace X] (x y : X) (r : unitInterval) : ProbabilityMeasure X :=
  ⟨bernoulliMeasure x y r,inferInstance⟩

private theorem moment_limit (c : ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => ∫ y, (y:ℝ)^k ∂(codeLaw (drift c N/log N) N : Measure unitInterval))
      atTop (𝓝 (exp (-(k:ℝ))*(1+exp (c+k))/(1+exp c))) := by
  have h := ((transition_masses (c+k)).1.div (transition_masses c).1 (by positivity)).const_mul (exp (-(k:ℝ)))
  rw [mul_div_assoc (exp (-(k:ℝ))) (1+exp (c+k)) (1+exp c)]
  apply h.congr'
  filter_upwards [logEnergy_growth.eventually_gt_atTop 0,eventually_ge_atTop 2] with N hL hN
  rw [code_moment _ hN]
  have shift : drift (c+k) N/log N = drift c N/log N + k/log N := by
    unfold drift displacement
    ring
  change exp (-(k:ℝ))*((powerMass (drift (c+k) N/log N) N/log (log N))/
    (powerMass (drift c N/log N) N/log (log N)))=_
  rw [shift]
  field_simp [(show 0<log (log N) from hL).ne',(powerMass_pos (drift c N/log N) N).ne']

/-- Resolving energy exponentially gives atoms at the two coded endpoints. -/
theorem code_law_limit (c : ℝ) :
    Tendsto (fun N : ℕ => codeLaw (drift c N/log N) N) atTop
      (𝓝 (twoPoint (code 0) (code 1) (Bulk.bulkWeight c))) := by
  apply probabilityMeasure_tendsto_of_integral_pow_tendsto
  intro k
  change Tendsto _ _ (𝓝 (∫ y : unitInterval, (y:ℝ)^k ∂bernoulliMeasure (code 0) (code 1) _))
  rw [integral_bernoulliMeasure]
  have eq : exp (-(k:ℝ))*(1+exp (c+k))/(1+exp c) =
      (Bulk.bulkWeight c:ℝ) • (code 0:ℝ)^k + (1-(Bulk.bulkWeight c:ℝ)) • (code 1:ℝ)^k := by
    change _ = 1/(1+exp c) * (exp ((0:ℝ)-1))^k + (1-1/(1+exp c)) * (exp ((1:ℝ)-1))^k
    rw [sub_self,exp_zero,one_pow,zero_sub,←exp_nat_mul,show (k:ℝ)*(-1)= -(k:ℝ) by ring,exp_add,exp_neg]
    field_simp [(exp_pos (k:ℝ)).ne',(show 0<1+exp c by positivity).ne']
    ring
  rw [←eq]
  exact moment_limit c k

/-- Continuous inverse on the support of every coded energy law. -/
def decode (z : unitInterval) := 1+log (max (exp (-1)) (z:ℝ))

theorem decode_continuous : Continuous decode :=
  continuous_const.add ((continuous_const.max continuous_subtype_val).log
    (fun _ => ((exp_pos _).trans_le (le_max_left _ _)).ne'))

theorem decode_code (y : unitInterval) : decode (code y)=(y:ℝ) := by
  have h : exp (-1) ≤ exp ((y:ℝ)-1) :=
    exp_le_exp.mpr (by linarith only [y.property.1])
  change 1+log (max (exp (-1)) (exp ((y:ℝ)-1)))=_
  rw [max_eq_right h,log_exp]
  ring

/-- Distribution of the physical energy fraction log p / log N. -/
def energyLaw (a : ℝ) (N : ℕ) := (codeLaw a N).map decode_continuous.measurable.aemeasurable

theorem energyLaw_eq (a : ℝ) (N : ℕ) : energyLaw a N =
    (labelLaw ((1-a)/2) N).map (f := fun p => (energyFraction N p:ℝ))
      (measurable_of_countable _).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((labelLaw ((1-a)/2) N : Measure ℕ).map (fun p => code (energyFraction N p))).map decode =
    (labelLaw ((1-a)/2) N : Measure ℕ).map (fun p => (energyFraction N p:ℝ))
  rw [Measure.map_map decode_continuous.measurable (measurable_of_countable _)]
  congr 1
  funext p
  exact decode_code _

/-- The whole rescaled Hamiltonian reading has spectral mass only at
energies zero and one in the limit. -/
theorem energy_law_limit (c : ℝ) :
    Tendsto (fun N : ℕ => energyLaw (drift c N/log N) N) atTop
      (𝓝 (twoPoint (0:ℝ) 1 (Bulk.bulkWeight c))) := by
  have lim := (ProbabilityMeasure.continuous_map decode_continuous).continuousAt.tendsto.comp (code_law_limit c)
  have eq : (twoPoint (code 0) (code 1) (Bulk.bulkWeight c)).map
      decode_continuous.measurable.aemeasurable = twoPoint (0:ℝ) 1 (Bulk.bulkWeight c) := by
    apply ProbabilityMeasure.toMeasure_injective
    change (bernoulliMeasure (code 0) (code 1) (Bulk.bulkWeight c)).map decode = _
    rw [map_bernoulliMeasure,decode_code,decode_code]
    rfl
  rw [eq] at lim
  exact lim

#print axioms code_law_limit
#print axioms energyLaw_eq
#print axioms energy_law_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics
