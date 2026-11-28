import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin.Return

/-! # The two polar states of the limiting spin chart -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin

open Filter Real
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.SchafferExl
open scoped Topology ComplexConjugate

/-- Fidelities to the bulk and terminal basis states. -/
theorem polar_fidelities (c h : ℝ) :
    finitePureStateFidelity (spinChartSpinor (coordinate c h)) ![(0:ℂ),1]=(Bulk.bulkWeight c:ℝ) ∧
    finitePureStateFidelity (spinChartSpinor (coordinate c h)) ![(1:ℂ),0]=1-(Bulk.bulkWeight c:ℝ) := by
  let z := coordinate c h
  have bulk : finiteComplexInner (spinChartSpinor z) ![(0:ℂ),1] = (spinChartScale z:ℂ) := by
    simp [finiteComplexInner,spinChartSpinor,Fin.sum_univ_two]
  have terminal : finiteComplexInner (spinChartSpinor z) ![(1:ℂ),0] = (spinChartScale z:ℂ)*conj z := by
    simp [finiteComplexInner,spinChartSpinor,Fin.sum_univ_two]
  have mass : ‖z‖^2=exp c := coordinate_norm_sq c h
  constructor
  · change ‖finiteComplexInner (spinChartSpinor z) ![(0:ℂ),1]‖^2=1/(1+exp c)
    rw [bulk,Complex.norm_real,Real.norm_eq_abs,sq_abs,spinChartScale_sq,mass,one_div]
  · change ‖finiteComplexInner (spinChartSpinor z) ![(1:ℂ),0]‖^2=1-1/(1+exp c)
    rw [terminal,norm_mul,mul_pow,RCLike.norm_conj,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      spinChartScale_sq,mass]
    field_simp [(show 0<1+exp c by positivity).ne']
    ring

/-- The two missing polar rays lie in the projective closure of the
limiting prime preparations, at either end of the temperature offsets. -/
theorem polar_limits (h : ℝ) :
    Tendsto (fun c => finitePureStateFidelity (spinChartSpinor (coordinate c h)) ![(0:ℂ),1])
      atBot (𝓝 1) ∧
    Tendsto (fun c => finitePureStateFidelity (spinChartSpinor (coordinate c h)) ![(1:ℂ),0])
      atTop (𝓝 1) := by
  have low := (tendsto_const_nhds (x := (1:ℝ))).div (tendsto_exp_atBot.const_add 1)
    (by norm_num : (1:ℝ)+0≠0)
  have grow : Tendsto (fun c : ℝ => 1+exp c) atTop atTop :=
    tendsto_atTop_mono (fun c => le_add_of_nonneg_left zero_le_one) tendsto_exp_atTop
  have high := (grow.const_div_atTop (1:ℝ)).const_sub 1
  constructor
  · simp only [(polar_fidelities _ h).1]
    change Tendsto (fun c : ℝ => 1/(1+exp c)) atBot (𝓝 1)
    simpa only [Pi.div_def,add_zero,div_one] using low
  · simp only [(polar_fidelities _ h).2]
    change Tendsto (fun c : ℝ => 1-1/(1+exp c)) atTop (𝓝 1)
    simpa only [sub_zero] using high

#print axioms polar_fidelities
#print axioms polar_limits

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin
