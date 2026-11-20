import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryEnergyMinimizer
import GaloisForLFunctions.HTGeometry.GaussianFrullaniLogKernel

/-!
# Exact costs of departing from the recovery equilibrium

The logarithmic energy separates into the equilibrium value, the
positive quadratic energy of the signed difference, and the excess
external potential. The quadratic term pays for every finite set of
Gaussian moment differences. The external term pays for mass placed
past either edge of the equilibrium support.
-/

noncomputable section
open MeasureTheory Set Filter GaloisForLFunctions.HTGeometry
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- Excess of the effective potential over its equilibrium level. -/
def recoveryObstacle (x : ℝ) : ℝ≥0∞ :=
  recoveryKernelPotential x+recoveryField x-ENNReal.ofReal recoveryEquilibriumConstant

private theorem obstacle_add_level {x : ℝ} (hx : |x| ≤ 1) :
    ENNReal.ofReal recoveryEquilibriumConstant+recoveryObstacle x =
      recoveryKernelPotential x+recoveryField x := by
  rw [add_comm,recoveryObstacle,tsub_add_cancel_of_le (recoveryEquilibriumConstant_le hx)]

/-- Exact extended-real splitting at the recovery measure. No finiteness
of the competitor's energy is required. -/
theorem recovery_energy_splitting (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, |x| ≤ 1) :
    recoveryWeightedEnergy ν = recoveryWeightedEnergy recoveryEquilibriumMeasure +
      (∫⁻ s in Ioi 0, gaussianEnergyDefectDensity ν recoveryEquilibriumMeasure s) +
      2*(∫⁻ x, recoveryObstacle x ∂ν) := by
  let μ := recoveryEquilibriumMeasure
  let A := frullaniEnergy μ μ
  let B := frullaniEnergy ν ν
  let M := frullaniEnergy ν μ
  let q (ρ : Measure ℝ) := ∫⁻ x, recoveryField x ∂ρ
  let c := ENNReal.ofReal recoveryEquilibriumConstant
  let D := ∫⁻ s in Ioi 0, gaussianEnergyDefectDensity ν μ s
  let O := ∫⁻ x, recoveryObstacle x ∂ν
  have hμ : ∀ᵐ x ∂μ, |x| ≤ 1 := ae_recoveryEquilibriumMeasure_abs_le_one
  have hpol : B+A=2*M+D := frullaniEnergy_polarization hν hμ
  have hlevel : A+q μ=c := frullaniEnergy_recovery_add_field
  have hfin : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hlevel ▸ le_self_add)
  have hobs : c+O=M+q ν := by
    calc _ = ∫⁻ x, c+recoveryObstacle x ∂ν := by
               rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
         _ = ∫⁻ x, recoveryKernelPotential x+recoveryField x ∂ν :=
               lintegral_congr_ae (hν.mono fun _ hx => obstacle_add_level hx)
         _ = _ := lintegral_add_left measurable_recoveryKernelPotential _
  change B+2*q ν=A+2*q μ+D+2*O
  apply (ENNReal.add_right_inj hfin).mp
  calc A+(B+2*q ν) = (B+A)+2*q ν := by ring
       _ = 2*(M+q ν)+D := by rw [hpol]; ring
       _ = 2*(A+q μ+O)+D := by rw [←hobs,hlevel]
       _ = A+(A+2*q μ+D+2*O) := by ring

/-- Any finite collection of Gaussian moments, integrated over any
measurable range of positive scales, costs part of the energy excess. -/
theorem recovery_moment_cost (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, |x| ≤ 1)
    (J : Finset ℕ) {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    recoveryWeightedEnergy recoveryEquilibriumMeasure +
      (∫⁻ s in S, ENNReal.ofReal ((∑ n ∈ J, (2*s)^n/n.factorial*
        (gaussianMoment s ν n-gaussianMoment s recoveryEquilibriumMeasure n)^2)/(2*s))) ≤
      recoveryWeightedEnergy ν := by
  have hm := ae_recoveryEquilibriumMeasure_abs_le_one
  have h : (∫⁻ s in S, ENNReal.ofReal ((∑ n ∈ J, (2*s)^n/n.factorial*
      (gaussianMoment s ν n-gaussianMoment s recoveryEquilibriumMeasure n)^2)/(2*s))) ≤
      ∫⁻ s in Ioi 0, gaussianEnergyDefectDensity ν recoveryEquilibriumMeasure s := by
    refine (lintegral_mono_set hS).trans ?_
    refine setLIntegral_mono' measurableSet_Ioi fun s hs => ENNReal.ofReal_le_ofReal ?_
    have hs' : 0 < s := hs
    have H := hasSum_gaussianGram_defect hs'.le hν hm
    have hupper := H.summable.sum_le_tsum J (fun n _ => by positivity)
    rw [H.tsum_eq] at hupper
    exact div_le_div_of_nonneg_right hupper (by positivity)
  rw [recovery_energy_splitting ν hν]
  exact (add_le_add_left h _).trans le_self_add

private theorem level_nonneg : 0 ≤ recoveryEquilibriumConstant := by
  have hz := recoveryEquilibrium_potential_eq (x:=0) (by simp [recoveryEdge_mem.1.le])
  have h := integral_log_abs_sub_le_log_two (x:=0) (by norm_num)
  simp only [abs_zero,sub_zero,Real.log_one,zero_div] at hz
  change 0 ≤ Real.log 2-Real.log (recoveryCapacity recoveryEdge)
  linarith only [h,hz]

private theorem real_effective_potential {x : ℝ} (hx : |x| < 1) :
    recoveryKernelPotential x+recoveryField x = ENNReal.ofReal (Real.log 2+recoveryWeightedPotential |x|) := by
  have he : recoveryWeightedPotential |x|=recoveryWeightedPotential x := by
    simp only [recoveryWeightedPotential,integral_log_abs_sub_recoveryEquilibriumMeasure hx.le,
      integral_log_abs_sub_recoveryEquilibriumMeasure (show | |x| | ≤ 1 by simpa only [abs_abs] using hx.le),abs_abs]
  rw [he,recoveryKernelPotential_eq hx.le,recoveryField,if_pos hx,←ENNReal.ofReal_add
    (sub_nonneg.mpr (integral_log_abs_sub_le_log_two hx.le))
    (by have := Real.log_nonpos (by linarith only [hx]) (by linarith only [abs_nonneg x] : 1-|x| ≤ 1); linarith)]
  congr 1
  unfold recoveryWeightedPotential
  ring

/-- The exterior mass beyond t has a strictly positive price per unit
mass whenever t lies outside the equilibrium support. -/
theorem recovery_exterior_mass_cost (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, |x| ≤ 1)
    {t : ℝ} (ht : recoveryEdge < t) (ht' : t < 1) :
    let price := recoveryWeightedPotential t+Real.log (recoveryCapacity recoveryEdge)
    0 < price ∧ recoveryWeightedEnergy recoveryEquilibriumMeasure +
      2*ENNReal.ofReal price*ν {x | t ≤ |x|} ≤ recoveryWeightedEnergy ν := by
  let price := recoveryWeightedPotential t+Real.log (recoveryCapacity recoveryEdge)
  have ht₀ : 0 < t := recoveryEdge_mem.1.trans ht
  have hp : 0 < price := by
    have h := recoveryWeightedPotential_gt (x:=t) (by simpa [abs_of_pos ht₀] using ht)
      (by simpa [abs_of_pos ht₀] using ht')
    dsimp only [price]; linarith only [h]
  let S : Set ℝ := {x | t ≤ |x|}
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hpoint {x : ℝ} (hx : |x| ≤ 1) (hs : x ∈ S) : ENNReal.ofReal price ≤ recoveryObstacle x := by
    apply (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp
    rw [obstacle_add_level hx,←ENNReal.ofReal_add level_nonneg hp.le]
    rcases hx.eq_or_lt with hx | hx
    · simp [recoveryField,hx]
    · rw [real_effective_potential hx]
      have hmono := recoveryWeightedPotential_strictMonoOn.monotoneOn ⟨ht.le,ht'⟩ ⟨ht.le.trans hs,hx⟩ hs
      apply ENNReal.ofReal_le_ofReal
      dsimp only [price,recoveryEquilibriumConstant]
      linarith only [hmono]
  have hmass : ENNReal.ofReal price*ν S ≤ ∫⁻ x, recoveryObstacle x ∂ν := by
    calc _ = ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal price) x ∂ν := by
               rw [lintegral_indicator hS,setLIntegral_const]
         _ ≤ _ := lintegral_mono_ae (hν.mono fun x hx => by
               by_cases h : x ∈ S
               · simpa [Set.indicator_of_mem h] using hpoint hx h
               · simp [Set.indicator_of_notMem h])
  refine ⟨hp,?_⟩
  rw [recovery_energy_splitting ν hν,mul_assoc]
  exact add_le_add (le_self_add) (mul_le_mul_left' hmass 2)

#print axioms recovery_energy_splitting
#print axioms recovery_moment_cost
#print axioms recovery_exterior_mass_cost

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
