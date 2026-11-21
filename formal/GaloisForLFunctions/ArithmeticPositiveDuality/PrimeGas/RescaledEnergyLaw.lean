import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalResidueState
import GaloisForLFunctions.RHTower.MobiusCriticalClockWeakConvergence
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Energy fluctuations at the partition pole

Multiplying energy by the inverse-temperature excess gives a nondegenerate
limiting energy law. The joint Laplace transform factors for every periodic
readout. Conditioning on any nonempty residue event leaves the same limiting
unit exponential distribution.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Set Topology MeasureTheory

/-- Energy in units of the inverse-temperature excess. -/
def rescaledEnergy (β : TraceTemperature) (n : ℕ+) : ℝ := (β.val - 1) * energy n

abbrev EnergyLaplaceDomain := {u : ℂ // -1 < u.re}

/-- Absolute convergence of the energy Laplace observable has a sharp boundary,
already at each individual temperature. -/
theorem energyMoment_domain_iff (β : TraceTemperature) (u : ℂ) :
    Summable (fun n => thermalWeight β n * Real.exp (-u.re * rescaledEnergy β n)) ↔
      -1 < u.re := by
  let c : ℝ := β.val + u.re * (β.val - 1)
  have hw (n : ℕ+) : thermalWeight β n * Real.exp (-u.re * rescaledEnergy β n) =
      ‖heat ((c : ℂ)/2) n‖^2 := by
    rw [thermalWeight, ← Real.exp_add, norm_heat, Complex.div_ofNat_re, Complex.ofReal_re,
      sq, ← Real.exp_add]
    congr 1
    dsimp only [c, rescaledEnergy]
    ring
  simp_rw [hw]
  rw [summable_heat_sq_iff, Complex.div_ofNat_re, Complex.ofReal_re]
  have hβ := sub_pos.mpr β.property
  have hid : c - 1 = (β.val - 1) * (1 + u.re) := by dsimp [c]; ring
  constructor
  · intro h
    have hp : 0 < (β.val - 1) * (1 + u.re) := by rw [← hid]; linarith
    linarith only [pos_of_mul_pos_right hp hβ.le]
  · intro h
    have hp := mul_pos hβ (show 0 < 1 + u.re by linarith)
    linarith only [hp, hid]

/-- Effective inverse temperature after inserting the energy Laplace observable. -/
def tiltTemperature (u : EnergyLaplaceDomain) (β : TraceTemperature) : {z : ℂ // 1 < z.re} :=
  ⟨1 + ((β.val : ℂ)-1)*(1+u.val), by
    simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_self, zero_mul, sub_zero]
    linarith only [mul_pos (sub_pos.mpr β.property) (show 0 < 1+u.val.re by linarith [u.property])]⟩

theorem heat_tiltTemperature (u : EnergyLaplaceDomain) (β : TraceTemperature) (n : ℕ+) :
    heat (tiltTemperature u β).val n =
      (thermalWeight β n : ℂ) * Complex.exp (-u.val * (rescaledEnergy β n : ℂ)) := by
  rw [heat, thermalWeight, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [tiltTemperature, rescaledEnergy, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_one]
  ring

/-- A single operator trace reads the rescaled energy and shell residue together. -/
def energyResidueTransform (m : ℕ+) (F : ZMod (m : ℕ) → ℂ)
    (u : EnergyLaplaceDomain) (β : TraceTemperature) : ℂ :=
  ContinuousLinearMap.opTrace (periodicGibbsOperator m F (tiltTemperature u β)) /
    ContinuousLinearMap.opTrace (gibbsOperator ⟨(β.val : ℂ), β.property⟩)

theorem energyResidueTransform_series (m : ℕ+) (F : ZMod (m : ℕ) → ℂ)
    (u : EnergyLaplaceDomain) (β : TraceTemperature) :
    energyResidueTransform m F u β =
      (∑' n : ℕ+, F (n : ℕ) * (thermalWeight β n : ℂ) *
        Complex.exp (-u.val * (rescaledEnergy β n : ℂ))) / riemannZeta β.val := by
  rw [energyResidueTransform, periodicGibbs_trace_series, partition_eq_zeta]
  congr 1
  exact tsum_congr fun n => by rw [heat_tiltTemperature, mul_assoc]

private theorem tilt_at_pole (u : EnergyLaplaceDomain) :
    Tendsto (fun β => (tiltTemperature u β).val) atPartitionPole (𝓝[≠] 1) := by
  have hb := tendsto_temperature_punctured.mono_right nhdsWithin_le_nhds
  have h := tendsto_const_nhds (x := (1 : ℂ)) |>.add
    ((hb.sub (tendsto_const_nhds (x := (1 : ℂ)))).mul (tendsto_const_nhds (x := 1+u.val)))
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun β : TraceTemperature => 1 + ((β.val : ℂ)-1)*(1+u.val)) _ _
    simpa only [sub_self, zero_mul, add_zero] using h
  · filter_upwards with β
    intro he
    change (tiltTemperature u β).val = 1 at he
    exact (tiltTemperature u β).property.ne' (congrArg Complex.re he)

theorem energyResidueTransform_limit (m : ℕ+) (F : ZMod (m : ℕ) → ℂ)
    (u : EnergyLaplaceDomain) :
    Tendsto (energyResidueTransform m F u) atPartitionPole
      (𝓝 (((∑ j, F j) / (m : ℕ)) / (1 + u.val))) := by
  have hL := (ZMod.LFunction_residue_one F).comp (tilt_at_pole u)
  have hZ := riemannZeta_residue_one.comp tendsto_temperature_punctured
  have h := (hL.div hZ one_ne_zero).div_const (1+u.val)
  rw [div_one, ← Finset.sum_div] at h
  apply h.congr'
  filter_upwards with β
  let v : ℂ := 1+u.val
  have hv : v ≠ 0 := by
    intro hzero
    have hr := congrArg Complex.re hzero
    change (1+u.val).re = 0 at hr
    rw [Complex.add_re, Complex.one_re] at hr
    linarith [u.property]
  have hb : (β.val : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast β.property.ne')
  let L := ZMod.LFunction F (tiltTemperature u β).val
  let Z := riemannZeta (β.val : ℂ)
  change (((tiltTemperature u β).val - 1) * L / (((β.val : ℂ) - 1) * Z)) / v = _
  rw [energyResidueTransform, periodicGibbs_trace, partition_eq_zeta]
  change ((((1 + ((β.val : ℂ)-1)*v) - 1)*L) / (((β.val : ℂ)-1)*Z)) / v = L/Z
  rw [add_sub_cancel_left, mul_assoc, mul_div_mul_left _ _ hb, mul_div_assoc,
    mul_div_cancel_left₀ _ hv]

/-- Raw Gibbs weight in a residue event. -/
private def eventWeight (m : ℕ+) (A : Finset (ZMod (m : ℕ))) (β : TraceTemperature) (n : ℕ+) :=
  if ((n : ℕ) : ZMod (m : ℕ)) ∈ A then thermalWeight β n else 0

private theorem eventWeight_nonneg (m : ℕ+) (A : Finset (ZMod (m : ℕ))) (β : TraceTemperature) (n : ℕ+) :
    0 ≤ eventWeight m A β n := by
  unfold eventWeight
  split
  · exact (thermalWeight_pos β n).le
  · exact le_rfl

private theorem eventWeight_summable (m : ℕ+) (A : Finset (ZMod (m : ℕ))) (β : TraceTemperature) :
    Summable (eventWeight m A β) :=
  Summable.of_nonneg_of_le (eventWeight_nonneg m A β) (fun n => by
    unfold eventWeight
    split
    · exact le_rfl
    · exact (thermalWeight_pos β n).le) (thermalWeight_summable β)

abbrev ResidueEvent (m : ℕ+) := {A : Finset (ZMod (m : ℕ)) // A.Nonempty}

/-- The event contains a positive representative, also when its only residue is zero. -/
private theorem eventWeight_total_pos (m : ℕ+) (A : ResidueEvent m) (β : TraceTemperature) :
    0 < ∑' n, eventWeight m A.val β n := by
  obtain ⟨j,hj⟩ := A.property
  let n : ℕ+ := ⟨j.val + m.val, Nat.add_pos_right _ m.pos⟩
  have hn : ((n : ℕ) : ZMod (m : ℕ)) = j := by
    change ((j.val + (m : ℕ) : ℕ) : ZMod (m : ℕ)) = j
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
  have hw : eventWeight m A.val β n = thermalWeight β n := if_pos (by rw [hn]; exact hj)
  exact (eventWeight_summable m A.val β).tsum_pos (eventWeight_nonneg m A.val β) n
    (by rw [hw]; exact thermalWeight_pos β n)

private def conditionalWeight (m : ℕ+) (A : ResidueEvent m) (β : TraceTemperature) (n : ℕ+) :=
  eventWeight m A.val β n / ∑' i, eventWeight m A.val β i

private theorem conditionalWeight_nonneg (m : ℕ+) (A : ResidueEvent m) (β : TraceTemperature) (n : ℕ+) :
    0 ≤ conditionalWeight m A β n :=
  div_nonneg (eventWeight_nonneg m _ β n) (eventWeight_total_pos m A β).le

private theorem conditionalWeight_hasSum (m : ℕ+) (A : ResidueEvent m) (β : TraceTemperature) :
    HasSum (conditionalWeight m A β) 1 := by
  have h := (eventWeight_summable m A.val β).hasSum.div_const (∑' n, eventWeight m A.val β n)
  rwa [div_self (eventWeight_total_pos m A β).ne'] at h

/-- Law of measured energy under the Gibbs weights conditioned on a nonempty residue event. -/
def conditionalEnergyLaw (m : ℕ+) (A : ResidueEvent m) (β : TraceTemperature) : ProbabilityMeasure ℝ :=
  ⟨Measure.sum (fun n : ℕ+ => ENNReal.ofReal (conditionalWeight m A β n) •
      Measure.dirac (rescaledEnergy β n)), ⟨by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg (conditionalWeight_nonneg m A β)
      (conditionalWeight_hasSum m A β).summable, (conditionalWeight_hasSum m A β).tsum_eq,
      ENNReal.ofReal_one]⟩⟩

/-- Laplace frequency for the characteristic function at t. -/
def fourierFrequency (t : ℝ) : EnergyLaplaceDomain :=
  ⟨-(t : ℂ)*Complex.I, by simp [Complex.mul_re]⟩

private theorem charFun_conditionalEnergyLaw (m : ℕ+) (A : ResidueEvent m) (β : TraceTemperature) (t : ℝ) :
    charFun (conditionalEnergyLaw m A β : Measure ℝ) t =
      (∑' n : ℕ+, (eventWeight m A.val β n : ℂ) *
        Complex.exp (-(fourierFrequency t).val * (rescaledEnergy β n : ℂ))) /
        ((∑' n, eventWeight m A.val β n : ℝ) : ℂ) := by
  rw [charFun_apply_real]
  unfold conditionalEnergyLaw
  simp only [ProbabilityMeasure.coe_mk]
  have hnorm (x : ℝ) : ‖Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top) (by
    simpa only [ENNReal.toReal_ofReal (conditionalWeight_nonneg m A β _), hnorm, mul_one] using
      (conditionalWeight_hasSum m A β).summable)]
  rw [← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [ENNReal.toReal_ofReal (conditionalWeight_nonneg m A β n), Complex.real_smul,
    conditionalWeight, Complex.ofReal_div]
  have he : (t : ℂ) * (rescaledEnergy β n : ℂ) * Complex.I =
      -(fourierFrequency t).val * (rescaledEnergy β n : ℂ) := by
    dsimp only [fourierFrequency]
    ring
  rw [he, div_mul_eq_mul_div]

/-- Indicator observable of a finite residue event. -/
def eventReadout {m : ℕ+} (A : ResidueEvent m) (j : ZMod (m : ℕ)) : ℂ :=
  if j ∈ A.val then 1 else 0

private theorem event_weight_coe (m : ℕ+) (A : ResidueEvent m) (β : TraceTemperature) (n : ℕ+) :
    (eventWeight m A.val β n : ℂ) = eventReadout A (n : ℕ) * (thermalWeight β n : ℂ) := by
  unfold eventReadout eventWeight
  split <;> simp

private theorem event_weight_mean (m : ℕ+) (A : ResidueEvent m) (β : TraceTemperature) :
    periodicGibbsMean m (eventReadout A) β =
      ((∑' n, eventWeight m A.val β n : ℝ) : ℂ) / riemannZeta β.val := by
  rw [periodicGibbsMean, periodicGibbs_trace_series, partition_eq_zeta, Complex.ofReal_tsum]
  congr 1
  refine tsum_congr fun n => ?_
  rw [event_weight_coe]
  congr 1
  simp only [heat, thermalWeight, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]

theorem conditionalEnergyLaw_fourier (m : ℕ+) (A : ResidueEvent m) (β : TraceTemperature) (t : ℝ) :
    charFun (conditionalEnergyLaw m A β : Measure ℝ) t =
      energyResidueTransform m (eventReadout A) (fourierFrequency t) β /
        periodicGibbsMean m (eventReadout A) β := by
  have hB : 0 < ∑' n, thermalWeight β n :=
    (thermalWeight_pos β 1).trans_le ((thermalWeight_summable β).le_tsum 1 (fun n _ => (thermalWeight_pos β n).le))
  have hz : riemannZeta (β.val : ℂ) ≠ 0 := by
    rw [← thermalWeight_partition]
    exact Complex.ofReal_ne_zero.mpr hB.ne'
  rw [charFun_conditionalEnergyLaw, energyResidueTransform_series, event_weight_mean,
    div_div_div_cancel_right₀ hz]
  simp_rw [event_weight_coe]

/-- Weak convergence to the unit exponential law after conditioning on any fixed residue event. -/
theorem conditionalEnergyLaw_limit (m : ℕ+) (A : ResidueEvent m) :
    Tendsto (conditionalEnergyLaw m A) atPartitionPole
      (𝓝 _root_.RHTower.mobiusCriticalExponentialProbabilityMeasure) := by
  have hsum : (∑ j, eventReadout A j) = (A.val.card : ℂ) := by
    unfold eventReadout
    rw [Finset.sum_boole]
    simp
  have hc : (∑ j, eventReadout A j) / ((m : ℕ) : ℂ) ≠ 0 := by
    rw [hsum]
    exact div_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr A.property).ne')
      (Nat.cast_ne_zero.mpr m.ne_zero)
  haveI : atPartitionPole.IsCountablyGenerated := by unfold atPartitionPole; infer_instance
  rw [tendsto_iff_seq_tendsto]
  intro seq hs
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have h := ((energyResidueTransform_limit m (eventReadout A) (fourierFrequency t)).div
    (periodicGibbsMean_limit m (eventReadout A)) hc).comp hs
  rw [_root_.RHTower.charFun_mobiusCriticalExponentialProbabilityMeasure]
  let c := (∑ j, eventReadout A j) / ((m : ℕ) : ℂ)
  have he : (c / (1 + (fourierFrequency t).val)) / c = (1 - (t : ℂ)*Complex.I)⁻¹ := by
    rw [div_right_comm, div_self hc, one_div]
    simp [fourierFrequency, sub_eq_add_neg]
  rw [he] at h
  exact h.congr' (Eventually.of_forall fun j => (conditionalEnergyLaw_fourier m A (seq j) t).symm)

#print axioms energyMoment_domain_iff
#print axioms heat_tiltTemperature
#print axioms energyResidueTransform_series
#print axioms energyResidueTransform_limit
#print axioms conditionalEnergyLaw_fourier
#print axioms conditionalEnergyLaw_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
