import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.FiniteSampling
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.CountAtoms

/-! # Single-prime odds and their limiting intensity measure -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount

open Filter Topology Set MeasureTheory _root_.RHTower
open scoped NNReal ENNReal

/-- The occupied-to-empty weight ratio of one mode at thermal drift a. -/
def odds (a : ℝ) (h : Ioi (0:ℝ)) (p : Nat.Primes) : ℝ≥0 :=
  ⟨squarefreePrimeNome (1+a*h.val) p,(squarefreePrimeNome_pos _ _).le⟩

theorem odds_eq (a : ℝ) (h : Ioi (0:ℝ)) (p : Nat.Primes) :
    (odds a h p:ℝ) = Real.exp (-a*location h p)/(p.val:ℝ) := by
  change squarefreePrimeNome _ _ = _
  rw [squarefreePrimeNome_eq_exp,show -(1+a*h.val)*squarefreePrimeEnergy p =
    -a*location h p-squarefreePrimeEnergy p by unfold location; ring,Real.exp_sub,
    squarefreePrimeEnergy,Real.exp_log (Nat.cast_pos.mpr p.property.pos)]

/-- Unnormalized discrete intensity on the measured energy axis. -/
def onePrime (c d a : ℝ) (h : Ioi (0:ℝ)) :=
  atomic (fun p : ↥(added c d h) => odds a h p.val) (fun p => location h p.val)

def densityAt (a v : ℝ) := Real.exp (-a*v)/v

private theorem density_cont {c d : ℝ} (hc : 0 < c) (a : ℝ) :
    ContinuousOn (densityAt a) (Icc c d) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.div continuousOn_id
    (fun v hv => (hc.trans_le hv.1).ne')

theorem mass_pos {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) : 0 < VacuumCalibration.mass c d a := by
  have H := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ => 0) hcd continuousOn_const (density_cont hc a)
    (fun _ hv => (div_pos (Real.exp_pos _) (hc.trans hv.1)).le)
    ⟨c,⟨le_rfl,hcd.le⟩,div_pos (Real.exp_pos _) hc⟩
  simpa only [intervalIntegral.integral_zero] using H

private def raw (c d a : ℝ) :=
  (volume.restrict (Ioc c d)).withDensity (fun v => ENNReal.ofReal (densityAt a v))

private theorem raw_univ {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (a : ℝ) :
    raw c d a univ = ENNReal.ofReal (VacuumCalibration.mass c d a) := by
  have hi : IntervalIntegrable (densityAt a) volume c d := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hcd]
    exact density_cont hc a
  rw [raw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,VacuumCalibration.mass,
    intervalIntegral.integral_of_le hcd]
  apply (ofReal_integral_eq_lintegral_ofReal hi.1 ?_).symm
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioc (a := c) (b := d))] with v hv
  exact (div_pos (Real.exp_pos _) (hc.trans hv.1)).le

/-- Finite intensity with density exp(-av)/v on the observed band. -/
def intensity {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (a : ℝ) : FiniteMeasure ℝ :=
  ⟨raw c d a, ⟨by rw [raw_univ hc hcd]; exact ENNReal.ofReal_lt_top⟩⟩

theorem intensity_mass {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (a : ℝ) :
    ((intensity hc hcd a).mass:ℝ) = VacuumCalibration.mass c d a := by
  have H := congrArg ENNReal.toReal (raw_univ hc hcd a)
  exact H.trans (ENNReal.toReal_ofReal (mass_nonneg hc hcd a))

theorem intensity_integral {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (a : ℝ) (f : ℝ → ℝ) :
    (∫ v, f v ∂(intensity hc hcd a : Measure ℝ)) = ∫ v in c..d, densityAt a v*f v := by
  change (∫ v, f v ∂(volume.restrict (Ioc c d)).withDensity _) = _
  have hm : Measurable (densityAt a) := (Real.measurable_exp.comp (measurable_const.mul measurable_id)).div measurable_id
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal (by simp),intervalIntegral.integral_of_le hcd]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioc (a := c) (b := d))] with v hv
  rw [ENNReal.toReal_ofReal (show 0 ≤ densityAt a v from (div_pos (Real.exp_pos _) (hc.trans hv.1)).le),smul_eq_mul]

/-- Weak convergence of the actual odds-weighted prime locations. -/
theorem onePrime_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) :
    Tendsto (onePrime c d a) criticalApproach (𝓝 (intensity hc hcd.le a)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let g (v : ℝ) := Real.exp (-a*v)*f v
  have hg : Continuous g := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul f.continuous
  have H := (Complex.continuous_re.tendsto _).comp
    (intensity_limit hc hcd (fun v => (g v:ℂ)) (Complex.continuous_ofReal.comp hg))
  have hi : (∫ v in c..d,(g v:ℂ)/(v:ℂ)) = ((∫ v in c..d, densityAt a v*f v:ℝ):ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [g,densityAt,Complex.ofReal_div,Complex.ofReal_mul]
    ring
  rw [hi,Complex.ofReal_re] at H
  rw [intensity_integral]
  apply H.congr
  intro h
  rw [Function.comp_apply,onePrime,atomic_integral,
    Finset.sum_coe_sort (added c d h) (fun p => (odds a h p:ℝ)*f (location h p))]
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_div,← Complex.ofReal_sum,Complex.ofReal_re]
  exact Finset.sum_congr rfl fun p _ => by rw [odds_eq]; dsimp [g]; ring

/-- One draw from the normalized limiting intensity. -/
def draw {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (a : ℝ) := (intensity hc hcd a).normalize

theorem draw_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) :
    Tendsto (fun h => (onePrime c d a h).normalize) criticalApproach (𝓝 (draw hc hcd.le a)) := by
  apply FiniteMeasure.tendsto_normalize_of_tendsto (onePrime_limit hc hcd a)
  apply (FiniteMeasure.mass_nonzero_iff _).mp
  intro hm
  have H := intensity_mass hc hcd.le a
  rw [hm,NNReal.coe_zero] at H
  exact (mass_pos hc hcd a).ne H

theorem partition_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) :
    Tendsto (fun h => finiteSquarefreePartition (added c d h) (1+a*h.val)) criticalApproach
      (𝓝 (Real.exp (VacuumCalibration.mass c d a))) := by
  have H := (VacuumCalibration.drift_limit hc hcd a).inv₀ (Real.exp_pos _).ne'
  simpa only [VacuumCalibration.vacuum_eq,inv_inv,VacuumCalibration.response,Real.exp_neg] using H

#print axioms odds_eq
#print axioms mass_pos
#print axioms intensity_mass
#print axioms intensity_integral
#print axioms onePrime_limit
#print axioms draw_limit
#print axioms partition_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount
