import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Bulk.Distribution
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Interior
import GaloisForLFunctions.HTGeometry.ProbabilityMeasureSimplex

/-! # Elementary log-energy measurements and the uniform law with terminal mass -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Bulk

open Filter Set Real MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology ENNReal

/-- Read normalized log energy in the unit interval, including the lowest shell. -/
def position (N p : ℕ) : unitInterval :=
  let x := log (log p)/log (log N)
  ⟨max 0 (min 1 x),le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

/-- The compact reading differs uniformly from the raw normalized log energy
by at most the rescaled logarithmic energy of the lowest prime. -/
theorem position_error {p N : ℕ} (hp : p.Prime) (hpN : p≤N) (hL : 0<log (log N)) :
    |(position N p:ℝ) - log (log p)/log (log N)| ≤ |log (log 2)|/log (log N) := by
  let L := log (log N)
  let x := log (log p)/L
  have pp : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have lp := log_pos (show (1:ℝ)<p by exact_mod_cast hp.one_lt)
  have h2 := log_pos (by norm_num : (1:ℝ)<2)
  have upper : x≤1 := (div_le_one hL).mpr (log_le_log lp (log_le_log pp (by exact_mod_cast hpN)))
  have lower : log (log 2)/L≤x := div_le_div_of_nonneg_right
    (log_le_log h2 (log_le_log (by norm_num) (by exact_mod_cast hp.two_le))) hL.le
  change |max 0 (min 1 x)-x|≤_
  rw [min_eq_right upper]
  by_cases hx : 0≤x
  · rw [max_eq_right hx,sub_self,abs_zero]
    exact div_nonneg (abs_nonneg _) hL.le
  · rw [max_eq_left (le_of_not_ge hx),zero_sub,abs_neg,abs_of_neg (lt_of_not_ge hx)]
    calc
      -x ≤ -(log (log 2)/L) := neg_le_neg lower
      _ ≤ |log (log 2)|/L := by rw [←neg_div]; exact div_le_div_of_nonneg_right (neg_le_abs _) hL.le

/-- Label Born law pushed forward by the compact position measurement.
The power index a corresponds to real part (1-a)/2. -/
def positionLaw (a : ℝ) (N : ℕ) : ProbabilityMeasure unitInterval :=
  (labelLaw ((1-a)/2) N).map (show Measurable (position N) from measurable_of_countable _).aemeasurable

private theorem position_le {N p : ℕ} {u : ℝ} (hu : 0<u) (hu' : u<1) (hL : 0<log (log N)) :
    (position N p:ℝ)≤u ↔ (p:ℝ) ≤ interiorCutoff u N := by
  change max 0 (min 1 (log (log p)/log (log N))) ≤ u ↔ _
  rw [max_le_iff,min_le_iff,or_iff_right hu'.not_ge,and_iff_right hu.le,div_le_iff₀ hL]
  by_cases pp : 1<p
  · have lp := log_pos (show (1:ℝ)<p by exact_mod_cast pp)
    have ppos := (Nat.cast_pos.mpr (by omega : 0<p) : 0<(p:ℝ))
    rw [log_le_iff_le_exp lp,log_le_iff_le_exp ppos,interiorCutoff,logEnergyCutoff]
  · have bound : (p:ℝ)≤1 := by exact_mod_cast (le_of_not_gt pp)
    have top : 1 ≤ interiorCutoff u N := (one_lt_exp_iff.mpr (exp_pos _)).le
    have p01 : p=0 ∨ p=1 := by omega
    rcases p01 with rfl | rfl <;>
      simpa only [Nat.cast_zero,Nat.cast_one,log_zero,log_one] using
        (iff_of_true (mul_nonneg hu.le hL.le) (bound.trans top))

/-- Every interior event is exactly a lower packet at the corresponding cutoff. -/
theorem position_cdf_eq (a : ℕ → ℝ) {u : ℝ} (hu : 0<u) (hu' : u<1) :
    ∀ᶠ N in atTop, cdf (positionLaw (a N) N) u =
      powerMass (a N) (interiorCutoff u N)/powerMass (a N) N := by
  filter_upwards [logEnergy_growth.eventually_gt_atTop 0,(interior_growth hu).eventually_ge_atTop 2,
    eventually_ge_atTop 2] with N hL hy h2
  have lp := log_pos (show (1:ℝ)<N by exact_mod_cast (by omega : 1<N))
  have up : interiorCutoff u N ≤ N := by
    calc
      _ ≤ exp (exp (log (log N))) := exp_le_exp.mpr (exp_le_exp.mpr
        (mul_le_of_le_one_left hL.le hu'.le))
      _ = _ := by rw [exp_log lp,exp_log (Nat.cast_pos.mpr (by omega : 0<N))]
  change ((labelLaw ((1-a N)/2) N : Measure ℕ).map (position N)).real _ = _
  rw [map_measureReal_apply (measurable_of_countable _) (measurableSet_le measurable_subtype_coe measurable_const)]
  have event : (position N) ⁻¹' {x : unitInterval | (x:ℝ)≤u} = {p : ℕ | (p:ℝ) ≤ interiorCutoff u N} :=
    Set.ext (fun _ => position_le hu hu' hL)
  rw [event,initial_measured _ hy up,show 1-2*((1-a N)/2)=a N by ring]

def uniformPosition : ProbabilityMeasure unitInterval := ⟨volume,inferInstance⟩

/-- Uniform log-energy bulk of weight r, with all other mass at the terminal endpoint. -/
def bulkAndEndpoint (r : unitInterval) : ProbabilityMeasure unitInterval :=
  probabilityMixture (ENNReal.ofReal r) (ENNReal.ofReal_le_one.mpr r.property.2)
    uniformPosition ⟨Measure.dirac 1,inferInstance⟩

private theorem level_set {u : ℝ} (hu : 0<u) (hu' : u<1) :
    {x : unitInterval | (x:ℝ)≤u} = Iic (⟨u,hu.le,hu'.le⟩ : unitInterval) := rfl

theorem uniform_cdf {u : ℝ} (hu : 0<u) (hu' : u<1) : cdf uniformPosition u = u := by
  change (volume {x : unitInterval | (x:ℝ)≤u}).toReal = _
  rw [level_set hu hu',unitInterval.volume_Iic,ENNReal.toReal_ofReal hu.le]

theorem mixture_cdf (r : unitInterval) {u : ℝ} (hu : 0<u) (hu' : u<1) :
    cdf (bulkAndEndpoint r) u = (r:ℝ)*u := by
  let B := {x : unitInterval | (x:ℝ)≤u}
  have absent : (1:unitInterval)∉B := hu'.not_ge
  have dead : Measure.dirac (1:unitInterval) B = 0 := by
    rw [Measure.dirac_apply' _ (show MeasurableSet B from
      measurableSet_le measurable_subtype_coe measurable_const)]
    exact Set.indicator_of_notMem absent _
  change ((ENNReal.ofReal (r:ℝ) • (volume : Measure unitInterval) +
    (1-ENNReal.ofReal (r:ℝ)) • Measure.dirac (1:unitInterval)) B).toReal = _
  rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,dead]
  simp only [smul_eq_mul,mul_zero,add_zero,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal r.property.1]
  change (r:ℝ)*cdf uniformPosition u = _
  rw [uniform_cdf hu hu']

#print axioms position_error
#print axioms position_cdf_eq
#print axioms uniform_cdf
#print axioms mixture_cdf

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Bulk
