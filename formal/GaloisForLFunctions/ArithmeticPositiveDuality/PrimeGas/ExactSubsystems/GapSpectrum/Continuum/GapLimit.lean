import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Continuum.Sampling
import GaloisForLFunctions.RHTower.MobiusCriticalClockWeakConvergence
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # The Laplace limit of the measured Gibbs energy gap -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology MeasureTheory

/-- Positive excess inverse temperature approaching zero. -/
abbrev criticalApproach : Filter (Set.Ioi (0:ℝ)) :=
  comap Subtype.val (𝓝[>] (0:ℝ))

theorem criticalApproach_neBot : NeBot criticalApproach :=
  comap_coe_neBot_of_le_principal inf_le_right

/-- At inverse temperature 1+h, the damping of the opposite-time waves is (1+h)/2. -/
def excessDamping (h : Set.Ioi (0:ℝ)) : ℝ := 1/2+h.val/2

theorem excessDamping_gt (h : Set.Ioi (0:ℝ)) : 1/2 < excessDamping h :=
  lt_add_of_pos_right _ (half_pos h.property)

theorem half_excess_tendsto :
    Tendsto (fun h : Set.Ioi (0:ℝ) => h.val/2) criticalApproach (𝓝[>] 0) := by
  have hv : Tendsto (Subtype.val : Set.Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have hpos (h : Set.Ioi (0:ℝ)) : h.val/2 ∈ Set.Ioi (0:ℝ) := by
    change 0 < h.val/2
    exact half_pos (show 0 < h.val from h.property)
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall hpos⟩
  simpa only [zero_div] using (hv.mono_right nhdsWithin_le_nhds).div_const 2

/-- Each characteristic value is an optimal finite-subsystem overlap at the corresponding clock time. -/
theorem charFun_sampledGapLaw {x : ℝ} (hx : 1/2 < x) (u t : ℝ) :
    charFun (sampledGapLaw x u hx : Measure ℝ) t = (finiteOverlapFloor x (t*u) : ℂ)^2 := by
  rw [charFun_apply_real,sampledGapLaw,ProbabilityMeasure.toMeasure_map,
    integral_map Measurable.of_discrete.aemeasurable (by fun_prop),squared_floor_eq_carrier hx,expSeriesCarrier]
  let f := fun q : ℕ+ × ℕ+ => Complex.exp ((t:ℂ)*((u*gapFrequency q:ℝ):ℂ)*Complex.I)
  have hint : Integrable f (gibbsPairLaw x hx : Measure (ℕ+ × ℕ+)) := by
    refine (integrable_const (1:ℝ)).mono' Measurable.of_discrete.aestronglyMeasurable ?_
    filter_upwards with q
    simp [f,Complex.norm_exp,Complex.mul_re]
  rw [integral_countable hint]
  apply tsum_congr
  intro q
  have hh : 1/4 < x/2 := by linarith
  obtain ⟨a,ha,hea⟩ := commonScaleWeight_positive hh q.1
  obtain ⟨b,hb,heb⟩ := commonScaleWeight_positive hh q.2
  have hw : gapAmplitude x q = ((a*b:ℝ):ℂ) := by
    rw [gapAmplitude_product hx,← hea,← heb,Complex.ofReal_mul]
  rw [measureReal_def,gibbsPairLaw_atom,hw,Complex.ofReal_re,ENNReal.toReal_ofReal (mul_pos ha hb).le]
  change ((a*b:ℝ):ℂ) * f q = ((a*b:ℝ):ℂ) * expChar (gapFrequency q) (t*u)
  congr 1
  unfold f expChar
  congr 1
  push_cast
  ring

/-- The scaled log ratio is h log(m/n) under two normalized Gibbs samples at inverse temperature 1+h. -/
def criticalGapLaw (h : Set.Ioi (0:ℝ)) : ProbabilityMeasure ℝ :=
  sampledGapLaw (excessDamping h) (h.val/2) (excessDamping_gt h)

theorem critical_gap_characteristic (t : ℝ) :
    Tendsto (fun h => charFun (criticalGapLaw h : Measure ℝ) t) criticalApproach
      (𝓝 (((1+t^2:ℝ):ℂ)⁻¹)) := by
  have hl := (finiteOverlapFloor_joint_limit t).comp half_excess_tendsto
  have hpow := ((Complex.continuous_ofReal.tendsto _).comp hl).pow 2
  have hs : ((1/Real.sqrt (1+t^2):ℝ):ℂ)^2 = (((1+t^2:ℝ):ℂ)⁻¹) := by
    rw [← Complex.ofReal_pow,div_pow,one_pow,Real.sq_sqrt (by positivity),one_div,Complex.ofReal_inv]
  rw [hs] at hpow
  apply hpow.congr
  intro h
  exact (charFun_sampledGapLaw (excessDamping_gt h) (h.val/2) t).symm

/-- The rescaled Gibbs gap converges weakly to the probability density exp(-|u|)/2. -/
theorem critical_gap_weak_limit :
    Tendsto criticalGapLaw criticalApproach (𝓝 _root_.RHTower.mobiusCriticalLaplaceGapProbabilityMeasure) := by
  rw [tendsto_iff_seq_tendsto]
  intro h hh
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  rw [_root_.RHTower.charFun_mobiusCriticalLaplaceGapProbabilityMeasure]
  exact (critical_gap_characteristic t).comp hh

#print axioms criticalApproach_neBot
#print axioms excessDamping_gt
#print axioms half_excess_tendsto
#print axioms charFun_sampledGapLaw
#print axioms critical_gap_characteristic
#print axioms critical_gap_weak_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
