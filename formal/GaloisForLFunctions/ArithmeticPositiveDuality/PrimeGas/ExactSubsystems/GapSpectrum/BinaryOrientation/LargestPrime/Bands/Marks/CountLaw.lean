import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.GeneratingFunctional
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.VacuumCalibration.Profile
import Mathlib.Probability.Distributions.Poisson.Basic

/-! # Poisson limit for the actual number of occupied prime modes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower
open scoped NNReal

/-- Occupied-prime count as an integer-valued measurement on the real line. -/
def countLaw (c d : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) : ProbabilityMeasure ℝ :=
  observed (added c d h) s fun x => ((squarefreeOccupationFinset x).card:ℝ)

theorem count_characteristic (c d : ℝ) (h : Ioi (0:ℝ)) (s t : ℝ) :
    charFun (countLaw c d h s : Measure ℝ) t =
      jointMoment (added c d h) s h (Complex.exp ((t:ℂ)*Complex.I)) 0 := by
  change charFun (finiteAtomicObserverSpectrum _ _) t = _
  rw [charFun_finiteAtomicObserverSpectrum _ _ (fun x => (weight_pos _ _ x).le),jointMoment]
  apply Finset.sum_congr rfl
  intro x _
  simp only [zero_mul,Complex.exp_zero,mul_one,← Complex.exp_nat_mul,Complex.ofReal_mul,Complex.ofReal_natCast]
  congr 2
  ring

theorem constant_exponent (c d a : ℝ) (w : ℂ) :
    exponent c d a (fun _ => w) = (w-1)*(VacuumCalibration.mass c d a:ℂ) := by
  rw [exponent,VacuumCalibration.mass,← intervalIntegral.integral_ofReal,← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun v _ => by simp only [tilt,Complex.ofReal_div]; ring

theorem mass_nonneg {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (a : ℝ) :
    0 ≤ VacuumCalibration.mass c d a :=
  intervalIntegral.integral_nonneg hcd fun _ hv => div_nonneg (Real.exp_pos _).le (hc.trans_le hv.1).le

/-- Poisson counting law embedded by the usual natural-number count observable. -/
def poissonCount (r : ℝ≥0) : ProbabilityMeasure ℝ := ⟨Po(ℝ, r), inferInstance⟩

/-- Every real drift fixes its own Poisson rate through the prime intensity on the band. -/
theorem count_weak_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) :
    Tendsto (fun h => countLaw c d h (1+a*h.val)) criticalApproach
      (𝓝 (poissonCount ⟨VacuumCalibration.mass c d a,mass_nonneg hc hcd.le a⟩)) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  let w := Complex.exp ((t:ℂ)*Complex.I)
  have H := joint_limit hc hcd a w 0
  simp only [zero_mul,Complex.exp_zero,mul_one,constant_exponent] at H
  let r : ℝ≥0 := ⟨VacuumCalibration.mass c d a,mass_nonneg hc hcd.le a⟩
  change Tendsto _ atTop (𝓝 (charFun Po(ℝ, r) t))
  rw [charFun_map_cast_poissonMeasure,mul_comm ((r:ℝ):ℂ)]
  exact (H.congr fun h => (count_characteristic c d h _ t).symm).comp hu

/-- At isometric damping every multiplicative octave has the same Poisson law. -/
theorem doubled_count_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun h => countLaw c (2*c) h 1) criticalApproach
      (𝓝 (poissonCount ⟨Real.log 2,(Real.log_pos one_lt_two).le⟩)) := by
  have hcd : c < 2*c := by linarith only [hc]
  have H := count_weak_limit hc hcd 0
  have hm : VacuumCalibration.mass c (2*c) 0 = Real.log 2 := by
    simp only [VacuumCalibration.mass,neg_zero,zero_mul,Real.exp_zero,
      integral_one_div_of_pos hc (hc.trans hcd),mul_div_cancel_right₀ _ hc.ne']
  have hr : (⟨VacuumCalibration.mass c (2*c) 0,mass_nonneg hc hcd.le 0⟩ : ℝ≥0) =
      ⟨Real.log 2,(Real.log_pos one_lt_two).le⟩ := Subtype.ext hm
  simpa only [zero_mul,add_zero,hr] using H

#print axioms count_characteristic
#print axioms constant_exponent
#print axioms mass_nonneg
#print axioms count_weak_limit
#print axioms doubled_count_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks
