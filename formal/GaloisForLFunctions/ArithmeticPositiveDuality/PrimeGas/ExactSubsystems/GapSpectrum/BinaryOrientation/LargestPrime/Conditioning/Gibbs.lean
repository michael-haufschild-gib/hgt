import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Conditioning.Support
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Limit
import GaloisForLFunctions.RHTower.FiniteAtomicObserverTimeGapLaw
import GaloisForLFunctions.HTGeometry.ExponentialSeedCarrier

/-! # Conditioned Gibbs probabilities and their entire energy transform -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime

open Set MeasureTheory ProbabilityTheory _root_.RHTower

abbrev CutStates (c : ℝ) (h : Ioi (0:ℝ)) := Retained (primeCut c h)

def measuredEnergy (c : ℝ) (h : Ioi (0:ℝ)) (d : CutStates c h) :=
  scaledEnergy h (retainedLabel (primeCut c h) d)

def conditionalWeight (c : ℝ) (h : Ioi (0:ℝ)) (d : CutStates c h) :=
  binaryMass h (retainedLabel (primeCut c h) d)/jointReading c 0 h

theorem conditionalWeight_pos (c : ℝ) (h : Ioi (0:ℝ)) (d : CutStates c h) :
    0 < conditionalWeight c h d :=
  div_pos (div_pos (thermalWeight_pos _ _) (binaryPartition_pos h)) (cutoff_probability_pos c h)

private theorem event_sum (c : ℝ) (h : Ioi (0:ℝ)) :
    jointReading c 0 h = ∑ d : CutStates c h, binaryMass h (retainedLabel _ d) := by
  simp only [jointReading,neg_zero,zero_mul,Real.exp_zero,mul_one]
  exact retained_sum _ _

theorem sum_conditionalWeight (c : ℝ) (h : Ioi (0:ℝ)) :
    ∑ d, conditionalWeight c h d = 1 := by
  simp only [conditionalWeight,← Finset.sum_div,← event_sum,div_self (cutoff_probability_pos c h).ne']

/-- The normalized law of the actual energy labels retained by the largest-prime event. -/
def conditionalLaw (c : ℝ) (h : Ioi (0:ℝ)) : ProbabilityMeasure ℝ :=
  ⟨finiteAtomicObserverSpectrum (conditionalWeight c h) (measuredEnergy c h),
    finiteAtomicObserverSpectrum_isProbabilityMeasure _ _ (fun d => (conditionalWeight_pos c h d).le)
      (sum_conditionalWeight c h)⟩

/-- Conditional average as a restriction of the original, unrestricted squarefree state. -/
theorem conditional_average (c : ℝ) (h : Ioi (0:ℝ)) (f : ℝ → ℂ) :
    (∑' j : SquarefreeLabel, if j.val.val ∈ (primeCut c h+1).smoothNumbers then
      (binaryMass h j:ℂ)*f (scaledEnergy h j) else 0)/(jointReading c 0 h:ℂ) =
    ∑ d : CutStates c h, (conditionalWeight c h d:ℂ)*f (measuredEnergy c h d) := by
  rw [retained_sum,Finset.sum_div]
  exact Finset.sum_congr rfl fun d _ => by
    rw [conditionalWeight,Complex.ofReal_div,div_mul_eq_mul_div,measuredEnergy]

/-- Moments with an optional complex energy probe; order zero is the exponential transform. -/
def momentProbe (c : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) (z : ℂ) :=
  ∑ d : CutStates c h, (conditionalWeight c h d:ℂ)*(measuredEnergy c h d:ℂ)^k*
    Complex.exp (z*(measuredEnergy c h d:ℂ))

theorem transform_derivative (c : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (momentProbe c h 0) z = momentProbe c h k z := by
  let F := fun (d : CutStates c h) (w : ℂ) =>
    (conditionalWeight c h d:ℂ)*Complex.exp ((measuredEnergy c h d:ℂ)*w)
  have hf : momentProbe c h 0 = fun w => ∑ d, F d w := by
    funext w
    simp only [F,momentProbe,pow_zero,mul_one,mul_comm (w:ℂ)]
  rw [hf,iteratedDeriv_fun_sum (fun d _ => (show ContDiffAt ℂ k (F d) z by dsimp [F]; fun_prop))]
  apply Finset.sum_congr rfl
  intro d _
  rw [show iteratedDeriv k (F d) = _ from GaloisForLFunctions.HTGeometry.iteratedDeriv_constMul_expLinear _ _ k]
  change (conditionalWeight c h d:ℂ)*(measuredEnergy c h d:ℂ)^k*Complex.exp ((measuredEnergy c h d:ℂ)*z) = _
  rw [mul_comm (measuredEnergy c h d:ℂ) z]

theorem charFun_conditionalLaw (c : ℝ) (h : Ioi (0:ℝ)) (t : ℝ) :
    charFun (conditionalLaw c h : Measure ℝ) t = momentProbe c h 0 ((t:ℂ)*Complex.I) := by
  change charFun (finiteAtomicObserverSpectrum (conditionalWeight c h) (measuredEnergy c h)) t = _
  rw [charFun_finiteAtomicObserverSpectrum _ _ (fun d => (conditionalWeight_pos c h d).le),momentProbe]
  apply Finset.sum_congr rfl
  intro d _
  simp only [pow_zero,mul_one,Complex.ofReal_mul]
  congr 2
  ring

private def rawTransform (c : ℝ) (h : Ioi (0:ℝ)) (z : ℂ) :=
  ∑ d : CutStates c h, (binaryMass h (retainedLabel _ d):ℂ)*Complex.exp (z*(measuredEnergy c h d:ℂ))

private theorem raw_trace (c : ℝ) (h : Ioi (0:ℝ)) (z : ℂ) :
    rawTransform c h z = Window.partition (primeCut c h) (1+(1-z)*(h.val:ℂ))/(binaryPartition h:ℂ) := by
  rw [rawTransform,← retained_trace,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  rw [binaryMass,Complex.ofReal_div,div_mul_eq_mul_div,thermalWeight,Complex.ofReal_exp,← Complex.exp_add]
  apply congrArg (fun u : ℂ => Complex.exp u/(binaryPartition h:ℂ))
  change ((-(1+h.val)*energy (retainedLabel _ d).val:ℝ):ℂ)+z*((h.val*energy (retainedLabel _ d).val:ℝ):ℂ) = _
  push_cast
  ring

private theorem raw_zero (c : ℝ) (h : Ioi (0:ℝ)) : rawTransform c h 0 = (jointReading c 0 h:ℂ) := by
  simp only [rawTransform,zero_mul,Complex.exp_zero,mul_one,event_sum,Complex.ofReal_sum]

/-- The cutoff makes the exact conditional partition ratio valid at every complex tilt. -/
theorem transform_partition (c : ℝ) (h : Ioi (0:ℝ)) (z : ℂ) :
    momentProbe c h 0 z =
      Window.partition (primeCut c h) (1+(1-z)*(h.val:ℂ))/Window.partition (primeCut c h) (1+(h.val:ℂ)) := by
  have he : momentProbe c h 0 z = rawTransform c h z/rawTransform c h 0 := by
    rw [raw_zero,rawTransform,Finset.sum_div,momentProbe]
    exact Finset.sum_congr rfl fun d _ => by
      rw [pow_zero,mul_one,conditionalWeight,Complex.ofReal_div,div_mul_eq_mul_div]
  have hQ : (binaryPartition h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (binaryPartition_pos h).ne'
  rw [he,raw_trace,raw_trace,sub_zero,one_mul,div_div_div_cancel_right₀ hQ]

theorem laplace_reading (c t : ℝ) (h : Ioi (0:ℝ)) :
    momentProbe c h 0 (-(t:ℂ)) = ((jointReading c t h/jointReading c 0 h:ℝ):ℂ) := by
  rw [Complex.ofReal_div,jointReading,retained_sum,Complex.ofReal_sum,Finset.sum_div,momentProbe]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [conditionalWeight,measuredEnergy,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_exp,
    Complex.ofReal_neg,pow_zero,mul_one,div_mul_eq_mul_div]

#print axioms conditionalWeight_pos
#print axioms sum_conditionalWeight
#print axioms conditional_average
#print axioms transform_derivative
#print axioms charFun_conditionalLaw
#print axioms transform_partition
#print axioms laplace_reading

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime
