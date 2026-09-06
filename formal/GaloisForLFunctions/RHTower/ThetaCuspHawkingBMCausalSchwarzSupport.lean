import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicSchwarzPolarization

/-!
# BM causal time support and Schwarz reality

For the actual convention `exp(-I * omega * t)`, pointwise conjugation transports frequency
by `omega ↦ -conj omega` and preserves the positive-time support. Time reversal instead
exchanges the two time supports and transports frequency by `omega ↦ -omega`.

The exact BM opposite branch at conjugate angular parameter is the former transformation.
Its fundamental and second-harmonic sources therefore remain retarded under conjugation.
The positive-time transform is the literal `I/(target-source)` multiplier already used by
the HB causal convolution; its convergence chamber is also preserved by negative conjugation.

These are time-supported sources, not augmented inverse Green operators. In particular,
an abstract retarded-to-advanced channel-Schwarz exchange law is an additional physical
identification, not a consequence of the source's ordinary complex reality. Existing
Schwarz-exchanged operator-class no-gos remain valid under their stated assumptions.
No causal radial/left-QNM operator or RH extinction law is asserted here.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- Literal positive-time BM exponential source, with value one at turn-on. -/
def d4BMRetardedTimeMode (omega : ℂ) (t : ℝ) : ℂ :=
  if 0 ≤ t then Complex.exp (-Complex.I * omega * t) else 0

/-- Literal negative-time exponential source. This is a source, not an inverse Green kernel. -/
def d4BMAdvancedTimeMode (omega : ℂ) (t : ℝ) : ℂ :=
  if t ≤ 0 then Complex.exp (-Complex.I * omega * t) else 0

/-- Exact nonzero support of every retarded mode. No frequency or damping premise is needed. -/
theorem support_d4BMRetardedTimeMode (omega : ℂ) :
    Function.support (d4BMRetardedTimeMode omega) = Ici 0 := by
  ext t
  by_cases ht : 0 ≤ t <;> simp [Function.mem_support, d4BMRetardedTimeMode, ht]

/-- Exact nonzero support of every advanced mode. -/
theorem support_d4BMAdvancedTimeMode (omega : ℂ) :
    Function.support (d4BMAdvancedTimeMode omega) = Iic 0 := by
  ext t
  by_cases ht : t ≤ 0 <;> simp [Function.mem_support, d4BMAdvancedTimeMode, ht]

/-- Pointwise conjugation preserves retarded support and sends frequency to minus conjugate. -/
theorem d4BMRetardedTimeMode_conj (omega : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (d4BMRetardedTimeMode omega t) =
      d4BMRetardedTimeMode (-((starRingEnd ℂ) omega)) t := by
  by_cases ht : 0 ≤ t
  · simp only [d4BMRetardedTimeMode, if_pos ht, ← Complex.exp_conj,
      map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    ring
  · simp [d4BMRetardedTimeMode, ht]

/-- Conjugation also preserves advanced support; it does not reverse time. -/
theorem d4BMAdvancedTimeMode_conj (omega : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (d4BMAdvancedTimeMode omega t) =
      d4BMAdvancedTimeMode (-((starRingEnd ℂ) omega)) t := by
  by_cases ht : t ≤ 0
  · simp only [d4BMAdvancedTimeMode, if_pos ht, ← Complex.exp_conj,
      map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    ring
  · simp [d4BMAdvancedTimeMode, ht]

/-- Actual time reversal swaps the causal support and negates frequency without conjugation. -/
theorem d4BMRetardedTimeMode_timeReverse (omega : ℂ) (t : ℝ) :
    d4BMRetardedTimeMode omega (-t) = d4BMAdvancedTimeMode (-omega) t := by
  simp only [d4BMRetardedTimeMode, d4BMAdvancedTimeMode, neg_nonneg, Complex.ofReal_neg]
  split_ifs
  · congr 1
    ring
  · rfl

/-- No conjugated nonzero retarded mode is any advanced mode: positive-time support separates
these functions, independently of both frequencies. -/
theorem d4BMRetardedTimeMode_conj_ne_advanced (omega eta : ℂ) :
    (fun t : ℝ => (starRingEnd ℂ) (d4BMRetardedTimeMode omega t)) ≠
      d4BMAdvancedTimeMode eta := by
  intro h
  have h1 := congrFun h 1
  rw [d4BMRetardedTimeMode_conj] at h1
  norm_num [d4BMRetardedTimeMode, d4BMAdvancedTimeMode] at h1

/-- Ordinary conjugation has exactly the original retarded support. -/
theorem support_conj_d4BMRetardedTimeMode (omega : ℂ) :
    Function.support (fun t : ℝ => (starRingEnd ℂ) (d4BMRetardedTimeMode omega t)) =
      Ici 0 := by
  simp_rw [d4BMRetardedTimeMode_conj]
  exact support_d4BMRetardedTimeMode _

/-- The actual BM opposite branch at conjugate momentum is the negative-conjugate frequency. -/
theorem d4BMCausalQNMMinus_conj_momentum (n : ℕ) (chi : ℂ) :
    d4BMCausalQNMMinus n ((starRingEnd ℂ) chi) =
      -((starRingEnd ℂ) (d4BMCausalQNMPlus n chi)) := by
  simp [d4BMCausalQNMMinus, d4BMCausalQNMPlus, d4BMCausalDecay,
    map_sub, map_mul, map_ofNat, Complex.conj_I]
  ring

/-- Fundamental BM channel reality transports momentum while retaining positive-time support. -/
theorem d4BMRetardedTimeMode_qnmPlus_conj (n : ℕ) (chi : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (d4BMRetardedTimeMode (d4BMCausalQNMPlus n chi) t) =
      d4BMRetardedTimeMode (d4BMCausalQNMMinus n ((starRingEnd ℂ) chi)) t := by
  rw [d4BMRetardedTimeMode_conj, d4BMCausalQNMMinus_conj_momentum]

/-- The retained second-harmonic source obeys the same support-preserving Schwarz law. -/
theorem d4BMRetardedTimeMode_plusPlus_conj (n : ℕ) (chi : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (d4BMRetardedTimeMode (d4BMCausalPlusPlusFrequency n chi) t) =
      d4BMRetardedTimeMode (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi)) t := by
  rw [d4BMRetardedTimeMode_conj, d4BMCausalMinusMinusFrequency_schwarz]

/-- On real momentum, ordinary BM channel conjugation remains within the retarded pair. -/
theorem d4BMRetardedTimeMode_qnmPlus_ofReal_conj (n : ℕ) (chi t : ℝ) :
    (starRingEnd ℂ) (d4BMRetardedTimeMode (d4BMCausalQNMPlus n chi) t) =
      d4BMRetardedTimeMode (d4BMCausalQNMMinus n chi) t := by
  simpa using d4BMRetardedTimeMode_qnmPlus_conj n (chi : ℂ) t

/-- Literal weighted positive-time source equals one complex exponential on its support. -/
theorem d4BMRetardedTimeMode_weighted_of_nonneg
    (target source : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    Complex.exp (Complex.I * target * t) * d4BMRetardedTimeMode source t =
      Complex.exp ((Complex.I * (target - source)) * t) := by
  rw [d4BMRetardedTimeMode, if_pos ht, ← Complex.exp_add]
  congr 1
  ring

/-- The genuine positive-time transform is the existing HB retarded turn-on multiplier. -/
theorem integral_d4BMRetardedTimeMode_eq_turnOnMultiplier
    (target source : ℂ) (h : source.im < target.im) :
    (∫ t : ℝ in Ioi 0,
      Complex.exp (Complex.I * target * t) * d4BMRetardedTimeMode source t) =
      Complex.I / (target - source) := by
  have hdecay : (Complex.I * (target - source)).re < 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im]
    linarith
  have heq : (∫ t : ℝ in Ioi 0,
      Complex.exp (Complex.I * target * t) * d4BMRetardedTimeMode source t) =
      ∫ t : ℝ in Ioi 0, Complex.exp ((Complex.I * (target - source)) * t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact d4BMRetardedTimeMode_weighted_of_nonneg target source t (le_of_lt ht)
  rw [heq, integral_exp_mul_complex_Ioi hdecay 0]
  have hne : target - source ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    simp only [Complex.sub_im, Complex.zero_im] at him
    linarith
  field_simp
  simp [Complex.I_sq]

/-- The advanced source has the opposite oriented half-line transform, on its own convergence
chamber. This concerns the source transform, without claiming an inverse Green equation. -/
theorem integral_d4BMAdvancedTimeMode_eq_neg_turnOnMultiplier
    (target source : ℂ) (h : target.im < source.im) :
    (∫ t : ℝ in Iic 0,
      Complex.exp (Complex.I * target * t) * d4BMAdvancedTimeMode source t) =
      -(Complex.I / (target - source)) := by
  have hdecay : 0 < (Complex.I * (target - source)).re := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im]
    linarith
  have heq : (∫ t : ℝ in Iic 0,
      Complex.exp (Complex.I * target * t) * d4BMAdvancedTimeMode source t) =
      ∫ t : ℝ in Iic 0, Complex.exp ((Complex.I * (target - source)) * t) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    change Complex.exp (Complex.I * target * t) * d4BMAdvancedTimeMode source t =
      Complex.exp ((Complex.I * (target - source)) * t)
    have ht0 : t ≤ 0 := ht
    rw [d4BMAdvancedTimeMode, if_pos ht0, ← Complex.exp_add]
    congr 1
    ring
  rw [heq, integral_exp_mul_complex_Iic hdecay 0]
  have hne : target - source ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    simp only [Complex.sub_im, Complex.zero_im] at him
    linarith
  field_simp
  simp [Complex.I_sq]

/-- Negative conjugation preserves the retarded transform's convergence chamber. -/
theorem d4BMRetardedTimeMode_schwarz_convergence (target source : ℂ) :
    (-((starRingEnd ℂ) source)).im < (-((starRingEnd ℂ) target)).im ↔
      source.im < target.im := by
  simp

/-- The literal retarded transform conjugates under negative conjugation of both frequencies,
within the same convergence chamber and with positive-time support on both sides. -/
theorem integral_d4BMRetardedTimeMode_schwarz
    (target source : ℂ) (h : source.im < target.im) :
    (∫ t : ℝ in Ioi 0,
      Complex.exp (Complex.I * (-((starRingEnd ℂ) target)) * t) *
        d4BMRetardedTimeMode (-((starRingEnd ℂ) source)) t) =
      (starRingEnd ℂ) (∫ t : ℝ in Ioi 0,
        Complex.exp (Complex.I * target * t) * d4BMRetardedTimeMode source t) := by
  rw [integral_d4BMRetardedTimeMode_eq_turnOnMultiplier _ _
      ((d4BMRetardedTimeMode_schwarz_convergence target source).2 h),
    integral_d4BMRetardedTimeMode_eq_turnOnMultiplier target source h]
  simp only [map_div₀, map_sub, Complex.conj_I]
  rw [show -((starRingEnd ℂ) target) - -((starRingEnd ℂ) source) =
      -((starRingEnd ℂ) target - (starRingEnd ℂ) source) by ring]
  simp only [div_neg, neg_div]

end

end RHTower
