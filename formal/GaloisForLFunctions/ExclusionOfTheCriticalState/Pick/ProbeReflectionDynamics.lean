import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeReflectionChannel
import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockDephasing
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The reflection Lindblad flow on actual zero observables

Exponential damping removes the odd reflection component. Its actual
derivative is minus one quarter of the reflection double commutator, and
the flow converges in operator norm to the reflection-even component.
-/

noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk

/-- Real-time extension of the reflection dephasing semigroup. -/
def reflectionFlow (t : ℝ) (A : ZeroObservable) : ZeroObservable :=
  reflectionAttenuation (Real.exp (-t) : ℂ) A

/-- The reflection Lindblad generator, normalized to decay cross-sector terms at unit rate. -/
def reflectionGenerator (A : ZeroObservable) : ZeroObservable := -oddObservable A

theorem reflectionFlow_nonnegative (t : NNReal) (A : ZeroObservable) :
    reflectionFlow t A = reflectionDephasing t A := rfl

theorem reflectionGenerator_doubleCommutator (A : ZeroObservable) :
    reflectionGenerator A = -(1 / 4 : ℂ) •
      _root_.HTGeometry.finiteInvolutiveClockDoubleCommutator zeroReflection A := by
  rw [_root_.HTGeometry.finiteInvolutiveClockDoubleCommutator]
  simp only [mul_sub, sub_mul, ← mul_assoc, zeroReflection_sq, one_mul]
  rw [mul_assoc A zeroReflection zeroReflection, zeroReflection_sq, mul_one]
  unfold reflectionGenerator oddObservable reflectedObservable
  module

private theorem odd_reflectionFlow (t : ℝ) (A : ZeroObservable) :
    oddObservable (reflectionFlow t A) = (Real.exp (-t) : ℂ) • oddObservable A := by
  unfold reflectionFlow reflectionAttenuation
  rw [oddObservable, reflectedObservable_add, reflectedObservable_smul,
    reflectedObservable_even, reflectedObservable_odd]
  module

/-- The exact observable flow solves the bounded reflection Lindblad equation. -/
theorem reflectionFlow_hasDerivAt (t : ℝ) (A : ZeroObservable) :
    HasDerivAt (fun s : ℝ => reflectionFlow s A)
      (reflectionGenerator (reflectionFlow t A)) t := by
  have hreal : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t :=
    Complex.ofRealCLM.hasDerivAt
  have h := hreal.neg.cexp
  have hd := (h.smul_const (oddObservable A)).const_add (evenObservable A)
  simp only [Pi.neg_apply, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    mul_neg_one] at hd
  simp only [Complex.ofReal_neg, neg_smul] at hd
  rw [reflectionGenerator, odd_reflectionFlow]
  simpa only [reflectionFlow, reflectionAttenuation] using hd

/-- The bounded generator vanishes precisely on the actual reflection commutant. -/
theorem reflectionGenerator_zero_iff (A : ZeroObservable) :
    reflectionGenerator A = 0 ↔ zeroReflection * A = A * zeroReflection := by
  rw [reflectionGenerator_doubleCommutator, smul_eq_zero]
  simp only [neg_eq_zero, one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  exact _root_.HTGeometry.finiteInvolutiveClockDoubleCommutator_eq_zero_iff_commutes
    zeroReflection A (by simpa only [pow_two] using zeroReflection_sq)

/-- The flow converges in operator norm to reflection averaging. -/
theorem reflectionFlow_tendsto (A : ZeroObservable) :
    Tendsto (fun t : ℝ => reflectionFlow t A) atTop (𝓝 (evenObservable A)) := by
  have he : Tendsto (fun t : ℝ => (Real.exp (-t) : ℂ)) atTop (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
  simpa only [reflectionFlow, reflectionAttenuation, zero_smul, add_zero] using
    (he.smul (tendsto_const_nhds (x := oddObservable A))).const_add (evenObservable A)

#print axioms reflectionGenerator_doubleCommutator
#print axioms reflectionFlow_hasDerivAt
#print axioms reflectionGenerator_zero_iff
#print axioms reflectionFlow_tendsto
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
