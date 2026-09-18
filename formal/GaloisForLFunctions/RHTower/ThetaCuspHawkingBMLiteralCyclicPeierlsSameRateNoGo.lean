import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsLiftDefect
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeAmplitudeHomogeneity

/-!
# Same-rate no-go for the literal cyclic Peierls source pairing

Each original source leg is quadratic in its independently chosen physical
amplitude.  Therefore a two-source causal pairing is biquadratic.  Combining
that fact with the literal integral antisymmetry proves that every same-rate
pairing vanishes, even for unequal independent amplitudes.

Proof-chain role:
`literal source homogeneity + two-event Peierls antisymmetry -> same-rate
scalar pairing and lift defect vanish -> B2 must use a complementary-rate
source-to-metric-current intertwiner, not a same-branch scalar identification`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsSameRateNoGo

open MeasureTheory
open D4BMJointSource D4BMFullSourceReciprocity
open D4BMFullAngularCausalPeierls D4BMLiteralCyclicPeierlsLiftDefect

noncomputable section
set_option autoImplicit false

/-- The native two-event density is biquadratic in its two independently
chosen source amplitudes. -/
theorem sourcePairDensity_amplitude_biquadratic (q : XiZeroCopy) (b c : Bool)
    (a d : ℂ) (X k : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) :
    sourcePairDensity q b c a d X k z =
      a ^ 2 * d ^ 2 * sourcePairDensity q b c 1 1 X k z := by
  unfold sourcePairDensity
  rw [timeReducedCoefficient_amplitude_square,
    timeReducedCoefficient_amplitude_square]
  ring

/-- The native causal source pairing inherits the exact biquadratic
amplitude degree of its two literal source events. -/
theorem causalSourcePair_amplitude_biquadratic (q : XiZeroCopy) (b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    causalSourcePair q b c a d X k =
      a ^ 2 * d ^ 2 * causalSourcePair q b c 1 1 X k := by
  rw [causalSourcePair_decomposition, causalSourcePair_decomposition]
  simp_rw [sourcePairDensity_amplitude_biquadratic]
  rw [integral_const_mul, integral_const_mul]
  ring

/-- A native causal Peierls pairing has no same-rate component, even after
polarizing its two independent source amplitudes. -/
theorem causalSourcePair_same_rate_zero (q : XiZeroCopy) (b : Bool)
    (a d : ℂ) (X k : ℝ) :
    causalSourcePair q b b a d X k = 0 := by
  rw [causalSourcePair_amplitude_biquadratic,
    causalSourcePair_self q b 1 X k]
  ring

/-- The literal full-circle two-event density is biquadratic in the same
independent source amplitudes. -/
theorem fullSourcePairDensity_amplitude_biquadratic (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) :
    fullSourcePairDensity q branch b c a d X k z =
      a ^ 2 * d ^ 2 * fullSourcePairDensity q branch b c 1 1 X k z := by
  unfold fullSourcePairDensity
  rw [timeReducedCoefficient_amplitude_square,
    timeReducedCoefficient_amplitude_square]
  ring

/-- The literal full-circle causal pairing has the exact biquadratic source
degree before any cap or metric boundary comparison. -/
theorem fullCausalSourcePair_amplitude_biquadratic (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    fullCausalSourcePair q branch b c a d X k =
      a ^ 2 * d ^ 2 * fullCausalSourcePair q branch b c 1 1 X k := by
  rw [fullCausalSourcePair_decomposition, fullCausalSourcePair_decomposition]
  simp_rw [fullSourcePairDensity_amplitude_biquadratic]
  rw [integral_const_mul, integral_const_mul]
  ring

/-- The literal full-circle Peierls pairing vanishes on every same-rate pair,
not merely on the diagonal `a = d`.  This is an unconditional obstruction to
identifying a same-branch scalar Peierls pairing with a nonzero B2 contact. -/
theorem fullCausalSourcePair_same_rate_zero (q : XiZeroCopy)
    (branch b : Bool) (a d : ℂ) (X k : ℝ) :
    fullCausalSourcePair q branch b b a d X k = 0 := by
  rw [fullCausalSourcePair_amplitude_biquadratic,
    fullCausalSourcePair_self q branch b 1 X k]
  ring

/-- The full-minus-native lift has no same-rate component either.  Thus the
literal lift cannot supply the missing same-branch B2 contact; a surviving B2
realization must be complementary-rate and explicitly metric-valued. -/
theorem causalSourceLiftDefect_same_rate_zero (q : XiZeroCopy)
    (branch b : Bool) (a d : ℂ) (X k : ℝ) :
    causalSourceLiftDefect q branch b b a d X k = 0 := by
  have h := fullCausalSourcePair_eq_native_add_liftDefect q branch b b a d X k
  rw [fullCausalSourcePair_same_rate_zero, causalSourcePair_same_rate_zero,
    zero_add] at h
  exact h.symm

end

end RHTower.D4BMLiteralCyclicPeierlsSameRateNoGo
