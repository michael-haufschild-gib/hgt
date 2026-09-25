import GaloisForLFunctions.RHTower.SourceZeroHedenmalmOrientationRigidity
import GaloisForLFunctions.RHTower.SelbergThetaSourcePhase

/-!
# Midpoint two-jet classifier for the literal Hedenmalm source flow

The actual zero mode never vanishes at the reflection midpoint. Its source ODE therefore makes
equality of the value and first derivative of the two reflected causal modes at that one point
equivalent to critical-line placement. This reduces the global orientation receiver to a local
source jet; it does not establish that the jets agree.
-/

open Complex
namespace RHTower

noncomputable section

/-- Equality of the literal zero mode and its critical-line-reflected copy through first order
at the reflection midpoint. -/
def SourceZeroHedenmalmMidpointTwoJet (q : XiZeroCopy) : Prop :=
  hedenmalmCausalVolterra (xiSpectralPoint q) 0 =
      hedenmalmCausalVolterra (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) 0 ∧
    deriv (hedenmalmCausalVolterra (xiSpectralPoint q)) 0 =
      deriv (hedenmalmCausalVolterra (xiSpectralPoint (xiZeroCopyLineConjEquiv q))) 0

/-- The actual midpoint two-jet agrees with its reflected copy exactly on the critical line. -/
theorem sourceZeroHedenmalmMidpointTwoJet_iff_re_eq_half (q : XiZeroCopy) :
    SourceZeroHedenmalmMidpointTwoJet q ↔ (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨hvalue, hderiv⟩
    have hstrip := abs_im_xiSpectralPoint_lt_one q
    have hstrip' := abs_im_xiSpectralPoint_lt_one (xiZeroCopyLineConjEquiv q)
    have hode := hedenmalmCausalVolterra_thetaEigen_ode hstrip 0
    have hode' := hedenmalmCausalVolterra_thetaEigen_ode hstrip' 0
    rw [← hvalue, ← hderiv] at hode'
    have hmul :
        (xiSpectralPoint q - xiSpectralPoint (xiZeroCopyLineConjEquiv q)) *
          hedenmalmCausalVolterra (xiSpectralPoint q) 0 = 0 := by
      linear_combination hode - hode'
    have hu : hedenmalmCausalVolterra (xiSpectralPoint q) 0 ≠ 0 := by
      change SelbergThetaSourcePhase.mode q 0 ≠ 0
      exact SelbergThetaSourcePhase.mode_ne_zero q 0
    have hz : xiSpectralPoint q = xiSpectralPoint (xiZeroCopyLineConjEquiv q) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hu)
    rw [xiSpectralPoint_lineConj] at hz
    have him : (xiSpectralPoint q).im = 0 :=
      Complex.conj_eq_iff_im.mp hz.symm
    rw [xiSpectralPoint_im_eq] at him
    linarith
  · intro hline
    have hflow : hedenmalmCausalVolterra (xiSpectralPoint q) =
        hedenmalmCausalVolterra (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) :=
      funext ((sourceZeroHedenmalmOrientationLaw_iff_re_eq_half q).2 hline)
    unfold SourceZeroHedenmalmMidpointTwoJet
    constructor
    · exact congrFun hflow 0
    · exact congrArg (fun f : ℝ → ℂ => deriv f 0) hflow

end
end RHTower
