import GaloisForLFunctions.RHTower.CCMRationalMoritaTraceNormAlgebra

/-!
# Unit norm of the trace-norm minimal unitization

The exact `ℓ¹` unitization norm is `|z| + ‖T‖₁`; therefore its identity has
norm one.  Registering this fact supplies the missing hypothesis for
projective continuity of Connes degeneracies.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

noncomputable instance ccmRationalMoritaTraceNormL1NormOneClass :
    NormOneClass CCMRationalMoritaTraceNormL1Unitization where
  norm_one := by
    rw [ccmRationalMoritaTraceNormL1_norm]
    change ‖(1 : ℂ)‖ +
      _root_.RHTower.traceNorm CCMRationalMoritaHilbert
        (0 : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) = 1
    rw [norm_one, _root_.RHTower.traceNorm_zero, add_zero]

end GaloisForLFunctions.RHTower
