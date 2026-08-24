import GaloisForLFunctions.HTGeometry.OnePointPullbackRigidity

/-!
# Shared projective real-line boundary

The one-point compactification of the real line is the common carrier for continuous boundary
symbols and their whole-line multiplication operators.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Continuous complex functions on the one-point compactification of `ℝ`. -/
abbrev ProjectiveBoundary := C(OnePoint ℝ, ℂ)

end GaloisForLFunctions.HTGeometry

