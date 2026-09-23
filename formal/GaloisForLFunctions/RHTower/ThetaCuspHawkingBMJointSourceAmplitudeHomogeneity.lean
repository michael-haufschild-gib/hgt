import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceAmplitude

/-!
# Quadratic amplitude homogeneity of the literal source

The original source amplitude carries the physical amplitude squared on each
leg.  This exact identity is the amplitude input for testing whether an
antisymmetric Peierls pairing can realize a same-rate quadratic contact.
-/

namespace RHTower.D4BMJointSource

noncomputable section
set_option autoImplicit false

/-- Every literal source leg is quadratic in its physical amplitude. -/
theorem sourceAmplitude_amplitude_square (s w a T : ℂ) (t : ℝ) :
    sourceAmplitude s w a T t =
      a ^ (2 : ℕ) * sourceAmplitude s w 1 T t := by
  unfold sourceAmplitude
  ring

end

end RHTower.D4BMJointSource
