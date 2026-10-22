import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicTargetReal

/-!
# Compatibility names for the exact CCM strong cyclic Real structure

`CCMRationalStrongCyclicTargetReal` is the canonical implementation.  This module retains the
short names used by the class-space action and Lefschetz layers without duplicating any theorem or
Real-structure proof.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Short compatibility name for the canonical degreewise strong-target Real structure. -/
abbrev ccmRationalStrongCyclicDegreeKReal :=
  ccmRationalStrongCyclicTargetDegreeKReal

/-- Short compatibility name for the canonical strong-target Real cyclic structure. -/
abbrev ccmRationalStrongCyclicKReal :=
  ccmRationalStrongCyclicTargetKReal

end RHTower
end GaloisForLFunctions
