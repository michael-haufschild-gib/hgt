import GaloisForLFunctions.HTGeometry.StokesEquivariantSpectrumIntegrality
import GaloisForLFunctions.HTGeometry.StokesGlobalPuiseuxWittLaw

/-!
# Global Witt law on genuine Puiseux monodromy orbits

This module specializes the coefficient-generated global law to local spectra carrying actual
cyclic Puiseux continuation.  Local charge coordinates are the quotient orbits of that
continuation action, not an independently supplied cellular partition.
-/

namespace GaloisForLFunctions.IrregularStokes.EquivariantGlobalWitt

noncomputable section

variable {p : ℕ}
variable {m K N : Fin (p + 1) → ℕ}

/-- Equivariant finite Puiseux spectrum at every marked point. -/
abbrev LocalFamily (p : ℕ) (m K N : Fin (p + 1) → ℕ) :=
  (a : Fin (p + 1)) → EquivariantFinitePuiseuxFamily (m a) (K a) (N a)

/-- Number of genuine analytic-continuation orbits at every marked point. -/
noncomputable def orbitCount (f : LocalFamily p m K N) (a : Fin (p + 1)) : ℕ :=
  (f a).orbitClassCount

/-- Global coefficient datum obtained by quotienting every local spectrum by its actual cyclic
continuation action. -/
noncomputable def toGlobalLocalData (f : LocalFamily p m K N) :
    GlobalPuiseuxWitt.LocalData p (orbitCount f) m K N :=
  fun a => (f a).toPuiseuxOrbitCoareaDatum

/-- Compatible global charges on genuine local Stokes-circle orbits. -/
abbrev CompatibleCharges (f : LocalFamily p m K N) :=
  GlobalPuiseuxWitt.compatibleCharges (toGlobalLocalData f)

/-- Fused coefficient-generated Stokes form on genuine monodromy-orbit charges. -/
noncomputable def globalOrbitWittForm (genus : ℕ) (f : LocalFamily p m K N) :
    QuadraticForm ℝ (CompatibleCharges f) :=
  GlobalPuiseuxWitt.globalWittForm genus (toGlobalLocalData f)

/-- The genuine-orbit global form is strictly positive away from zero on the common
physical-rank kernel. -/
theorem globalOrbitWittForm_pos_of_commonRank_eq_zero
    (genus : ℕ) (f : LocalFamily p m K N) {x : CompatibleCharges f}
    (hrank : GlobalPuiseuxWitt.commonRankLinear (toGlobalLocalData f) x = 0)
    (hx : x ≠ 0) :
    0 < globalOrbitWittForm genus f x :=
  GlobalPuiseuxWitt.globalWittForm_pos_of_commonRank_eq_zero
    genus (toGlobalLocalData f) hrank hx

/-- **Global genuine-orbit nonpositive-channel law.** Negative inertia plus global Cartan
nullity is at most one for every genus and every finite family of cyclic coefficient spectra.
The unique possible negative or null channel is common physical rank. -/
theorem globalOrbitWittForm_sigNeg_add_radical_finrank_le_one
    (genus : ℕ) (f : LocalFamily p m K N) :
    sigNeg (globalOrbitWittForm genus f) +
      Module.finrank ℝ (globalOrbitWittForm genus f).radical ≤ 1 :=
  GlobalPuiseuxWitt.globalWittForm_sigNeg_add_radical_finrank_le_one
    genus (toGlobalLocalData f)

end

end GaloisForLFunctions.IrregularStokes.EquivariantGlobalWitt
