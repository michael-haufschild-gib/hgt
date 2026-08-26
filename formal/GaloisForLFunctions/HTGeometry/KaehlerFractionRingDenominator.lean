import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Clearing denominators in fraction-field Kähler differentials

The canonical map from a domain's Kähler differentials to those of its fraction field is a
localized-module map.  Consequently, a differential that vanishes generically is annihilated by
one nonzero denominator in the original ring.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped nonZeroDivisors

/-- If a Kähler differential becomes zero in the fraction field, one nonzero element of the
original domain annihilates it. -/
theorem exists_nonzero_smul_eq_zero_of_map_fractionRing_eq_zero
    {k R : Type*} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {w : Ω[R⁄k]}
    (h : KaehlerDifferential.map k k R (FractionRing R) w = 0) :
    ∃ s : R, s ≠ 0 ∧ s • w = 0 := by
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff
    (nonZeroDivisors R) (KaehlerDifferential.map k k R (FractionRing R))).mp h
  refine ⟨s, ?_, hs⟩
  intro hzero
  have hone : (1 : R) = 0 := s.2.1 1 (by simp [hzero])
  exact one_ne_zero hone

end GaloisForLFunctions.HTGeometry
