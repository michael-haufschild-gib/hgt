import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.NonCoordinate
import GaloisForLFunctions.HTGeometry.PaperFiberClockGeometry
import GaloisForLFunctions.HTGeometry.PaperIntrinsicFiberClocks
import GaloisForLFunctions.HTGeometry.PaperStabilizedAdditiveAction

/-!
# Intrinsic fibre clocks, ambient obstruction, and stabilization

The proved non-coordinate theorem closes the native slice-clock criterion.
Every actual fibre is affine three-space with three intrinsic commuting clocks,
but no locally nilpotent transverse clock exists on the original four-variable
algebra. The existing fifth-variable construction supplies such a clock.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate CoactionLND

/-- The original four-variable polynomial admits no locally nilpotent unit-speed clock. -/
theorem paperFourVariable_no_terminating_clock :
    ¬ ∃ D : Derivation ℂ (R 4) (R 4), D f = 1 ∧
      ∀ p : R 4, ∃ n : ℕ, (D^[n]) p = 0 := by
  intro h
  exact f_not_coordinate (paperFourVariableClock_iff_coordinate.mp h)

/-- No embedded fibre can be straightened by an ambient scheme automorphism. -/
theorem paperFiber_not_schemeRectifiable (t : ℂ) :
    ¬ GeometricInterpretation.IsSchemeRectifiableFiber t := by
  intro h
  exact paperFourVariable_no_terminating_clock
    ((paperFourVariableClock_iff_schemeRectifiable t).mpr h)

/-- Each fibre is intrinsically affine three-space despite its ambient obstruction. -/
theorem paperFiber_affine_and_not_rectifiable (t : ℂ) :
    IsAffineThreeSpaceFiber t ∧ ¬ GeometricInterpretation.IsSchemeRectifiableFiber t :=
  ⟨all_fibers_isAffineThreeSpace t, paperFiber_not_schemeRectifiable t⟩

/-- The polynomial admits intrinsic terminating clocks on every fibre, but no transverse one. -/
theorem paperIntrinsicClocks_without_transverse_clock :
    (∀ (t : ℂ) (i : Fin 3), ∀ p : FiberRing t,
      ∃ n : ℕ, ((paperIntrinsicFiberClock t i)^[n]) p = 0) ∧
      ¬ ∃ D : Derivation ℂ (R 4) (R 4), D f = 1 ∧
        ∀ p : R 4, ∃ n : ℕ, (D^[n]) p = 0 :=
  ⟨paperIntrinsicFiberClock_locallyNilpotent, paperFourVariable_no_terminating_clock⟩

/-- No polynomial additive action on the original algebra translates the distinguished polynomial. -/
theorem paperFourVariable_no_translating_coaction :
    ¬ ∃ ρ : PolynomialAdditiveAction ℂ (R 4),
      ρ.toAlgHom f = Polynomial.C f + Polynomial.X := by
  rintro ⟨ρ, hρ⟩
  apply paperFourVariable_no_terminating_clock
  refine ⟨ρ.derivation, ?_, ρ.locallyNilpotent⟩
  change (ρ.toAlgHom f).coeff 1 = 1
  simp [hρ]

/-- One extra variable changes the exact unit-speed termination problem. -/
theorem paperTerminatingClock_stabilization_boundary :
    (¬ ∃ D : Derivation ℂ (R 4) (R 4), D f = 1 ∧
      ∀ p : R 4, ∃ n : ℕ, (D^[n]) p = 0) ∧
    (paperStabilizedClock (stabilize f) = 1 ∧
      ∀ p : R 5, ∃ n : ℕ, (paperStabilizedClock^[n]) p = 0) :=
  ⟨paperFourVariable_no_terminating_clock, paperStabilizedClock_slice,
    paperStabilizedClock_locallyNilpotent⟩

end GaloisForLFunctions.HTGeometry
