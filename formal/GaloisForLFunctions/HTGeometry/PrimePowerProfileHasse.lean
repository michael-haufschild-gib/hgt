import GaloisForLFunctions.HTGeometry.PrimeRadialFusionNaturality

/-!
# Prime-power profile Hasse classification

Arithmetic functions supported on positive prime powers are classified by their complete local
coordinates indexed by a prime and a positive valuation depth.  Every arbitrary coordinate profile
has a unique supported global realization, and one prime-power coordinate detects any pair of
distinct supported sources.

This is a literal existence-and-uniqueness Hasse principle for Euler-source data.  The support
restriction is intrinsic to the classified carrier rather than an added theorem hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- Arithmetic functions supported on positive prime powers. -/
abbrev PositivePrimePowerArithmeticFunction :=
  {A : ArithmeticFunction ℂ // PrimeProfileSupportedOnPositivePrimePowers A}

/-- Complete prime-power coordinate profiles classify supported arithmetic functions. -/
noncomputable def primePowerProfileEquivSupported :
    (PrimePowerClockIndex → ℂ) ≃ PositivePrimePowerArithmeticFunction where
  toFun u := ⟨arithmeticFunctionOfPrimePowerProfile u,
    arithmeticFunctionOfPrimePowerProfile_supportedOnPositivePrimePowers u⟩
  invFun A := primePowerCoordinateProfile A.1
  left_inv u := by
    funext x
    exact primePowerCoordinateProfile_arithmeticFunctionOfPrimePowerProfile u x
  right_inv A := by
    apply Subtype.ext
    exact positivePrimePowerProjection_eq_self A.1 A.2

@[simp] theorem primePowerProfileEquivSupported_apply
    (u : PrimePowerClockIndex → ℂ) :
    (primePowerProfileEquivSupported u : ArithmeticFunction ℂ) =
      arithmeticFunctionOfPrimePowerProfile u := rfl

/-- Prime-power Hasse congruence for supported arithmetic functions. -/
theorem positivePrimePowerArithmeticFunction_congr_hasse_iff
    (A B : PositivePrimePowerArithmeticFunction) :
    A = B ↔ ∀ x, primePowerCoordinateProfile A.1 x = primePowerCoordinateProfile B.1 x := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    apply primePowerProfileEquivSupported.symm.injective
    funext x
    exact h x

/-- Every complete prime-power local profile has one unique supported global arithmetic source. -/
theorem primePowerProfile_existsUnique_supported_global
    (u : PrimePowerClockIndex → ℂ) :
    ∃! A : PositivePrimePowerArithmeticFunction,
      ∀ x, primePowerCoordinateProfile A.1 x = u x := by
  refine ⟨primePowerProfileEquivSupported u, ?_, ?_⟩
  · intro x
    exact primePowerCoordinateProfile_arithmeticFunctionOfPrimePowerProfile u x
  · intro A hA
    apply (positivePrimePowerArithmeticFunction_congr_hasse_iff A
      (primePowerProfileEquivSupported u)).2
    intro x
    rw [primePowerProfileEquivSupported_apply,
      primePowerCoordinateProfile_arithmeticFunctionOfPrimePowerProfile]
    exact hA x

/-- Distinct supported global sources differ at one prime and one valuation depth. -/
theorem exists_primePowerCoordinate_ne_of_supported_ne
    (A B : PositivePrimePowerArithmeticFunction) (hAB : A ≠ B) :
    ∃ x, primePowerCoordinateProfile A.1 x ≠ primePowerCoordinateProfile B.1 x := by
  by_contra h
  push Not at h
  exact hAB ((positivePrimePowerArithmeticFunction_congr_hasse_iff A B).2 h)

end

end GaloisForLFunctions.HTGeometry
