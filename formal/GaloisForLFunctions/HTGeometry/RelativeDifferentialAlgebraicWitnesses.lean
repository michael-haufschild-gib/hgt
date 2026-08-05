import GaloisForLFunctions.HTGeometry.RelativeDifferentialAlgebraicity

/-!
# Relative differential algebraicity is realized

Differential algebraicity over a base family is realized at order zero by the zero function: the
single coordinate variable is a nonzero relation vanishing on it.  So the relative notion is not
empty, and its negation — relative hypertranscendence — is the substantive side.
-/

namespace GaloisForLFunctions
namespace RelativeDifferentialAlgebraicity

variable {ι : Type*}

/-- **The zero function is differentially algebraic over every base, at order zero.** -/
theorem differentiallyAlgebraicOverOfOrder_zero (g : ι → ℂ → ℂ) :
    DifferentiallyAlgebraicOverOfOrder g (fun _ => 0) 0 := by
  refine ⟨MvPolynomial.X (Sum.inr 0), MvPolynomial.X_ne_zero _, fun z => ?_⟩
  simp

/-- Hence the zero function is differentially algebraic over every base. -/
theorem differentiallyAlgebraicOver_zero (g : ι → ℂ → ℂ) :
    DifferentiallyAlgebraicOver g (fun _ => 0) :=
  ⟨0, differentiallyAlgebraicOverOfOrder_zero g⟩

/-- The zero function is therefore not relatively hypertranscendental. -/
theorem not_hypertranscendentalOver_zero (g : ι → ℂ → ℂ) :
    ¬ HypertranscendentalOver g (fun _ => 0) := fun h => h (differentiallyAlgebraicOver_zero g)

end RelativeDifferentialAlgebraicity
end GaloisForLFunctions
