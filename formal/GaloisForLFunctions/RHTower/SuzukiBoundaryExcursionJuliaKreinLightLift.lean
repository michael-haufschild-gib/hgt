import GaloisForLFunctions.RHTower.SuzukiBoundaryExcursionJuliaKreinHermitianNoGo

/-!
# Source-light Julia--Krein lift for the four-label Suzuki excursion

The direct finite pullback from the reflected Suzuki boundary form to the
P-G105F Julia block is impossible: its source form is negative definite,
whereas P has a positive child direction.  The literal source already carries
the minimal missing positive direction: its ordered four-label Plücker minor
is exactly one.  This module adjoins that one source light direction, keeps
the original two-port form as the negative sector, and gives an explicit
Hermitian lift to the actual P Julia--Krein block.

This discharges only the finite signature obstruction.  It does not identify
the source and P history actions, transport the complete SP-E prime-power
current, or supply a cofinal bound.
-/

open Complex Matrix

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The source's nonzero four-label Plücker minor supplies one positive light direction while
retaining the literal two-port boundary form as its negative sector. -/
def suzukiBoundaryExcursionFourLabelLightKreinForm : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(suzukiBoundaryExcursionFourLabelMinor : ℂ), 0, 0;
    0, (suzukiBoundaryExcursionFourLabelEntry31 : ℂ),
      (suzukiBoundaryExcursionFourLabelEntry32 : ℂ);
    0, (suzukiBoundaryExcursionFourLabelEntry41 : ℂ),
      (suzukiBoundaryExcursionFourLabelEntry42 : ℂ)]

/-- Explicit minimal light/Krein lift into the fixed P-G105F Julia block. -/
def suzukiBoundaryExcursionFourLabelLightKreinLift : Matrix (Fin 3) (Fin 2) ℂ :=
  !![(1 / 8 : ℂ), 8 * (RHTower.routeEPCubicFourthDepthJuliaDefect : ℂ);
    0, 1;
    0, (Real.sqrt 63 : ℂ)]

/-- One literal source Plücker light direction is sufficient to remove the finite Hermitian
signature obstruction to the P Julia--Krein block. -/
theorem suzukiBoundaryExcursionFourLabelLightKreinLift_pullback :
    suzukiBoundaryExcursionFourLabelLightKreinLift.conjTranspose *
        suzukiBoundaryExcursionFourLabelLightKreinForm *
      suzukiBoundaryExcursionFourLabelLightKreinLift =
        RHTower.routePPrimitiveBurnolJuliaKreinBlock := by
  have hminor : (suzukiBoundaryExcursionFourLabelMinor : ℂ) = 1 := by
    norm_cast
    exact suzukiBoundaryExcursionFourLabelMinor_eq_one
  have hdefect : (RHTower.routeEPCubicFourthDepthJuliaDefect : ℂ) ^ (2 : ℕ) = 63 / 64 := by
    calc
      (RHTower.routeEPCubicFourthDepthJuliaDefect : ℂ) ^ (2 : ℕ) =
          ((RHTower.routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) : ℝ) : ℂ) :=
        (Complex.ofReal_pow _ _).symm
      _ = ((63 / 64 : ℝ) : ℂ) := by
        have h := RHTower.routeEPCubicFourthDepthJulia_pythagoras
        norm_num [RHTower.routeEPCubicFourthDepthNormalizedContraction] at h
        congr 1
        nlinarith
      _ = 63 / 64 := Complex.ofReal_div _ _
  have hsqrt : (Real.sqrt 63 : ℂ) ^ (2 : ℕ) = 63 := by
    rw [← Complex.ofReal_pow]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiBoundaryExcursionFourLabelLightKreinLift,
      suzukiBoundaryExcursionFourLabelLightKreinForm,
      RHTower.routePPrimitiveBurnolJuliaKreinBlock, Matrix.mul_apply,
      Fin.sum_univ_succ, hminor,
      suzukiBoundaryExcursionFourLabelEntry31_eq_neg_one,
      suzukiBoundaryExcursionFourLabelEntry32_eq_zero,
      suzukiBoundaryExcursionFourLabelEntry41_eq_zero,
      suzukiBoundaryExcursionFourLabelEntry42_eq_neg_one]
  all_goals simp only [starRingEnd_apply, star_ofNat]
  · norm_num
  · field_simp
  · field_simp
  · have hrewrite :
      8 * (RHTower.routeEPCubicFourthDepthJuliaDefect : ℂ) *
          (8 * (RHTower.routeEPCubicFourthDepthJuliaDefect : ℂ)) +
          (-1 + -((Real.sqrt 63 : ℂ) * (Real.sqrt 63 : ℂ))) =
        (64 : ℂ) * (RHTower.routeEPCubicFourthDepthJuliaDefect : ℂ) ^ (2 : ℕ) -
          (Real.sqrt 63 : ℂ) ^ (2 : ℕ) - 1 := by
        ring
    rw [hrewrite, hdefect, hsqrt]
    norm_num

end GaloisForLFunctions.RHTower
