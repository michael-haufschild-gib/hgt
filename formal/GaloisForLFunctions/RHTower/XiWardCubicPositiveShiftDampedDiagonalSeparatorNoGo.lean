import GaloisForLFunctions.RHTower.XiWardCubicPositiveShiftDampedDiagonalSeparator
import GaloisForLFunctions.RHTower.XiWardCubicSesquiholomorphicLandingNoGo

/-!
# Damped positive-shift separator: entire-scalarization no-go

The damped positive-shift mask is a genuine diagonal separator on every finite divisor packet,
but it cannot be the restriction of an entire two-variable source weight.  Its pullback to the
reflection graph is real-valued and nonconstant, so holomorphic Schwarz rigidity forces a
contradiction.  Thus the remaining source realization must use a real Stokes/Wirtinger term or
the fixed crossing poles of the rational Cauchy-pair kernel; more entire-kernel optimization cannot
close the source-covariance gap.
-/

open Complex

namespace RHTower

noncomputable section

/-- The normalized damped mask is already strictly positive at unit depth-to-shift ratio. -/
theorem xiWardCubicPositiveShiftDiagonalMask_one_pos :
    0 < xiWardCubicPositiveShiftDiagonalMask 1 := by
  norm_num [xiWardCubicPositiveShiftDiagonalMask,
    xiWardCubicPositiveShiftDiagonalSeparatorProfile,
    xiWardCubicPositiveShiftDiagonalAnomalyProfile]

/-- No jointly entire source weight restricts to the damped diagonal mask at any positive source
shift.  The obstruction is scalarization, not small-shift convergence or divisor collisions. -/
theorem not_exists_entire_xiWardCubicPositiveShiftDiagonalMaskLanding
    {eps : ℝ} (heps : 0 < eps) :
    ¬ ∃ F : ℂ × ℂ → ℂ,
      Differentiable ℂ F ∧
      ∀ z : ℂ,
        F (1 - z, z) =
          (xiWardCubicPositiveShiftDiagonalMask (z.re / eps) : ℂ) := by
  rintro ⟨F, hF, hland⟩
  let g : ℂ → ℂ := fun z => F (1 - z, z)
  have hg : Differentiable ℂ g := by
    dsimp only [g]
    fun_prop
  have hstarEq : (fun z : ℂ => star (g z)) = g := by
    funext z
    change star (F (1 - z, z)) = F (1 - z, z)
    rw [hland]
    exact Complex.conj_ofReal _
  have hgstar : Differentiable ℂ (fun z : ℂ => star (g z)) := by
    rw [hstarEq]
    exact hg
  have hconst :=
    GaloisForLFunctions.HTGeometry.eq_of_differentiable_pointwiseStar
      hg hgstar (eps : ℂ)
  dsimp only [g] at hconst
  rw [hland, hland, Complex.ofReal_inj] at hconst
  norm_num [heps.ne'] at hconst
  rw [xiWardCubicPositiveShiftDiagonalMask_zero] at hconst
  linarith [xiWardCubicPositiveShiftDiagonalMask_one_pos]

end

end RHTower
