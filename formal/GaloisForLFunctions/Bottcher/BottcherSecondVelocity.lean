import GaloisForLFunctions.Bottcher.BottcherVelocityMahler
import GaloisForLFunctions.HTGeometry.MahlerInhomogeneousSolve

/-!
# The second Böttcher parameter velocity as a formal series

The second logarithmic parameter jet of the Böttcher constraint satisfies the triangular
Mahler equation `B(X²) = 2·B + (2X³·A′ − X⁴)`, whose inhomogeneity is built from the first
jet.  By unique solvability of inhomogeneous Mahler equations this pins a canonical formal
series (`bottcherSecondVelocitySeries`, with defining equation
`bottcherSecondVelocitySeries_spec` and uniqueness `bottcherSecondVelocity_unique`), and the
equation rearranges into the exposure identity
`2X³·A′ = B(X²) − 2B + X⁴` (`bottcherSecondVelocity_exposes_deriv`): the spatial derivative
of the first jet is an exact linear expression in the second jet and its dyadic transform —
the triangular mechanism behind the algebraic independence of the two parameter velocities.
-/

open PowerSeries

namespace GaloisForLFunctions

/-- The inhomogeneity of the second-velocity equation: `2X³·A′ − X⁴`. -/
noncomputable def bottcherSecondVelocityRHS : ℂ⟦X⟧ :=
  PowerSeries.C (2 : ℂ) * PowerSeries.X ^ (3 : ℕ) * d⁄dX ℂ bottcherVelocitySeries
    - PowerSeries.X ^ (4 : ℕ)

/-- The second Böttcher parameter-velocity series: the unique formal solution of
`B(X²) = 2·B + (2X³·A′ − X⁴)`. -/
noncomputable def bottcherSecondVelocitySeries : ℂ⟦X⟧ :=
  (mahler_inhomogeneous_solvable (le_refl 2) (two_ne_zero) (by norm_num)
    bottcherSecondVelocityRHS).exists.choose

/-- Defining equation of the second velocity. -/
theorem bottcherSecondVelocitySeries_spec :
    subst (PowerSeries.X ^ (2 : ℕ)) bottcherSecondVelocitySeries
      = PowerSeries.C (2 : ℂ) * bottcherSecondVelocitySeries + bottcherSecondVelocityRHS :=
  (mahler_inhomogeneous_solvable (le_refl 2) (two_ne_zero) (by norm_num)
    bottcherSecondVelocityRHS).exists.choose_spec

/-- Uniqueness: any formal solution of the second-velocity equation is the canonical one. -/
theorem bottcherSecondVelocity_unique {Y : ℂ⟦X⟧}
    (h : subst (PowerSeries.X ^ (2 : ℕ)) Y
      = PowerSeries.C (2 : ℂ) * Y + bottcherSecondVelocityRHS) :
    Y = bottcherSecondVelocitySeries :=
  (mahler_inhomogeneous_solvable (le_refl 2) (two_ne_zero) (by norm_num)
    bottcherSecondVelocityRHS).unique h bottcherSecondVelocitySeries_spec

/-- **Exposure identity**: the spatial derivative of the first jet is recovered exactly from
the second jet and its dyadic transform, `2X³·A′ = B(X²) − 2B + X⁴`. -/
theorem bottcherSecondVelocity_exposes_deriv :
    PowerSeries.C (2 : ℂ) * PowerSeries.X ^ (3 : ℕ) * d⁄dX ℂ bottcherVelocitySeries
      = subst (PowerSeries.X ^ (2 : ℕ)) bottcherSecondVelocitySeries
        - PowerSeries.C (2 : ℂ) * bottcherSecondVelocitySeries + PowerSeries.X ^ (4 : ℕ) := by
  have h := bottcherSecondVelocitySeries_spec
  rw [bottcherSecondVelocityRHS] at h
  linear_combination -h

end GaloisForLFunctions
