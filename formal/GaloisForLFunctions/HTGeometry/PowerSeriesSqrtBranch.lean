import GaloisForLFunctions.HTGeometry.PowerSeriesSimpleRootLift

/-!
# A power series square root with a prescribed branch

A power series whose constant term is a nonzero square has a square root, and Hensel's lemma pins
it down by its constant term.  Choosing that constant term is exactly the branch choice a labelled
root family needs: the two roots of a block quadratic are distinguished by which unperturbed level
they degenerate to.

## Main results

* `exists_powerSeries_sqrt_branch` — the square root with prescribed constant term.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **A power series with a nonzero square constant term has a square root with that square root as
its constant term.** -/
theorem exists_powerSeries_sqrt_branch {A : Type*} [Field A] (h2 : (2 : A) ≠ 0)
    (f : PowerSeries A) (δ : A) (hδ : δ ≠ 0)
    (h0 : PowerSeries.constantCoeff (R := A) f = δ * δ) :
    ∃ ρ : PowerSeries A, ρ * ρ = f ∧ PowerSeries.constantCoeff (R := A) ρ = δ := by
  classical
  set G : Polynomial (PowerSeries A) := Polynomial.X ^ 2 - Polynomial.C f with hG
  set y₀ : PowerSeries A := PowerSeries.C δ with hy₀
  have hderiv : Polynomial.derivative G = 2 * Polynomial.X := by
    rw [hG]
    simp [Polynomial.derivative_sub]
    ring
  have hdu : IsUnit ((Polynomial.derivative G).eval y₀) := by
    rw [hderiv]
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have : Polynomial.eval y₀ (2 * Polynomial.X) = 2 * y₀ := by
      simp
    rw [this, map_mul, hy₀]
    simp only [PowerSeries.constantCoeff_C, map_ofNat]
    exact (mul_ne_zero h2 hδ).isUnit
  have hv : (PowerSeries.X : PowerSeries A) ∣ Polynomial.eval y₀ G := by
    rw [PowerSeries.X_dvd_iff, hG]
    have : Polynomial.eval y₀ (Polynomial.X ^ 2 - Polynomial.C f) = y₀ ^ 2 - f := by
      simp
    rw [this, map_sub, h0, hy₀]
    simp [sq, PowerSeries.constantCoeff_C]
  obtain ⟨ρ, hroot, hcong⟩ := exists_isRoot_powerSeries_of_isUnit_deriv hdu hv
  have hsq : ρ ^ 2 - f = 0 := by
    have : Polynomial.eval ρ G = 0 := hroot
    rw [hG] at this
    simpa using this
  refine ⟨ρ, by linear_combination hsq, ?_⟩
  have := (PowerSeries.X_dvd_iff (R := A)).mp hcong
  rw [map_sub, hy₀] at this
  simp only [PowerSeries.constantCoeff_C] at this
  exact sub_eq_zero.mp this

end GaloisForLFunctions.HTGeometry
