import Mathlib

/-!
# Coprimality of a polynomial pair from a one-dimensional solution space

A pair of polynomials cut out by a linear condition whose solution space is one-dimensional is
automatically coprime, provided the condition survives division by a common factor.  If the quotient
pair still solves the condition, it is proportional to the original, so `g` times a scalar is `1`
and `g` is a unit — the second component is not even needed for that step.

The mechanism is only that a line has no room for two independent points: no property of the linear
condition is used beyond its solution space having rank one, and no property of the factor `g`
beyond its dividing both entries.  This is the shape in which "generic corank one" upgrades a
divisibility statement to coprimality.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- **A common factor that survives division is a unit**, when the solution space is a line. -/
theorem isUnit_of_dvd_pair_of_finrank_one
    (S : Submodule K (Polynomial K × Polynomial K)) (hS : Module.finrank K S = 1)
    {U W g U' W' : Polynomial K} (hU : U ≠ 0)
    (hmem : (U, W) ∈ S) (hmem' : (U', W') ∈ S) (hUdvd : U = g * U') :
    IsUnit g := by
  have hne : (⟨(U, W), hmem⟩ : S) ≠ 0 := by
    intro h
    apply hU
    have := congrArg (fun x : S => (x : Polynomial K × Polynomial K).1) h
    simpa using this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hS ⟨(U', W'), hmem'⟩
  have hfst : c • U = U' := by
    have := congrArg (fun x : S => (x : Polynomial K × Polynomial K).1) hc
    simpa using this
  have hCc : Polynomial.C c * U = U' := by
    rw [← Polynomial.smul_eq_C_mul]
    exact hfst
  have hkey : U * (1 - g * Polynomial.C c) = 0 := by
    have hUeq : U = g * (Polynomial.C c * U) := by rw [hCc]; exact hUdvd
    linear_combination hUeq
  have hunit : g * Polynomial.C c = 1 := by
    rcases mul_eq_zero.1 hkey with h | h
    · exact absurd h hU
    · linear_combination -h
  exact ⟨⟨g, Polynomial.C c, hunit, by rw [mul_comm]; exact hunit⟩, rfl⟩

/-- **Coprimality from a one-dimensional solution space.** -/
theorem isCoprime_of_finrank_one
    (S : Submodule K (Polynomial K × Polynomial K)) (hS : Module.finrank K S = 1)
    {U W : Polynomial K} (hU : U ≠ 0) (hmem : (U, W) ∈ S)
    (hdiv : ∀ g U' W' : Polynomial K, U = g * U' → W = g * W' → (U', W') ∈ S) :
    IsCoprime U W := by
  classical
  have hgcd : IsUnit (EuclideanDomain.gcd U W) := by
    obtain ⟨U', hU'⟩ := EuclideanDomain.gcd_dvd_left U W
    obtain ⟨W', hW'⟩ := EuclideanDomain.gcd_dvd_right U W
    exact isUnit_of_dvd_pair_of_finrank_one S hS hU hmem
      (hdiv _ _ _ hU' hW') hU'
  exact EuclideanDomain.gcd_isUnit_iff.1 hgcd

end GaloisForLFunctions.HTGeometry

end
