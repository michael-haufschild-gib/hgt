import GaloisForLFunctions.HTGeometry.FiniteNomeSectionRestriction
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaSchemeChange

/-!
# The finite-section genus gauge

A finite section of the canonical product at genus `g` differs from the same section at genus zero
by the exponential of an explicit polynomial in the coordinate whose coefficients are the finite
Euler products of the nome set.  Every finite section is a restricted infinite product, so this is
the scheme-change law for that restriction, with all its summability hypotheses automatic.

The gauge is a polynomial of degree `g` with no constant term, so it is entire and nowhere zero;
raising the genus therefore changes no finite section's divisor.
-/

namespace HTGeometry

open scoped BigOperators

/-- The genus gauge of a finite nome set: the polynomial whose exponential relates the genus-`g`
finite section to the genus-zero one. -/
noncomputable def finiteSectionGauge {ι : Type*} (g : ℕ) (p : ι → ℂ) (S : Finset ι) (t : ℂ) : ℂ :=
  ∑ k ∈ Finset.range g, t ^ (k + 1) / ((k + 1 : ℕ) : ℂ) * ∏ a ∈ S, (1 - p a ^ (k + 1))⁻¹

/-- **The exact finite-section scheme gauge.**  At every genus the finite section is the genus-zero
section multiplied by the exponential of an explicit polynomial gauge whose coefficients are the
finite Euler products of the nome set. -/
theorem finiteNomeSection_eq_zero_genus_mul_gauge {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) (t : ℂ) :
    finiteNomeSection g p S t
      = finiteNomeSection 0 p S t * Complex.exp (finiteSectionGauge g p S t) := by
  classical
  have hres_ne : ∀ a : S, (p a : ℂ) ≠ 0 := fun a => hp_ne a
  have hres_lt : ∀ a : S, ‖(p a : ℂ)‖ < 1 := fun a => hp_lt a
  rw [finiteNomeSection_eq_restricted, finiteNomeSection_eq_restricted,
    infiniteMultipleEllipticGamma_scheme_change (Nat.zero_le g) (fun a : S => p a)
      hres_ne hres_lt Summable.of_finite t,
    infiniteGenusCounterterm_eq_moment_sum (fun a : S => p a) hres_lt Summable.of_finite t]
  congr 2
  rw [finiteSectionGauge, Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  congr 1
  rw [tsum_nomeMonomial_pow (fun a : S => p a) hres_lt (k := k + 1) (by omega)
      Summable.of_finite,
    tprod_fintype]
  exact (Finset.prod_subtype S (fun _ => Iff.rfl) (fun a => (1 - p a ^ (k + 1))⁻¹)).symm

/-- The gauge is nowhere zero, so raising the genus preserves the divisor of every finite
section. -/
theorem finiteNomeSection_eq_zero_iff_genus_zero {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) (t : ℂ) :
    finiteNomeSection g p S t = 0 ↔ finiteNomeSection 0 p S t = 0 := by
  rw [finiteNomeSection_eq_zero_genus_mul_gauge g p hp_ne hp_lt S t]
  simp

/-- The gauge vanishes at the origin and is a polynomial in the coordinate, hence entire. -/
@[simp] theorem finiteSectionGauge_zero {ι : Type*} (g : ℕ) (p : ι → ℂ) (S : Finset ι) :
    finiteSectionGauge g p S 0 = 0 := by
  rw [finiteSectionGauge]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp

end HTGeometry
