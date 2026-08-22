import GaloisForLFunctions.HTGeometry.PowerSeriesSimpleRootLift
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Deformation with a labelled root family over a residue ring

`PowerSeriesRootFamilyTransfer` lifts a split separable residue over a field.  The multivariate
induction needs the same statement one level down, where the coefficient ring is itself a power
series ring: not a field, but a ring whose nonunits are detected by a residue map.  Only the
separability argument changes — the derivative at a root is the product of the differences, and its
residue is nonzero exactly when the residues of the roots are distinct.

## Main results

* `eval_derivative_prod_X_sub_C` — the derivative of a split polynomial at one of its roots.
* `exists_powerSeriesRootFamily_of_residue` — the labelled family of lifts and its equivariance.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem eval_derivative_prod_X_sub_C {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ρ : ι → R) (i : ι) :
    Polynomial.eval (ρ i) (Polynomial.derivative (∏ j, (X - C (ρ j))))
      = ∏ j ∈ Finset.univ.erase i, (ρ i - ρ j) := by
  classical
  rw [Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ i) (fun j => X - C (ρ j))]
  rw [Polynomial.derivative_mul]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
    mul_one, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, mul_zero, zero_add, Polynomial.eval_prod]
  rw [Finset.sdiff_singleton_eq_erase]

/-- **One-variable deformation over a residue ring.**  If the residue of `G` splits with roots whose
residues are distinct, then `G` has roots congruent to them, and every coefficientwise automorphism
fixing `G` permutes the lifts exactly as it permutes the residue roots. -/
theorem exists_powerSeriesRootFamily_of_residue
    {R k : Type*} [CommRing R] [IsDomain R] [Field k] (res : R →+* k)
    (hunit : ∀ r : R, res r ≠ 0 → IsUnit r)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Polynomial (PowerSeries R)) (ρ : ι → R)
    (hinj : Function.Injective fun i => res (ρ i))
    (hres : G.map (PowerSeries.constantCoeff (R := R)) = ∏ j, (X - C (ρ j))) :
    ∃ y : ι → PowerSeries R,
      (∀ i, G.IsRoot (y i)) ∧
      (∀ i, (PowerSeries.X : PowerSeries R) ∣ (y i - PowerSeries.C (ρ i))) ∧
      ∀ (φ : R ≃+* R) (π : Equiv.Perm ι),
        G.map (PowerSeries.map (φ : R →+* R)) = G → (∀ i, φ (ρ i) = ρ (π i)) →
        ∀ i, PowerSeries.map (φ : R →+* R) (y i) = y (π i) := by
  classical
  have hconstC : ∀ i, PowerSeries.constantCoeff (R := R) (PowerSeries.C (ρ i)) = ρ i := by
    intro i
    simp
  have hv : ∀ i, (PowerSeries.X : PowerSeries R) ∣
      Polynomial.eval (PowerSeries.C (ρ i)) G := by
    intro i
    rw [PowerSeries.X_dvd_iff]
    have hmap := Polynomial.eval_map_apply (PowerSeries.constantCoeff (R := R))
      (PowerSeries.C (ρ i)) (p := G)
    rw [hconstC i] at hmap
    rw [← hmap, hres, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hdu : ∀ i, IsUnit
      (Polynomial.eval (PowerSeries.C (ρ i)) (Polynomial.derivative G)) := by
    intro i
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hmap := Polynomial.eval_map_apply (PowerSeries.constantCoeff (R := R))
      (PowerSeries.C (ρ i)) (p := Polynomial.derivative G)
    rw [hconstC i] at hmap
    rw [← hmap, ← Polynomial.derivative_map, hres, eval_derivative_prod_X_sub_C]
    refine hunit _ ?_
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    rw [map_sub]
    intro hzero
    exact (Finset.mem_erase.mp hj).1 (hinj (sub_eq_zero.mp hzero)).symm
  choose y hy using fun i =>
    (existsUnique_isRoot_powerSeries_of_isUnit_deriv (hdu i) (hv i)).exists
  refine ⟨y, fun i => (hy i).1, fun i => (hy i).2, ?_⟩
  intro φ π hG hπ i
  have hmapC : PowerSeries.map (φ : R →+* R) (PowerSeries.C (ρ i))
      = PowerSeries.C (ρ (π i)) := by
    rw [PowerSeries.map_C]
    congr 1
    exact hπ i
  refine map_lift_eq φ hG (y₀ := PowerSeries.C (ρ i)) ?_ ?_ (hy i).1 (hy i).2 (hy (π i)).1 ?_
  · rw [hmapC]
    exact hdu (π i)
  · rw [hmapC]
    exact hv (π i)
  · rw [hmapC]
    exact (hy (π i)).2

end

end GaloisForLFunctions.HTGeometry
