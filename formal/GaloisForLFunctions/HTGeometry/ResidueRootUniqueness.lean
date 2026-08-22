import GaloisForLFunctions.HTGeometry.HenselDefectRoot
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# A simple root is determined by its residue

In a ring whose nonunits are exactly the elements with vanishing residue, two roots of a polynomial
with the same residue coincide as soon as the derivative at one of them has nonvanishing residue.
No completeness is needed: the second-order Taylor expansion factors the difference of the two
values, and the cofactor has the same residue as the derivative, hence is a unit.

This is the uniqueness half of Hensel's lemma stripped of its existence half, and it is what makes
a labelled root family independent of the order in which the deformation variables were introduced:
whichever route produces it, a root with a given residue is the same element.

## Main results

* `isRoot_unique_of_residue` — the abstract statement.
* `isRoot_unique_mvPowerSeries` — its instance for multivariate power series over a field.
-/

namespace GaloisForLFunctions.HTGeometry

theorem isRoot_unique_of_residue {S k : Type*} [CommRing S] [Field k] (res : S →+* k)
    (hunit : ∀ s : S, res s ≠ 0 → IsUnit s)
    {F : Polynomial S} {y y' : S}
    (hy : F.IsRoot y) (hy' : F.IsRoot y')
    (hd : res ((Polynomial.derivative F).eval y) ≠ 0)
    (hres : res y = res y') : y = y' := by
  obtain ⟨B, hB⟩ := exists_eval_add_eq F y (y' - y)
  have hy2 : y + (y' - y) = y' := by ring
  rw [hy2] at hB
  have hy0 : Polynomial.eval y F = 0 := hy
  have hy'0 : Polynomial.eval y' F = 0 := hy'
  rw [hy0, hy'0] at hB
  have hfac : (y' - y) * ((Polynomial.derivative F).eval y + (y' - y) * B) = 0 := by
    linear_combination -hB
  have hresh : res (y' - y) = 0 := by
    rw [map_sub, hres, sub_self]
  have hunitfac : IsUnit ((Polynomial.derivative F).eval y + (y' - y) * B) := by
    refine hunit _ ?_
    rw [map_add, map_mul, hresh, zero_mul, add_zero]
    exact hd
  obtain ⟨u, hu⟩ := hunitfac
  have hzero : y' - y = 0 := by
    have h := congrArg (fun s => s * (↑u⁻¹ : S)) hfac
    simp only [zero_mul] at h
    rw [mul_assoc, ← hu] at h
    simpa using h
  exact (sub_eq_zero.mp hzero).symm

/-- **A simple root of a multivariate power series polynomial is determined by its constant
coefficient.** -/
theorem isRoot_unique_mvPowerSeries {σ R : Type*} [Field R]
    {F : Polynomial (MvPowerSeries σ R)} {y y' : MvPowerSeries σ R}
    (hy : F.IsRoot y) (hy' : F.IsRoot y')
    (hd : MvPowerSeries.constantCoeff ((Polynomial.derivative F).eval y) ≠ 0)
    (hres : MvPowerSeries.constantCoeff y = MvPowerSeries.constantCoeff y') : y = y' := by
  refine isRoot_unique_of_residue (MvPowerSeries.constantCoeff (σ := σ) (R := R)) ?_ hy hy' hd hres
  intro s hs
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  exact hs.isUnit

end GaloisForLFunctions.HTGeometry
