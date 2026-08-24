import GaloisForLFunctions.RHTower.ContinuousH2CyclotomicHasse
import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality
import GaloisForLFunctions.HTGeometry.ABHN.ZModTwoReciprocitySupportParity

/-!
# Support rigidity for Deninger cyclotomic reciprocity

Finite local `H²` invariants become literal roots of unity in a Deninger cyclotomic stage.
Product-one reciprocity forces every nonzero packet to occupy at least two coordinates and every
active coordinate to have a distinct partner. At order two, product-one is exactly even support.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

/-- A nonzero product-one Deninger cyclotomic packet occupies at least two coordinates. -/
theorem deningerCyclotomicProfileProduct_two_le_support_card_of_ne_zero
    (ι : Type u) [DecidableEq ι] (n : ℕ) [NeZero n]
    (x : ι →₀ ratModIntNTorsion n)
    (hprod : deningerCyclotomicProfileProduct n
      (ratModIntNTorsionCyclotomicProfileAddEquiv ι n x) = 1)
    (hne : x ≠ 0) :
    2 ≤ x.support.card := by
  apply finsupp_two_le_support_card_of_sum_eq_zero x
  · exact (deningerCyclotomicProfileProduct_eq_one_hasse_iff ι n x).mp hprod
  · exact hne

/-- A nonzero product-one Deninger cyclotomic packet has two distinct nonzero coordinates. -/
theorem deningerCyclotomicProfileProduct_exists_two_nonzero_places_of_ne_zero
    (ι : Type u) [DecidableEq ι] (n : ℕ) [NeZero n]
    (x : ι →₀ ratModIntNTorsion n)
    (hprod : deningerCyclotomicProfileProduct n
      (ratModIntNTorsionCyclotomicProfileAddEquiv ι n x) = 1)
    (hne : x ≠ 0) :
    ∃ i j, i ≠ j ∧ x i ≠ 0 ∧ x j ≠ 0 := by
  apply finsupp_exists_two_nonzero_places_of_sum_eq_zero x
  · exact (deningerCyclotomicProfileProduct_eq_one_hasse_iff ι n x).mp hprod
  · exact hne

/-- Every active coordinate of a product-one Deninger cyclotomic packet has a distinct active
partner. -/
theorem deningerCyclotomicProfileProduct_nonzero_place_has_partner
    (ι : Type u) [DecidableEq ι] (n : ℕ) [NeZero n]
    (x : ι →₀ ratModIntNTorsion n)
    (hprod : deningerCyclotomicProfileProduct n
      (ratModIntNTorsionCyclotomicProfileAddEquiv ι n x) = 1)
    (i : ι) (hi : x i ≠ 0) :
    ∃ j, j ≠ i ∧ x j ≠ 0 := by
  apply finsupp_exists_other_nonzero_place_of_sum_eq_zero x
  · exact (deningerCyclotomicProfileProduct_eq_one_hasse_iff ι n x).mp hprod
  · exact hi

/-- At the quadratic cyclotomic stage, product-one reciprocity is exactly even support. -/
theorem deningerCyclotomicProfileProduct_two_eq_one_iff_even_support_card
    (ι : Type u) [DecidableEq ι] (x : ι →₀ ratModIntNTorsion 2) :
    deningerCyclotomicProfileProduct 2
      (ratModIntNTorsionCyclotomicProfileAddEquiv ι 2 x) = 1 ↔
      Even x.support.card := by
  let d := (zmodRatModIntAddEquivNTorsion 2 (by decide)).symm
  rw [deningerCyclotomicProfileProduct_eq_one_hasse_iff]
  rw [← finsuppAddEquivZModTwo_sum_eq_zero_iff_even_support_card d x]
  change x.sum (fun _ q => q) = 0 ↔ x.sum (fun _ q => d q) = 0
  constructor
  · intro h
    have hmap := congrArg d h
    rw [map_zero, map_finsuppSum] at hmap
    exact hmap
  · intro h
    apply d.injective
    rw [map_zero, map_finsuppSum]
    exact h

end

end RHTower
