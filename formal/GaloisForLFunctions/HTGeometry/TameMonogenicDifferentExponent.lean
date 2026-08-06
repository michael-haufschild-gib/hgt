import GaloisForLFunctions.HTGeometry.TameMonicDifferentExponent
import GaloisForLFunctions.HTGeometry.LocalRamificationOrderLaw

/-!
# The tame different exponent of a monogenic totally ramified extension

A coefficient in the maximal ideal downstairs has valuation at least the ramification index
upstairs, because the ramification index multiplies valuations.  Eisenstein coefficients therefore
satisfy exactly the bound the exact computation of the different exponent requires.

Consequently, for an extension of discrete valuation rings presented by an Eisenstein polynomial of
degree equal to the ramification index, the derivative of that polynomial at a uniformizer has
valuation exactly one less than the index, provided the index is a unit at the place.  Only the
existence of such a presentation -- monogenicity -- is assumed; nothing about the shape of the
polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDiscreteValuationRing

variable {A B : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- **A coefficient in the maximal ideal has valuation at least the ramification index.** -/
theorem le_addVal_map_of_addVal_ne_zero (ψ : A →+* B) {πA : A} (hπA : Irreducible πA) (e : ℕ)
    (hram : addVal B (ψ πA) = (e : ℕ∞)) {c : A} (hc : c ≠ 0) (hcm : addVal A c ≠ 0) :
    (e : ℕ∞) ≤ addVal B (ψ c) := by
  rw [addVal_map_eq_mul_ramification ψ hπA e hram c hc]
  calc (e : ℕ∞) = (e : ℕ∞) * 1 := (mul_one _).symm
    _ ≤ (e : ℕ∞) * addVal A c := by
        gcongr
        exact Order.one_le_iff_ne_zero.mpr hcm

/-- **The tame different exponent of a monogenic totally ramified extension.**  If the extension is
presented by an Eisenstein polynomial whose degree is the ramification index, and that index is a
unit at the place, then the derivative at a uniformizer has valuation exactly one less. -/
theorem addVal_eval_derivative_map_eisenstein (ψ : A →+* B) {πA : A} (hπA : Irreducible πA)
    (e : ℕ) (he : 0 < e) (hram : addVal B (ψ πA) = (e : ℕ∞))
    {g : A[X]} (hmonic : g.Monic) (hdeg : g.natDegree = e)
    (hcoef : ∀ i < e, g.coeff i ≠ 0 → addVal A (g.coeff i) ≠ 0)
    (x : B) (hx : Irreducible x) (htame : addVal B ((e : ℕ) : B) = 0) :
    addVal B (eval x (derivative (g.map ψ))) = ((e - 1 : ℕ) : ℕ∞) := by
  have hmonic' : (g.map ψ).Monic := hmonic.map ψ
  have hdeg' : (g.map ψ).natDegree = e := by rw [hmonic.natDegree_map, hdeg]
  have hcoef' : ∀ i ∈ Finset.range (g.map ψ).natDegree,
      (((g.map ψ).natDegree : ℕ) : ℕ∞) ≤ addVal B ((g.map ψ).coeff i) := by
    intro i hi
    rw [hdeg'] at hi ⊢
    rw [Polynomial.coeff_map]
    by_cases hzero : g.coeff i = 0
    · rw [hzero, map_zero, AddValuation.map_zero]
      exact le_top
    · exact le_addVal_map_of_addVal_ne_zero ψ hπA e hram hzero
        (hcoef i (Finset.mem_range.mp hi) hzero)
  have hmain := addVal_eval_derivative_monic hmonic' (by rw [hdeg']; exact he) hcoef' x hx
    (by rw [hdeg']; exact htame)
  rwa [hdeg'] at hmain

end GaloisForLFunctions.HTGeometry
