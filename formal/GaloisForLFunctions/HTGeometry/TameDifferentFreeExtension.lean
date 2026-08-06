import GaloisForLFunctions.HTGeometry.TameDifferentMonogenic
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# The monic relation from the characteristic polynomial

An element of a finite free algebra satisfies the characteristic polynomial of multiplication by
it, which is monic of degree the rank.  For a finite free extension of discrete valuation rings
whose rank is the ramification index, a uniformizer therefore satisfies a monic relation of exactly
that degree, and the tame computation applies with no monogenicity hypothesis: the presentation is
produced rather than assumed.

The resulting valuation is that of the derivative of the characteristic polynomial.  It is the
different exponent precisely when the presented element generates the extension; without that the
statement remains a computation of the characteristic polynomial's derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDiscreteValuationRing

variable {A B : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

omit [IsDomain B] [IsDiscreteValuationRing B] in
/-- **A finite free extension supplies a monic relation of degree the rank.** -/
theorem exists_monic_relation_of_free [Module.Free A B] [Module.Finite A B] (e : ℕ)
    (hrank : Module.finrank A B = e) (x : B) :
    ∃ g : A[X], g.Monic ∧ g.natDegree = e ∧ eval x (g.map (algebraMap A B)) = 0 := by
  refine ⟨LinearMap.charpoly (Algebra.lmul A B x), LinearMap.charpoly_monic _, ?_, ?_⟩
  · rw [LinearMap.charpoly_natDegree, hrank]
  · rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact Algebra.aeval_self_charpoly_lmul x

/-- **The tame computation for a finite free extension of discrete valuation rings.**  If the rank
equals the ramification index and that index is a unit at the place, then a uniformizer satisfies a
monic relation of that degree whose derivative there has valuation exactly one less. -/
theorem exists_monic_relation_addVal_eval_derivative [Module.Free A B] [Module.Finite A B]
    {πA : A} (hπA : Irreducible πA) (e : ℕ) (he : 0 < e)
    (hram : addVal B (algebraMap A B πA) = (e : ℕ∞)) (hrank : Module.finrank A B = e)
    {x : B} (hx : addVal B x = 1) (htame : addVal B ((e : ℕ) : B) = 0) :
    ∃ g : A[X], g.Monic ∧ g.natDegree = e ∧ eval x (g.map (algebraMap A B)) = 0 ∧
      addVal B (eval x (derivative (g.map (algebraMap A B)))) = ((e - 1 : ℕ) : ℕ∞) := by
  obtain ⟨g, hmonic, hdeg, hroot⟩ := exists_monic_relation_of_free e hrank x
  exact ⟨g, hmonic, hdeg, hroot,
    addVal_eval_derivative_of_monic_uniformizer_root (algebraMap A B) hπA e he hram hx hmonic hdeg
      hroot htame⟩

/-- **The relation supplied by a finite free extension is Eisenstein at a uniformizer.** -/
theorem exists_eisenstein_relation_of_free [Module.Free A B] [Module.Finite A B]
    {πA : A} (hπA : Irreducible πA) (e : ℕ) (he : 0 < e)
    (hram : addVal B (algebraMap A B πA) = (e : ℕ∞)) (hrank : Module.finrank A B = e)
    {x : B} (hx : addVal B x = 1) :
    ∃ g : A[X], g.Monic ∧ g.natDegree = e ∧ eval x (g.map (algebraMap A B)) = 0 ∧
      (∀ i < e, addVal A (g.coeff i) ≠ 0) ∧ addVal A (g.coeff 0) = 1 := by
  obtain ⟨g, hmonic, hdeg, hroot⟩ := exists_monic_relation_of_free e hrank x
  obtain ⟨hcoef, hc0⟩ :=
    eisenstein_of_monic_uniformizer_root (algebraMap A B) hπA e he hram hx hmonic hdeg hroot
  exact ⟨g, hmonic, hdeg, hroot, hcoef, hc0⟩

end GaloisForLFunctions.HTGeometry
