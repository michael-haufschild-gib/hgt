import GaloisForLFunctions.RHTower.FieldOnePadicProductHaarQuadrature

/-!
# Exact finite-quotient Haar quadrature on products of p-adic integers

The product probability Haar measure on `∏ᵢ ℤ_{pᵢ}` descends exactly to the
literal quotient `∏ᵢ ZMod (pᵢ ^ nᵢ)`.  This file constructs the quotient and
its canonical representatives and proves exact quadrature for every
simultaneously periodic integrable function.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

/-- Coordinatewise reduction modulo `pᵢ ^ nᵢ`. -/
def fieldOnePadicIntProductToFiniteQuotient (n : ι → ℕ) :
    FieldOnePadicIntProduct p →+
      FieldOneFiniteCyclicProduct (fun i => p i ^ n i) where
  toFun u i := PadicInt.toZModPow (n i) (u i)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

omit [Fintype ι] [DecidableEq ι] in
theorem fieldOnePadicIntProductToFiniteQuotient_surjective (n : ι → ℕ) :
    Function.Surjective (fieldOnePadicIntProductToFiniteQuotient p n) := by
  intro r
  refine ⟨fun i => fieldOnePadicIntResidueRep (p i) (n i) (r i), ?_⟩
  funext i
  exact fieldOnePadicIntResidueRep_spec (p i) (n i) (r i)

/-- Coordinatewise least-nonnegative residue representatives. -/
def fieldOnePadicIntProductResidueRep (n : ι → ℕ) :
    FieldOneFiniteCyclicProduct (fun i => p i ^ n i) →
      FieldOnePadicIntProduct p :=
  fun r i => fieldOnePadicIntResidueRep (p i) (n i) (r i)

omit [Fintype ι] [DecidableEq ι] in
theorem fieldOnePadicIntProductResidueRep_spec (n : ι → ℕ)
    (r : FieldOneFiniteCyclicProduct (fun i => p i ^ n i)) :
    fieldOnePadicIntProductToFiniteQuotient p n
        (fieldOnePadicIntProductResidueRep p n r) = r := by
  funext i
  exact fieldOnePadicIntResidueRep_spec (p i) (n i) (r i)

/-- A point of the product lattice `∏ᵢ pᵢ ^ nᵢ ℤ_{pᵢ}`. -/
def fieldOnePadicIntProductLatticePoint (n : ι → ℕ)
    (z : FieldOnePadicIntProduct p) : FieldOnePadicIntProduct p :=
  fun i => (p i : ℤ_[p i]) ^ n i * z i

omit [Fintype ι] [DecidableEq ι] in
/-- Invariance under the product lattice implies constancy on every fiber of
coordinatewise residue reduction. -/
theorem fieldOnePadicIntProduct_classInvariant_of_primePowerInvariant
    (n : ι → ℕ) (f : FieldOnePadicIntProduct p → ℂ)
    (hperiod : ∀ x z : FieldOnePadicIntProduct p,
      f (x + fieldOnePadicIntProductLatticePoint p n z) = f x) :
    ∀ {x y : FieldOnePadicIntProduct p},
      fieldOnePadicIntProductToFiniteQuotient p n x =
          fieldOnePadicIntProductToFiniteQuotient p n y →
        f x = f y := by
  intro x y hxy
  have hcoord : ∀ i,
      x i - y i ∈ RingHom.ker (PadicInt.toZModPow (p := p i) (n i)) := by
    intro i
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact congrFun hxy i
  have hspan : ∀ i, x i - y i ∈
      Ideal.span ({(p i : ℤ_[p i]) ^ n i} : Set ℤ_[p i]) := by
    intro i
    rw [← PadicInt.ker_toZModPow]
    exact hcoord i
  choose z hz using fun i => Ideal.mem_span_singleton.mp (hspan i)
  calc
    f x = f (y + fieldOnePadicIntProductLatticePoint p n z) := by
      congr 1
      funext i
      change x i = y i + (p i : ℤ_[p i]) ^ n i * z i
      rw [← hz i]
      abel
    _ = f y := hperiod y z

/-- Exact product residue-class quadrature.  There are precisely
`∏ᵢ pᵢ ^ nᵢ` classes. -/
theorem fieldOnePadicIntProduct_sampleSum_eq_nsmul_integral
    (n : ι → ℕ) (f : FieldOnePadicIntProduct p → ℂ)
    (hf : Integrable f (fieldOnePadicIntProductNormalizedHaar p))
    (hperiod : ∀ x z : FieldOnePadicIntProduct p,
      f (x + fieldOnePadicIntProductLatticePoint p n z) = f x) :
    ∑ r : FieldOneFiniteCyclicProduct (fun i => p i ^ n i),
        f (fieldOnePadicIntProductResidueRep p n r) =
      (∏ i, p i ^ n i) •
        (∫ x, f x ∂fieldOnePadicIntProductNormalizedHaar p) := by
  have h := fieldOneFiniteQuotient_sampleSum_eq_nsmul_integral
    (fieldOnePadicIntProductNormalizedHaar p)
    (fieldOnePadicIntProductNormalizedHaar_univ p)
    (fieldOnePadicIntProductToFiniteQuotient p n)
    (fieldOnePadicIntProductToFiniteQuotient_surjective p n)
    (fieldOnePadicIntProductResidueRep p n)
    (fieldOnePadicIntProductResidueRep_spec p n) f hf
    (fieldOnePadicIntProduct_classInvariant_of_primePowerInvariant
      p n f hperiod)
  simpa [FieldOneFiniteCyclicProduct] using h

end

end GaloisForLFunctions.RHTower
