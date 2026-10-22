import GaloisForLFunctions.RHTower.Deninger.DeningerFlasqueAcyclic
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeResidueSheaf

/-!
# The direct sum of skyscrapers is acyclic

Restriction on the direct sum of skyscrapers along a finite set of primes is precomposition with an
inclusion of index sets, so it is onto: extend by zero.  The sheaf is therefore flasque, and hence
has no higher cohomology.  This is the amplitude `[0,0]` of the prime-packet residue target.

* `deningerResidueAddSheaf_isFlasque` : the residue sheaf is flasque.
* `deningerResidueAddSheaf_ext_eq_zero` : it has no higher cohomology.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

variable (P : Finset Nat.Primes) (A : Type) [AddCommGroup A]

/-- **The direct sum of skyscrapers is flasque**: restriction is precomposition with an inclusion
of index sets, and a section over a smaller open extends by zero. -/
theorem deningerResidueAddSheaf_isFlasque :
    TopCat.Sheaf.IsFlasque (deningerResidueAddSheaf P A) := by
  classical
  constructor
  intro W₁ W₂ i
  refine (AddCommGrpCat.epi_iff_surjective _).2 (fun g => ?_)
  refine ⟨(fun j : deningerLogIdx P W₁.unop =>
    if h : deningerClosedPt ((j : Nat.Primes)) ∈ W₂.unop then g ⟨(j : Nat.Primes), j.2.1, h⟩
    else 0), ?_⟩
  rw [show ConcreteCategory.hom ((deningerResidueAddSheaf P A).obj.map i) =
    deningerResidueAddRes P A (leOfHom i.unop) from deningerResidueAddPresheaf_hom P A i]
  funext j
  show (if h : deningerClosedPt ((j : Nat.Primes)) ∈ W₂.unop then
    g ⟨(j : Nat.Primes), j.2.1, h⟩ else 0) = g j
  rw [dif_pos j.2.2]

variable [CategoryTheory.HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase)]

/-- **The direct sum of skyscrapers has no higher cohomology.** -/
theorem deningerResidueAddSheaf_ext_eq_zero (U : Opens deningerArithBase) (n : ℕ)
    (x : deningerSheafCohomology.{0} U (deningerResidueAddSheaf P A) (n + 1)) : x = 0 :=
  deningerFlasque_ext_eq_zero n (deningerResidueAddSheaf P A)
    (deningerResidueAddSheaf_isFlasque P A) U x

/-- **The residue target has amplitude `[0,0]`.** -/
theorem deningerResidueAddSheaf_subsingleton_cohomology (U : Opens deningerArithBase) (n : ℕ) :
    Subsingleton (deningerSheafCohomology.{0} U (deningerResidueAddSheaf P A) (n + 1)) :=
  deningerFlasque_subsingleton_cohomology (deningerResidueAddSheaf P A)
    (deningerResidueAddSheaf_isFlasque P A) U n

end RHTower
