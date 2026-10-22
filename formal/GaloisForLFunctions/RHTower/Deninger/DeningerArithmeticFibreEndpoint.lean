import GaloisForLFunctions.RHTower.Deninger.DeningerResidueFibreCohomology
import GaloisForLFunctions.RHTower.Deninger.DeningerSkyscraperAcyclic
import GaloisForLFunctions.RHTower.Deninger.DeningerRestrictedPrimeAcyclic

/-!
# The fibre of the arithmetic residue morphism

Both residue targets on the arithmetic base — the direct sum of skyscrapers along a finite set of
primes and the restricted prime sum — are acyclic.  So for a surjective residue morphism into either
of them, the fibre carries all of the higher cohomology of the source: the comparison is an
isomorphism above degree one and is onto in degree one.

* `deningerSkyscraperFibre_ext_bijective` : the fibre of a residue into the skyscraper sum.
* `deningerPrimeFibre_ext_bijective` : the fibre of a residue into the restricted prime sum.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

variable [CategoryTheory.HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase)]

section Skyscraper

variable (P : Finset Nat.Primes)
variable {G : TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase}
variable (f : G ⟶ deningerResidueAddSheaf P ℤ) [Epi f]

/-- **The fibre of a surjective residue into the skyscraper sum carries all higher cohomology of
the source.** -/
theorem deningerSkyscraperFibre_ext_bijective (U : Opens deningerArithBase) (n : ℕ) :
    Function.Bijective (fun x : deningerSheafCohomology.{0} U
        (ShortComplex.mk (kernel.ι f) f (by simp)).X₁ (n + 2) =>
      x.comp (Ext.mk₀ (ShortComplex.mk (kernel.ι f) f (by simp)).f) (add_zero (n + 2))) :=
  deningerFibre_ext_bijective (deningerKernelShortExact f)
    (fun U m x => deningerResidueAddSheaf_ext_eq_zero P ℤ U m x) U n

/-- **In degree one the comparison is onto.** -/
theorem deningerSkyscraperFibre_ext_surjective (U : Opens deningerArithBase) :
    Function.Surjective (fun x : deningerSheafCohomology.{0} U
        (ShortComplex.mk (kernel.ι f) f (by simp)).X₁ 1 =>
      x.comp (Ext.mk₀ (ShortComplex.mk (kernel.ι f) f (by simp)).f) (add_zero 1)) :=
  deningerFibre_ext_surjective (deningerKernelShortExact f)
    (fun U m x => deningerResidueAddSheaf_ext_eq_zero P ℤ U m x) U

end Skyscraper

section RestrictedPrime

variable {E : Nat.Primes → Type} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
variable (n1 n2 : ∀ p, Seminorm ℝ (E p)) (α β : Nat.Primes → NNReal)
variable {G : TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase}
variable (f : G ⟶ deningerPrimeSheaf n1 n2 α β) [Epi f]

/-- **The fibre of a surjective residue into the restricted prime sum carries all higher cohomology
of the source.** -/
theorem deningerPrimeFibre_ext_bijective (U : Opens deningerArithBase) (n : ℕ) :
    Function.Bijective (fun x : deningerSheafCohomology.{0} U
        (ShortComplex.mk (kernel.ι f) f (by simp)).X₁ (n + 2) =>
      x.comp (Ext.mk₀ (ShortComplex.mk (kernel.ι f) f (by simp)).f) (add_zero (n + 2))) :=
  deningerFibre_ext_bijective (deningerKernelShortExact f)
    (fun U m x => deningerPrimeSheaf_ext_eq_zero n1 n2 α β U m x) U n

/-- **In degree one the comparison is onto.** -/
theorem deningerPrimeFibre_ext_surjective (U : Opens deningerArithBase) :
    Function.Surjective (fun x : deningerSheafCohomology.{0} U
        (ShortComplex.mk (kernel.ι f) f (by simp)).X₁ 1 =>
      x.comp (Ext.mk₀ (ShortComplex.mk (kernel.ι f) f (by simp)).f) (add_zero 1)) :=
  deningerFibre_ext_surjective (deningerKernelShortExact f)
    (fun U m x => deningerPrimeSheaf_ext_eq_zero n1 n2 α β U m x) U

end RestrictedPrime

end RHTower
