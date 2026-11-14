import GaloisForLFunctions.RepresentationLifting.TruncatedPeriodicComplex
import Mathlib.CategoryTheory.Abelian.Ext

/-!
# Self-extensions of the truncated polynomial residue

Applying `Hom(-, A/(x))` to the rank-one periodic resolution kills every
differential. Consequently `Ext_A^q(A/(x), A/(x))` is the residue module in
every degree, over any commutative coefficient ring.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open CategoryTheory

variable (R : Type*) [CommRing R]

/-- The nilpotent generator acts by zero on the coefficient residue. -/
theorem truncatedRoot_smul_residue (n : ℕ) (m : TruncatedResidue R n) :
    truncatedRoot R (n + 2) • m = 0 := by
  change Ideal.Quotient.mk (truncatedAugmentationIdeal R n) (truncatedRoot R (n + 2)) * m = 0
  have h : Ideal.Quotient.mk (truncatedAugmentationIdeal R n) (truncatedRoot R (n + 2)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [h, zero_mul]

/-- Every map to the residue annihilates both periodic differentials. -/
theorem truncatedPeriodicDifferential_comp_residue (n q : ℕ)
    (f : TruncatedPeriodicTerm R n ⟶
      ModuleCat.of (TruncatedPolynomialAlgebra R (n + 2)) (TruncatedResidue R n)) :
    truncatedPeriodicDifferential R n q ≫ f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change f.hom (truncatedRoot R (n + 2) ^ truncatedPeriodicExponent n q • v) = 0
  rw [map_smul]
  unfold truncatedPeriodicExponent
  split
  · rw [pow_one, truncatedRoot_smul_residue]
  · rw [pow_succ' (truncatedRoot R (n + 2)) n, mul_smul, truncatedRoot_smul_residue]

/-- The cochain complex computing self-extensions of the residue. -/
def truncatedResidueCochain (n : ℕ) :
    CochainComplex (ModuleCat (TruncatedPolynomialAlgebra R (n + 2))) ℕ :=
  (truncatedPeriodicComplex R n).linearYonedaObj (TruncatedPolynomialAlgebra R (n + 2))
    (ModuleCat.of (TruncatedPolynomialAlgebra R (n + 2)) (TruncatedResidue R n))

theorem truncatedResidueCochain_d_succ (n q : ℕ) :
    (truncatedResidueCochain R n).d q (q + 1) = 0 := by
  rw [truncatedResidueCochain, ChainComplex.linearYonedaObj_d, truncatedPeriodicComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact truncatedPeriodicDifferential_comp_residue R n q f

theorem truncatedResidueCochain_d (n i j : ℕ) :
    (truncatedResidueCochain R n).d i j = 0 := by
  by_cases h : i + 1 = j
  · subst j
    exact truncatedResidueCochain_d_succ R n i
  · exact (truncatedResidueCochain R n).shape _ _ h

/-- Evaluation at `1` identifies every cochain term with the residue. -/
def truncatedResidueCochainTermIso (n q : ℕ) :
    (truncatedResidueCochain R n).X q ≅
      ModuleCat.of (TruncatedPolynomialAlgebra R (n + 2)) (TruncatedResidue R n) :=
  (ModuleCat.homLinearEquiv.trans
    (LinearMap.ringLmapEquivSelf (TruncatedPolynomialAlgebra R (n + 2))
      (TruncatedPolynomialAlgebra R (n + 2)) (TruncatedResidue R n))).toModuleIso

/-- Every residue self-extension group is a copy of the residue, in all degrees. -/
def truncatedResidueExtIso (n q : ℕ) :
    ((Ext (TruncatedPolynomialAlgebra R (n + 2))
      (ModuleCat (TruncatedPolynomialAlgebra R (n + 2))) q).obj
        (Opposite.op (ModuleCat.of (TruncatedPolynomialAlgebra R (n + 2))
          (TruncatedResidue R n)))).obj
            (ModuleCat.of (TruncatedPolynomialAlgebra R (n + 2)) (TruncatedResidue R n)) ≅
      ModuleCat.of (TruncatedPolynomialAlgebra R (n + 2)) (TruncatedResidue R n) :=
  (truncatedProjectiveResolution R n).isoExt q _ ≪≫
    (ShortComplex.LeftHomologyData.ofZeros ((truncatedResidueCochain R n).sc q)
      (truncatedResidueCochain_d R n _ _) (truncatedResidueCochain_d R n _ _)).homologyIso ≪≫
    truncatedResidueCochainTermIso R n q

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.truncatedResidueExtIso
