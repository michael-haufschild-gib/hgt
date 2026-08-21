import GaloisForLFunctions.HTGeometry.MilnorKTotalResidue

/-!
# Quotient form of the finite-support Milnor residue map

For a fraction field of a Dedekind domain, quotienting Milnor `K`-theory by its everywhere
unramified tame kernel gives exactly the finite-support local residue profiles realized globally.
This is the first-isomorphism form of the restricted local-to-global map.
-/

namespace GaloisForLFunctions.HTGeometry

section TotalResidue

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Modulo the everywhere-unramified tame kernel, a global Milnor class is exactly its realized
finite-support family of local residues. -/
noncomputable def milnorTameResidueQuotientEquiv (n : ℕ) :
    (MilnorKDeg K n ⧸ milnorTameKernel R K n) ≃+
      (milnorTotalResidue (R := R) K n).range :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (milnorTameKernel_eq_ker_milnorTotalResidue (R := R) K n)).trans
    (QuotientAddGroup.quotientKerEquivRange (milnorTotalResidue (R := R) K n))

/-- The quotient class of a global Milnor element is represented by its total local residue. -/
theorem milnorTameResidueQuotientEquiv_mk (n : ℕ) (x : MilnorKDeg K n) :
    (milnorTameResidueQuotientEquiv (R := R) K n
      (QuotientAddGroup.mk x)).1 = milnorTotalResidue (R := R) K n x :=
  rfl

end TotalResidue

end GaloisForLFunctions.HTGeometry
