import GaloisForLFunctions.HTGeometry.FinitelyGeneratedDivisibleSubgroup
import GaloisForLFunctions.HTGeometry.MilnorKTameResidueFinite
import GaloisForLFunctions.HTGeometry.MilnorKTotalResidue

/-!
# Divisible classes lie in the Milnor tame kernel

The first Milnor group of a finite field is finite, by the existing equivalence
`K₁ᴹ(F) ≃ Fˣ`.  Therefore every divisible subgroup of `K₂ᴹ` is killed by the finite-place total
residue map and lies in the tame kernel.  This is the exact algebraic step used by the Moore route
to tame-kernel torsion.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsLocalRing NumberField
open DirectSum

/-- The first Milnor group of a finite field is finite. -/
noncomputable instance finite_milnorKDeg_one
    (F : Type*) [Field F] [Finite F] : Finite (MilnorKDeg F 1) :=
  Finite.of_equiv (Additive Fˣ) (milnorDegOneEquiv F).symm.toEquiv

/-- Every divisible subgroup of degree-two Milnor `K`-theory lies in the tame kernel when all
finite residue rings are finite. -/
theorem addSubgroup_le_milnorTameKernel_of_nsmulDivisible_of_finiteResidue
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
    (D : AddSubgroup (MilnorKDeg K 2))
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : MilnorKDeg K 2, x ∈ D →
      ∃ y : MilnorKDeg K 2, y ∈ D ∧ n • y = x) :
    D ≤ milnorTameKernel R K 2 := by
  letI : ∀ v : HeightOneSpectrum R,
      Finite (MilnorKDeg
        (ResidueField ((v.valuation K).valuationSubring)) (2 - 1)) := fun v => by
    simpa using finite_milnorKDeg_one
      (ResidueField ((v.valuation K).valuationSubring))
  rw [milnorTameKernel_eq_ker_milnorTotalResidue]
  exact addSubgroup_le_ker_of_nsmulDivisible_directSumFinite D
    (milnorTotalResidue (R := R) K 2) hdiv

/-- Every divisible subgroup of `K₂ᴹ` of a number field lies in its finite-place tame kernel. -/
theorem addSubgroup_le_milnorTameKernel_of_nsmulDivisible_numberField
    (K : Type*) [Field K] [NumberField K]
    (D : AddSubgroup (MilnorKDeg K 2))
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : MilnorKDeg K 2, x ∈ D →
      ∃ y : MilnorKDeg K 2, y ∈ D ∧ n • y = x) :
    D ≤ milnorTameKernel (RingOfIntegers K) K 2 := by
  exact addSubgroup_le_milnorTameKernel_of_nsmulDivisible_of_finiteResidue K D hdiv

/-- Moore-route assembly for a number field: finite generation of the tame kernel and divisibility
of a reciprocity kernel force all of `K₂ᴹ` to be torsion. -/
theorem milnorKDegTwo_isTorsion_of_tameKernel_fg_of_ker_nsmulDivisible_numberField
    (K : Type*) [Field K] [NumberField K]
    [AddGroup.FG (milnorTameKernel (RingOfIntegers K) K 2)]
    {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    [∀ i, Finite (G i)]
    (φ : MilnorKDeg K 2 →+ ⨁ i, G i)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : MilnorKDeg K 2, x ∈ φ.ker →
      ∃ y : MilnorKDeg K 2, y ∈ φ.ker ∧ n • y = x) :
    AddMonoid.IsTorsion (MilnorKDeg K 2) := by
  have hkerT : φ.ker ≤ milnorTameKernel (RingOfIntegers K) K 2 :=
    addSubgroup_le_milnorTameKernel_of_nsmulDivisible_numberField K φ.ker hdiv
  exact isTorsion_of_ker_le_fg_of_ker_nsmulDivisible_directSumFinite φ
    (milnorTameKernel (RingOfIntegers K) K 2) hkerT hdiv

end GaloisForLFunctions.HTGeometry
