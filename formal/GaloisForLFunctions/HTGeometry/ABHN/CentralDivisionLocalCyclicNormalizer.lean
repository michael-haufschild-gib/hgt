import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionUnramifiedMaximalSubfieldGalois
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionSkolemNoether

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped NormedField ValuativeRel Valued

universe u

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [LocallyCompactSpace F] [DivisionRing A] [Algebra F A]
  [Module.Finite F A] [Algebra.IsCentral F A]

/-- Every local central division algebra has a degree-exact cyclic Galois maximal subfield and
an internal unit normalizing it. The degree-th power of the normalizer centralizes that field. -/
theorem exists_residueExhausting_cyclicNormalizer_power_mem_centralizer :
    ∃ x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A),
      let T := Algebra.adjoin F ({(x : A)} : Set A)
      ∃ hT : IsField T,
        letI : Field T := hT.toField
        letI : Algebra F T := Subalgebra.algebra T
        Module.finrank F T = divisionAlgebraDegree (F := F) (A := A) ∧
          (letI : NormedDivisionRing A :=
              divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A);
            letI : NontriviallyNormedField T :=
              divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
                (F := F) (A := A) T hT;
            letI : NormedSpace F T :=
              divisionAlgebraRestrictedRootDeterminantNormedSpace
                (F := F) (A := A) T hT;
            letI : IsUltrametricDist T :=
              divisionAlgebraRestrictedRootDeterminantIsUltrametricDist
                (F := F) (A := A) T hT;
            Nonempty (NormValuationResidue (F := T) ≃ₐ[NormValuationResidue (F := F)]
              DivisionAlgebraDeterminantResidue (F := F) (A := A))) ∧
          IsGalois F T ∧ ∃ hCyclic : IsCyclic Gal(T / F),
            letI : IsCyclic Gal(T / F) := hCyclic
            ∃ u : Aˣ,
              (∀ t : T, (t : A) * (u : A) =
                (u : A) * (cyclicGaloisGeneratorAnyUniverse F T t : T)) ∧
              (∀ t : T, Commute (t : A) ((u : A) ^ Module.finrank F T)) := by
  obtain ⟨x, hT, hdegree, ⟨hres⟩, hGalois, hCyclic, hsplit⟩ :=
    exists_residueExhausting_galoisMaximalSubfield_scalarExtension_eq_split
      (F := F) (A := A)
  let T := Algebra.adjoin F ({(x : A)} : Set A)
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : CompleteSpace T :=
    divisionAlgebraRestrictedRootDeterminantCompleteSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist
      (F := F) (A := A) T hT
  letI : ProperSpace T :=
    divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := A) T hT
  letI : FiniteDimensional F T := by infer_instance
  letI : IsGalois F T := hGalois
  letI : IsCyclic Gal(T / F) := hCyclic
  obtain ⟨u, hu, hupow⟩ :=
    exists_cyclicGaloisNormalizer_power_mem_centralizer F T A (Subalgebra.val T)
  refine ⟨x, hT, hdegree, ⟨hres⟩, hGalois, hCyclic, u, ?_, ?_⟩
  · exact hu
  · exact hupow
/-- The local cyclic normalizer has a base-field power parameter. This is the defining scalar
parameter of the cyclic crossed product attached to the division algebra. -/
theorem exists_residueExhausting_cyclicNormalizer_baseParameter :
    ∃ x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A),
      let T := Algebra.adjoin F ({(x : A)} : Set A)
      ∃ hT : IsField T,
        letI : Field T := hT.toField
        letI : Algebra F T := Subalgebra.algebra T
        Module.finrank F T = divisionAlgebraDegree (F := F) (A := A) ∧
          (letI : NormedDivisionRing A :=
              divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A);
            letI : NontriviallyNormedField T :=
              divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
                (F := F) (A := A) T hT;
            letI : NormedSpace F T :=
              divisionAlgebraRestrictedRootDeterminantNormedSpace
                (F := F) (A := A) T hT;
            letI : IsUltrametricDist T :=
              divisionAlgebraRestrictedRootDeterminantIsUltrametricDist
                (F := F) (A := A) T hT;
            Nonempty (NormValuationResidue (F := T) ≃ₐ[NormValuationResidue (F := F)]
              DivisionAlgebraDeterminantResidue (F := F) (A := A))) ∧
          ∃ hGalois : IsGalois F T,
            letI : IsGalois F T := hGalois
            ∃ hCyclic : IsCyclic Gal(T / F),
              letI : IsCyclic Gal(T / F) := hCyclic
              ∃ u : Aˣ, ∃ a : Fˣ,
                (∀ t : T, (t : A) * (u : A) =
                  (u : A) * (cyclicGaloisGeneratorAnyUniverse F T t : T)) ∧
                (u : A) ^ Module.finrank F T = algebraMap F A (a : F) := by
  obtain ⟨x, hT, hdegree, ⟨hres⟩, hGalois, hCyclic, u, hu, hupow⟩ :=
    exists_residueExhausting_cyclicNormalizer_power_mem_centralizer
      (F := F) (A := A)
  let T := Algebra.adjoin F ({(x : A)} : Set A)
  letI : Field T := hT.toField
  letI : Algebra F T := Subalgebra.algebra T
  letI : FiniteDimensional F T := by infer_instance
  letI : IsGalois F T := hGalois
  letI : IsCyclic Gal(T / F) := hCyclic
  have hcommT : IsMulCommutative T := inferInstance
  obtain ⟨S, hTS, hcommS, hfieldS, hmaxS⟩ :=
    exists_maximalCommutativeSubfield_containing_element F A (x : A)
  have hSsq : Module.finrank F S * Module.finrank F S = Module.finrank F A :=
    maximalCommutativeSubfield_finrank_sq F A S hcommS hfieldS hmaxS
  have hSdegree : Module.finrank F S = divisionAlgebraDegree (F := F) (A := A) :=
    Nat.mul_self_inj.mp
      (hSsq.trans (divisionAlgebraDegree_mul_self (F := F) (A := A)).symm)
  have hTeqS : T = S :=
    Subalgebra.eq_of_le_of_finrank_eq hTS (hdegree.trans hSdegree.symm)
  have hmaxT : ∀ U : Subalgebra F A, T ≤ U → IsMulCommutative U → U = T := by
    intro U hTU hcommU
    exact (hmaxS U (by simpa only [hTeqS] using hTU) hcommU).trans hTeqS.symm
  have hcentral : Subalgebra.centralizer F (T : Set A) = T :=
    maximalCommutativeSubalgebra_centralizer_eq F A T hcommT hmaxT
  let n := Module.finrank F T
  let pA : A := (u : A) ^ n
  have hpcentral : pA ∈ Subalgebra.centralizer F (T : Set A) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro z hz
    exact hupow ⟨z, hz⟩
  have hpT : pA ∈ T := by
    rw [← hcentral]
    exact hpcentral
  let p : T := ⟨pA, hpT⟩
  let sigma := cyclicGaloisGeneratorAnyUniverse F T
  have hfixCoe : ((sigma p : T) : A) = (p : A) := by
    apply mul_left_cancel₀ u.ne_zero
    calc
      (u : A) * ((sigma p : T) : A) = (p : A) * (u : A) := (hu p).symm
      _ = ((u : A) ^ n) * (u : A) := rfl
      _ = (u : A) * ((u : A) ^ n) := (Commute.self_pow (u : A) n).eq.symm
      _ = (u : A) * (p : A) := rfl
  have hfix : sigma p = p := Subtype.ext hfixCoe
  let H : Subgroup Gal(T / F) := MulAction.stabilizer Gal(T / F) p
  have hgenmem : sigma ∈ H := by
    change sigma p = p
    exact hfix
  have hfixed : ∀ tau : Gal(T / F), tau p = p := by
    intro tau
    have htaumem : tau ∈ H :=
      (Subgroup.zpowers_le.mpr hgenmem)
        (cyclicGaloisGeneratorAnyUniverse_spec F T tau)
    exact htaumem
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (p : T)).mpr hfixed
  have hpne : p ≠ 0 := by
    intro hp0
    have hpA0 : (u : A) ^ n = 0 := by
      change (p : A) = 0
      exact congrArg Subtype.val hp0
    exact pow_ne_zero n u.ne_zero hpA0
  have hane : a ≠ 0 := by
    intro ha0
    apply hpne
    rw [← ha, ha0, map_zero]
  let aUnit : Fˣ := Units.mk0 a hane
  refine ⟨x, hT, hdegree, ⟨hres⟩, hGalois, hCyclic, u, aUnit, hu, ?_⟩
  calc
    (u : A) ^ Module.finrank F T = (p : A) := rfl
    _ = ((algebraMap F T a : T) : A) := congrArg Subtype.val ha.symm
    _ = algebraMap F A (aUnit : F) := by
      rw [Subalgebra.coe_algebraMap]
      rfl

end

end GaloisForLFunctions.HTGeometry.ABHN
