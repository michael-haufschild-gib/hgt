import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RayCharactersOfGlobalArtin
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.GlobalIdelicArtinQuotient

/-! Every open subgroup of the compact idelic quotient is the kernel of
a finite Artin quotient. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem exists_finite_idelic_artin_of_open
    (N : Subgroup (CompactIdeleClassQuotient K)) (hN : IsOpen (N : Set (CompactIdeleClassQuotient K))) :
    ∃ V : finiteAbelianExtensions K Ω,
      let L := (V : IntermediateField K Ω)
      letI := V.2.1
      ∃ (E : IntermediateField K L) (hE : IsAbelianGalois K E),
        letI := hE
        ∃ f : IdeleGroup K →* Gal(E/K),
          Continuous f ∧ Function.Surjective f ∧
          f.ker = N.comap (toCompactIdeleClassQuotient K) ∧ IsFiniteIdelicArtin f := by
  obtain ⟨a, ha, hm, -⟩ := exists_global_idelic_artin K Ω
  obtain ⟨V, hV⟩ := exists_finite_restriction_kernel_le K Ω a ha N hN (globalArtin_ker_le_open a hm N hN)
  let L := (V : IntermediateField K Ω)
  letI := V.2.1
  letI := V.2.2
  letI : NumberField L := NumberField.of_module_finite K L
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  let f := (restrictAb L (le_maximalAbelianExtension L)).comp
    (a.comp (toCompactIdeleClassQuotient K))
  obtain ⟨m, hr, hp⟩ := hm V
  have hd (u : Kˣ) : f (diagonal K u) = 1 := by
    simp only [f, MonoidHom.comp_apply, toCompactIdeleClassQuotient_diagonal, map_one]
  have hk : f.ker ≤ N.comap (toCompactIdeleClassQuotient K) := fun x hx =>
    hV (toCompactIdeleClassQuotient K x) (MonoidHom.mem_ker.mp hx)
  obtain ⟨E, hE, g, hg, hs, he, hA⟩ :=
    exists_finite_idelic_artin_of_kernel_le m f hd
      (fun v hv => not_not.mp fun hu => hv ((hr v).mpr hu)) hp _ hk
  exact ⟨V, E, hE, g, hg, hs, he, hA⟩

end GlobalTheory.Reciprocity
