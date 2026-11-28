import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FixedFieldIdelicKernel

/-! Finite idelic Artin compatibility is preserved by restriction
to an intermediate field of an abelian extension. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L]

local instance : CommGroup Gal(L/K) :=
  { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }

local instance (E : IntermediateField K L) [IsAbelianGalois K E] : CommGroup Gal(E/K) :=
  { (inferInstance : Group Gal(E/K)) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : Fintype Gal(L/K) := Fintype.ofFinite _

theorem isFiniteIdelicArtin_restrict (E : IntermediateField K L) [IsAbelianGalois K E]
    (f : IdeleGroup K →* Gal(L/K)) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ x : Kˣ, f (diagonal K x) = 1) :
    IsFiniteIdelicArtin ((AlgEquiv.restrictNormalHom E).comp f) := by
  letI : NumberField E := NumberField.of_module_finite K E
  letI : Fintype Gal(E/K) := Fintype.ofFinite _
  obtain ⟨m, hu, hm⟩ := hf
  obtain ⟨q, g, -, -, hqd, hqu, hqg⟩ := exists_finite_idelic_artin K E Gal(E/K)
  have he : (AlgEquiv.restrictNormalHom E).comp f = g := by
    rw [← eq_restriction E]
    exact finite_idelic_artin_restrict K E L Gal(E/K) Gal(L/K) q m g f hqd hd
      (fun v hv => not_not.mp (fun h => hv ((hqu v).mpr h)))
      (fun v hv => not_not.mp (fun h => hv ((hu v).mpr h))) hqg hm
  rw [he]
  exact ⟨q, hqu, hqg⟩

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.isFiniteIdelicArtin_restrict
