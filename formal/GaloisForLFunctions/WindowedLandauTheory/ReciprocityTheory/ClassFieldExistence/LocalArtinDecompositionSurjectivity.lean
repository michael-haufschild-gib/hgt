import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinFullDecomposition
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteIdelicArtinInertiaSurjectivity

/-! At a finite place the global Artin map has image the decomposition
group, and its restriction to units has image inertia. Over the fixed
field of decomposition the local Artin map is surjective, and idelic
norm compatibility descends the preimages. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open scoped GlobalTheory.Reciprocity.AdicLiesOver IsMulCommutative Pointwise

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L]

local notation "G" => Gal(L/K)

theorem finiteIdelicArtin_range_eq_decomposition
    (f : IdeleGroup K →* G) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ a : Kˣ, f (diagonal K a) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    (f.comp (finiteEmbedding v)).range = MulAction.stabilizer G w.asIdeal := by
  let D := MulAction.stabilizer G w.asIdeal
  let E := fixedField D
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E := IsAbelianGalois.of_algHom E.val
  letI : IsAbelianGalois E L := IsAbelianGalois.tower_top K E L
  letI : Fintype Gal(L/E) := Fintype.ofFinite _
  letI : CommGroup Gal(L/E) :=
    { (inferInstance : Group Gal(L/E)) with mul_comm := IsMulCommutative.is_comm.comm }
  let u := w.under (𝓞 E)
  letI : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  letI : u.asIdeal.LiesOver v.asIdeal := liesOver_under_intermediateField v w E
  let j : Gal(L/E) →* G := AlgEquiv.restrictScalarsHom K
  have hD : E.fixingSubgroup = D := fixingSubgroup_fixedField D
  have hw : MulAction.stabilizer Gal(L/E) w.asIdeal = ⊤ := by
    apply top_unique
    intro τ _
    have ht : j τ ∈ E.fixingSubgroup := fun a => τ.commutes a
    rw [hD] at ht
    exact MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp ht)
  obtain ⟨m, ψ, -, -, hψd, hψu, hψm⟩ := exists_finite_idelic_artin E L Gal(L/E)
  have hψ : IsFiniteIdelicArtin ψ := ⟨m, hψu, hψm⟩
  have hs := finiteIdelicArtin_surjective_at_full_decomposition ψ hψ hψd u w hw
  have hN := finiteIdelicArtin_comp_ideleNorm K E L j (fun _ _ => rfl) f ψ hf hψ hd hψd
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact finiteIdelicArtin_finiteEmbedding_mem_decomposition f hf hd v w x
  intro σ hσ
  have hfix (a : E) : σ (algebraMap E L a) = algebraMap E L a :=
    (show σ ∈ E.fixingSubgroup from hD.symm ▸ hσ) a
  let τ : Gal(L/E) := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hfix
  obtain ⟨y, hy⟩ := hs τ
  let u' : finitePlacesAbove E v := ⟨u, (mem_finitePlacesAbove E v u).mpr inferInstance⟩
  have h := DFunLike.congr_fun hN (finiteEmbedding u y)
  change f (ideleNorm (finiteEmbedding u'.val y)) = j ((ψ.comp (finiteEmbedding u)) y) at h
  rw [ideleNorm_finiteEmbedding v u', hy] at h
  exact ⟨Units.map (Algebra.norm (v.adicCompletion K)) y, h⟩

theorem finiteIdelicArtin_range_localUnits_eq_inertia
    (f : IdeleGroup K →* G) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ a : Kˣ, f (diagonal K a) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    (unitsLevel v 0).map (f.comp (finiteEmbedding v)) = w.asIdeal.inertia G :=
  finiteIdelicArtin_range_localUnits_eq_inertia_of_range f hf hd v w
    (finiteIdelicArtin_range_eq_decomposition f hf hd v w)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_range_eq_decomposition
#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_range_localUnits_eq_inertia
