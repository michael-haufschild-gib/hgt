import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicProductNorm

/-! The norm equations over individual places glue when the chosen
finite preimages are integral units. -/

noncomputable section

open NumberField IsDedekindDomain Filter
open scoped GlobalTheory.Reciprocity.AdicLiesOver NumberField.LiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

private def finiteUnitsFromFibres
    (y : ∀ v : HeightOneSpectrum (𝓞 K), ∀ w : finitePlacesAbove L v, (w.val.adicCompletion L)ˣ)
    (w : HeightOneSpectrum (𝓞 L)) : (w.adicCompletion L)ˣ :=
  y (w.under (𝓞 K)) ⟨w, (mem_finitePlacesAbove L _ w).mpr ⟨rfl⟩⟩

private theorem finiteUnitsFromFibres_apply
    (y : ∀ v : HeightOneSpectrum (𝓞 K), ∀ w : finitePlacesAbove L v, (w.val.adicCompletion L)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (h : w ∈ finitePlacesAbove L v) :
    finiteUnitsFromFibres y w = y v ⟨w, h⟩ := by
  have hv := (finitePlace_under_eq_iff w v).mpr ((mem_finitePlacesAbove L v w).mp h)
  subst v
  rfl

private def infiniteUnitsFromFibres
    (y : ∀ v : InfinitePlace K, ∀ w : infinitePlacesAbove L v, w.val.Completionˣ)
    (w : InfinitePlace L) : w.Completionˣ :=
  y (w.comap (algebraMap K L)) ⟨w, (mem_infinitePlacesAbove L _ w).mpr ⟨rfl⟩⟩

private theorem infiniteUnitsFromFibres_apply
    (y : ∀ v : InfinitePlace K, ∀ w : infinitePlacesAbove L v, w.val.Completionˣ)
    (v : InfinitePlace K) (w : InfinitePlace L) (h : w ∈ infinitePlacesAbove L v) :
    infiniteUnitsFromFibres y w = y v ⟨w, h⟩ := by
  letI := (mem_infinitePlacesAbove L v w).mp h
  have hv := InfinitePlace.LiesOver.comap_eq w v
  subst v
  rfl

theorem mem_range_ideleNorm_of_localIntegralPreimages (x : IdeleGroup K)
    (hf : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ y : ∀ w : finitePlacesAbove L v, (w.val.adicCompletion L)ˣ,
        (∀ w, y w ∈ (Submonoid.ofClass (w.val.adicCompletionIntegers L)).units) ∧
          finiteLocalNorm L v y = finiteProj v x)
    (hi : ∀ v : InfinitePlace K, infiniteProj v x ∈ (infiniteLocalNorm L v).range) :
    x ∈ (ideleNorm (K := K) (L := L)).range := by
  choose yf hf hf' using hf
  choose yi hi using hi
  let y := ofLocalUnits ⟨finiteUnitsFromFibres yf, Filter.Eventually.of_forall fun w =>
    hf (w.under (𝓞 K)) ⟨w, (mem_finitePlacesAbove L _ w).mpr ⟨rfl⟩⟩⟩
    (infiniteUnitsFromFibres yi)
  refine ⟨y, ext_of_localUnits (fun v => ?_) (fun w => ?_)⟩
  · rw [finiteProj_ideleNorm, ← hf' v]
    apply congrArg (finiteLocalNorm L v)
    funext w
    exact (finiteProj_ofLocalUnits _ _ _).trans (finiteUnitsFromFibres_apply yf v w.val w.2)
  · rw [infiniteProj_ideleNorm, ← hi w]
    apply congrArg (infiniteLocalNorm L w)
    funext v
    exact (infiniteProj_ofLocalUnits _ _ _).trans (infiniteUnitsFromFibres_apply yi w v.val v.2)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.mem_range_ideleNorm_of_localIntegralPreimages
