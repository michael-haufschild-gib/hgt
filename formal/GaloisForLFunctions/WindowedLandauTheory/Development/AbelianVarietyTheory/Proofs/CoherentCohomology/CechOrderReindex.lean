import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechDatum
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.SubcoverCechRestriction

/-! Order-preserving reindexing preserves deletion signs and the linear
cohomology of a Čech datum. -/

noncomputable section

open CategoryTheory GlobalTheory.SchemeCohomology
open GaloisForLFunctions.HTGeometry.BorelWeil

namespace HTGeometry.FinsetCechDatum

variable {R ι κ : Type} [CommRing R] [LinearOrder ι] [LinearOrder κ]
  (D : FinsetCechDatum.{0} ι) [∀ s, Module R (D.obj s)]
  (hD : ∀ {s t : Finset ι} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x)
  (j : κ ≃o ι)

private abbrev onIndices (s : Finset κ) : Finset ι := s.map j.toOrderEmbedding.toEmbedding

private theorem onIndices_mono : Monotone (onIndices j) :=
  fun _ _ h => Finset.map_subset_map.2 h

private abbrev reindexed := D.comap (onIndices j) (onIndices_mono j)

private theorem d_reindex (x : D.Cochain) (s : Finset κ) :
    D.d x (onIndices j s) = (D.reindexed j).d (fun t => x (onIndices j t)) s := by
  let a (i : ι) : D.obj (onIndices j s) :=
    (cechSign (onIndices j s) i : ℤ) • D.res (Finset.erase_subset i (onIndices j s))
      (x ((onIndices j s).erase i))
  let b (i : κ) : D.obj (onIndices j s) :=
    (cechSign s i : ℤ) • D.res (onIndices_mono j (Finset.erase_subset i s))
      (x (onIndices j (s.erase i)))
  have h₁ : D.d x (onIndices j s) = ∑ i ∈ s, a (j i) :=
    Finset.sum_map s j.toOrderEmbedding.toEmbedding a
  have h₂ : (D.reindexed j).d (fun t => x (onIndices j t)) s = ∑ i ∈ s, b i := rfl
  rw [h₁, h₂]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (cechSign (onIndices j s) (j i) : ℤ) = cechSign s i :=
    cechSign_orderEmbedding j.toOrderEmbedding s i
  exact congrArg₂ (fun (c : ℤ) (u : D.obj (onIndices j s)) => c • u) hs
    (D.res_cochain_congr x (Finset.map_erase j.toOrderEmbedding.toEmbedding s i).symm _ _)

private def cochainEquiv : D.Cochain ≃ₗ[R] (D.reindexed j).Cochain :=
  (LinearEquiv.piCongrLeft R D.obj j.toEquiv.finsetCongr).symm

private theorem cochainEquiv_apply (x : D.Cochain) (s : Finset κ) :
    D.cochainEquiv (R := R) j x s = x (onIndices j s) := rfl

private def degreeReindex (n : ℕ) :
    D.degreeSubmodule (R := R) n →ₗ[R] (D.reindexed j).degreeSubmodule (R := R) n where
  toFun x := ⟨D.cochainEquiv j x.1, fun s hs =>
    (D.cochainEquiv_apply j x.1 s).trans
      (x.2 (onIndices j s) (by simpa only [onIndices, Finset.card_map] using hs))⟩
  map_add' x y := Subtype.ext ((D.cochainEquiv j).map_add x.1 y.1)
  map_smul' r x := Subtype.ext ((D.cochainEquiv j).map_smul r x.1)

private theorem degreeReindex_bijective (n : ℕ) : Function.Bijective (D.degreeReindex (R := R) j n) := by
  let I := D.cochainEquiv (R := R) j
  refine ⟨fun x y h => Subtype.ext (I.injective (congrArg Subtype.val h)), fun y => ?_⟩
  let x := I.symm y.1
  have hx : D.IsDeg x n := by
    intro s
    obtain ⟨t, rfl⟩ := j.toEquiv.finsetCongr.surjective s
    intro hs
    have e : x (onIndices j t) = y.1 t := congrFun (I.apply_symm_apply y.1) t
    exact e.trans (y.2 t (by simpa only [Equiv.finsetCongr_apply, Finset.card_map] using hs))
  exact ⟨⟨x, hx⟩, Subtype.ext (I.apply_symm_apply y.1)⟩

/-- Reindexing by an order isomorphism gives an isomorphism of Čech complexes. -/
def linearComplexIsoReindex :
    (D.linearComplex hD) ≅ ((D.reindexed j).linearComplex
      (fun h r x => hD (onIndices_mono j h) r x)) := by
  let E := D.reindexed j
  have hE {s t : Finset κ} (h : s ⊆ t) (r : R) (x : E.obj s) :
      E.res h (r • x) = r • E.res h x := hD (onIndices_mono j h) r x
  let φ : D.linearComplex hD ⟶ E.linearComplex hE :=
    CochainComplex.ofHom (fun n => ModuleCat.ofHom (D.degreeReindex j n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [linearComplex, CochainComplex.of_d]
      apply Subtype.ext
      funext s
      exact (D.d_reindex j x.1 s).symm)
  haveI (n : ℕ) : IsIso (φ.f n) := by
    let e := LinearEquiv.ofBijective (D.degreeReindex (R := R) j n) (D.degreeReindex_bijective j n)
    change IsIso e.toModuleIso.hom
    infer_instance
  letI := HomologicalComplex.Hom.isIso_of_components φ
  exact asIso φ

end HTGeometry.FinsetCechDatum
