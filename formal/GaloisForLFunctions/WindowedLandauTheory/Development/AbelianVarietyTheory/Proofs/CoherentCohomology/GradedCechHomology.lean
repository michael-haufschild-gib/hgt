import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ScalarCechGrading
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectCochainModel

/-! Grading cochains by cardinality recovers the cohomology of the alternating Čech complex. -/

noncomputable section

open CategoryTheory

namespace HTGeometry.FinsetCechDatum

variable {K ι : Type} [Field K] [DecidableEq ι] [LinearOrder ι] [Fintype ι]
  (D : FinsetCechDatum.{0} ι) [∀ s, Module K (D.obj s)]
  (hres : ∀ {s t : Finset ι} (h : s ⊆ t) (r : K) (x : D.obj s),
    D.res h (r • x) = r • D.res h x)

private theorem gradedTerm_comm (n : ℕ) (x : (D.graded hres).term (n + 1)) :
    (D.linearComplex hres).d n (n + 1) (D.gradedTermEquiv hres n x) =
      D.gradedTermEquiv hres (n + 1) ((D.graded hres).termMap (n + 1) x) := by
  change CochainComplex.of.d (fun j : ℕ => ModuleCat.of K (D.degreeSubmodule (R := K) j))
    _ n (n + 1) _ = _
  rw [CochainComplex.of_d]
  rfl

/-- The shifted grading and the ordinary unaugmented complex yield the same
cohomology. In degree zero both complexes have zero incoming differential. -/
theorem nonempty_gradedHomology_equiv (n : ℕ) :
    Nonempty (((D.graded hres).degreeShort n).homology ≃ₗ[K] (D.linearComplex hres).homology n) := by
  let C := D.linearComplex hres
  let G := D.graded hres
  cases n with
  | zero =>
    let S := G.degreeShort 0
    let T := C.sc' 0 0 1
    let E : S.X₂ ≃ₗ[K] T.X₂ := D.gradedTermEquiv hres 0
    let F : S.X₃ ≃ₗ[K] T.X₃ := D.gradedTermEquiv hres 1
    have hS : S.f = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hx : x = 0 := Subtype.ext ((G.π_apply_term 0 x).symm.trans (G.zero _))
      rw [hx, map_zero, map_zero]
    have hT : T.f = 0 := C.shape 0 0 (by simp)
    have hc (x : S.X₂) : T.g (E x) = F (S.g x) := D.gradedTerm_comm hres 0 x
    let φ : S ⟶ T :=
      ⟨0, E.toModuleIso.hom, F.toModuleIso.hom,
        by simp [hS, hT],
        ModuleCat.hom_ext (LinearMap.ext hc)⟩
    haveI : ShortComplex.QuasiIso φ := by
      rw [GlobalTheory.shortComplex_quasiIso_iff]
      constructor
      · intro y hy
        refine ⟨E.symm y, 0, F.injective ?_, ?_⟩
        · rw [← hc, E.apply_symm_apply, hy, map_zero]
        · change T.f 0 + E (E.symm y) = y
          rw [map_zero, zero_add, E.apply_symm_apply]
      · intro x z _ hz
        have hx : E x = 0 := hz.symm.trans (by rw [hT]; rfl)
        refine ⟨0, ?_⟩
        exact (map_zero S.f.hom).trans (E.injective (E.map_zero.trans hx.symm))
    exact ⟨(asIso (ShortComplex.homologyMap φ) ≪≫
      (C.homologyIsoSc' 0 0 1 (by simp) (by simp)).symm).toLinearEquiv⟩
  | succ n =>
    let S := G.degreeShort (n + 1)
    let T := C.sc' n (n + 1) (n + 2)
    let E : S ≅ T := ShortComplex.isoMk
      (D.gradedTermEquiv hres n).toModuleIso
      (D.gradedTermEquiv hres (n + 1)).toModuleIso
      (D.gradedTermEquiv hres (n + 2)).toModuleIso
      (ModuleCat.hom_ext (LinearMap.ext (D.gradedTerm_comm hres n)))
      (ModuleCat.hom_ext (LinearMap.ext (D.gradedTerm_comm hres (n + 1))))
    exact ⟨(ShortComplex.homologyMapIso E ≪≫
      (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).symm).toLinearEquiv⟩

end HTGeometry.FinsetCechDatum
