import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedSaturatingGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LargeDegreeGradedCechExactness
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechMaps
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! A graded module with finite dehomogenizations has vanishing positive
Čech cohomology in all sufficiently large degrees. -/

noncomputable section

open CategoryTheory DirectSum HTGeometry MvPolynomial

namespace GlobalTheory

private theorem gradedCech_exactAt_succ {ι R M : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CommRing R] [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (D : ℤ → Submodule R M) [PolyGradedSMul ι D]
    (t : ℤ) (q : ℕ) (h : (homLocDatum (ι := ι) D t).ExactAt (q + 1)) :
    (gradedCech (ι := ι) D t).ExactAt (q + 1) := by
  let A := homLocDatum (ι := ι) D t
  let C := gradedCech (ι := ι) D t
  let S := C.sc' q (q + 1) (q + 2)
  have hd (n : ℕ) (z : A.degreeSubmodule (R := R) n) :
      ((C.d n (n + 1)) z).1 = A.d z.1 := by
    change (CochainComplex.of.d (fun j : ℕ => ModuleCat.of R (A.degreeSubmodule (R := R) j))
      _ n (n + 1) z).1 = _
    rw [CochainComplex.of_d]
    rfl
  apply (C.exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp)).mpr
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
  intro x
  constructor
  · intro hx
    change (C.d (q + 1) (q + 1 + 1)) x = 0 at hx
    have hdx : A.d x.1 = 0 := (hd (q + 1) x).symm.trans (congrArg Subtype.val hx)
    obtain ⟨y, hy, hdy⟩ := h x.1 x.2 hdx
    let b : C.X q := ⟨y, hy⟩
    exact ⟨b, Subtype.ext ((hd q b).trans hdy)⟩
  · rintro ⟨y, rfl⟩
    exact congr($(S.zero).hom y)

/-- Finite generators on the coordinate charts lie in a finite homogeneous
submodule with the same localizations on all nonempty intersections. -/
theorem exists_gradedCech_exactAt_succ_of_finite_charts
    {ι R M : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (D : ℤ → Submodule R M) [PolyGradedSMul ι D]
    [Decomposition D]
    (hfin : ∀ i : ι, Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) M)) :
    ∃ b : ℤ, ∀ t ≥ b, ∀ q : ℕ, (gradedCech (ι := ι) D t).ExactAt (q + 1) := by
  obtain ⟨r, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating D hfin
  let N := Submodule.span (MvPolynomial ι R) (Set.range g)
  have hN : N.IsHomogeneous D := by
    apply isHomogeneous_span_gr
    intro y hy
    change y ∈ Set.range g at hy
    obtain ⟨j, rfl⟩ := hy
    exact ⟨d j, hg j⟩
  let E := grSub D N
  letI : Decomposition E := grSubDecomposition hN
  letI : Module.Finite (MvPolynomial ι R) N := Module.Finite.iff_fg.mpr
    (Submodule.fg_span (Set.finite_range g))
  obtain ⟨b, hb⟩ := exists_gradedCech_exactAt_of_largeDegree (ι := ι) E
  refine ⟨b, fun t ht q => ?_⟩
  have hi : IsGradedMap E D N.subtype := fun _ _ x => x
  let φ := homLocDatumMap hi t
  let v : gradedCech (ι := ι) E t ⟶ gradedCech (ι := ι) D t := FinsetCechDatum.linearCochainMap
    (fun h => homLocDatum_res_smul E h t) (fun h => homLocDatum_res_smul D h t)
    φ (fun s a x => (homLocMap hi s t).map_smul a x)
  have hv : IsIso v := FinsetCechDatum.isIso_linearCochainMap _ _ _ _ (fun _ ⟨i, hi'⟩ =>
    homLocMap_bijective_of_X hi hi'
      (fun z hz => ⟨0, by
        simpa only [pow_zero, one_smul] using N.injective_subtype (hz.trans (map_zero N.subtype).symm)⟩)
      (fun y => by
        obtain ⟨k, hk⟩ := hsat i y
        exact ⟨k, ⟨⟨_, hk⟩, rfl⟩⟩) t)
  exact (gradedCech_exactAt_succ (ι := ι) E t q (hb t ht (q + 1))).of_iso (asIso v)

end GlobalTheory
