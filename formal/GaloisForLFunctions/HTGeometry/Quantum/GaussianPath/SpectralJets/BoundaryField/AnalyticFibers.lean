import GaloisForLFunctions.HTGeometry.AnalyticNullPreimage
import GaloisForLFunctions.HTGeometry.SortedEigenbranchAnalytic
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum

/-! # Null sets of spectral actions along a single affine field -/
open MeasureTheory Matrix Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section

private theorem finite_levels_nonflat {f : ℝ→ℝ} {U : Set ℝ} (hu : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (hlevel : ∀ c, {z ∈ U | f z=c}.Finite)
    (x : ℝ) (hx : x∈U) : ¬ ∀ᶠ z in 𝓝 x, deriv f z=0 := by
  intro hflat
  have hnear : ∀ᶠ z in 𝓝 x, z∈U := hu.mem_nhds hx
  obtain ⟨V,hV,ho,hxV⟩ := mem_nhds_iff.mp (hnear.and hflat)
  have hVU : V⊆U := fun z hz => (hV hz).1
  have hzero : V.EqOn (deriv f) 0 := fun z hz => (hV hz).2
  have hop := ho.isOpen_inter_preimage_of_deriv_eq_zero (hf.differentiableOn.mono hVU) hzero {f x}
  have hp := hop.measure_pos volume ⟨x,hxV,rfl⟩
  have hsub : V ∩ f ⁻¹' {f x} ⊆ {z ∈ U | f z=f x} := fun z hz => ⟨hVU hz.1,hz.2⟩
  exact hp.ne' (measure_mono_null hsub ((hlevel (f x)).countable.measure_zero volume))

/-- Finite level sets exclude a locally vanishing derivative on the analytic
locus. Consequently every null set of action values has a null preimage. -/
theorem null_preimage_of_finite_levels {f : ℝ→ℝ} {U : Set ℝ} (hu : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (hlevel : ∀ c, {z ∈ U | f z=c}.Finite)
    (S : Set ℝ) (hS : volume S=0) : volume (f ⁻¹' S ∩ U)=0 :=
  analyticOnNhd_preimage_volume_eq_zero_of_deriv_not_eventually_zero hu hf
    (finite_levels_nonflat hu hf hlevel) hS

/-- The critical field settings of such an action are isolated within the
simple-spectrum locus, hence countable. -/
theorem countable_critical_of_finite_levels {f : ℝ→ℝ} {U : Set ℝ} (hu : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (hlevel : ∀ c, {z ∈ U | f z=c}.Finite) :
    {z ∈ U | deriv f z=0}.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  apply isDiscrete_iff_nhdsNE.mpr
  intro z hz
  apply inf_principal_eq_bot.mpr
  have h := ((hf z hz.1).deriv.eventually_eq_zero_or_eventually_ne_zero).resolve_left
    (finite_levels_nonflat hu hf hlevel z hz.1)
  exact h.mono fun _ hy hmem => hy hmem.2

variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Coord (I : Type*) [Fintype I] := Fin (Fintype.card I)
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Sort the native eigenvalues after numbering the physical register. -/
def sortedFieldLevels (E : ℝ→I→ℝ) (t : ℝ) : Coord I→ℝ :=
  sortedTuple (E t ∘ (Fintype.equivFin I).symm)

/-- Sorting gives analytic labels near every simple point of an affine
Hermitian family. The base matrix and field direction may be arbitrary. -/
theorem sortedFieldLevels_analytic {A Z : Mat I} (ha : A.IsHermitian) (hz : Z.IsHermitian)
    (hH : ∀ z : ℝ, (A+(z:ℂ) • Z).IsHermitian) {t : ℝ}
    (hi : Function.Injective (hH t).eigenvalues) (j : Coord I) :
    AnalyticAt ℝ (fun z => sortedFieldLevels (fun s => (hH s).eigenvalues) z j) t := by
  let e := Fintype.equivFin I
  let P : Fin 2→Mat (Coord I) := ![reindex e e A,reindex e e Z]
  have hP (b : Fin 2) : (P b).IsHermitian := by
    fin_cases b
    · exact ha.reindex e
    · exact hz.reindex e
  let w (s : ℝ) : Fin 2→ℝ := ![1,s]
  have he (s : ℝ) : spectralEnsembleMatrix P (w s)=reindex e e (A+(s:ℂ) • Z) := by
    ext i l
    simp [spectralEnsembleMatrix,Fin.sum_univ_two,P,w,reindex_apply]
  have hsort (s : ℝ) : sortedEnsembleSpectrum hP (w s)=sortedFieldLevels (fun u => (hH u).eigenvalues) s := by
    refine Eq.trans ?_ (sortedTuple_eigenvalues_reindex e (hH s))
    have same {B C : Mat (Coord I)} (hb : B.IsHermitian) (hc : C.IsHermitian) (h : B=C) :
        sortedTuple hb.eigenvalues=sortedTuple hc.eigenvalues := by subst C; rfl
    exact same _ _ (he s)
  have hin : Function.Injective (isHermitian_spectralEnsembleMatrix hP (w t)).eigenvalues := by
    rw [injective_iff_injective_sortedTuple]
    change Function.Injective (sortedEnsembleSpectrum hP (w t))
    rw [hsort]
    exact injective_sortedTuple (hi.comp e.symm.injective)
  have hw : AnalyticAt ℝ w t := by
    apply AnalyticAt.pi
    intro l
    fin_cases l
    · exact analyticAt_const
    · exact analyticAt_id
  exact ((analyticAt_sortedEnsembleSpectrum hP hin j).comp hw).congr
    (.of_forall fun s => congrFun (hsort s) j)

#print axioms null_preimage_of_finite_levels
#print axioms sortedFieldLevels_analytic
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
