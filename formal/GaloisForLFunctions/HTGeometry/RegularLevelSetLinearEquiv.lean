import GaloisForLFunctions.HTGeometry.RegularLevelSetHausdorffDimension

/-!
# Transport of regular stratifications by linear equivalences

Finite regular stratifications and their codimension bounds are invariant under continuous real
linear coordinate changes.  This is the transport layer used to pass between arbitrary finite
coordinate types and canonical `Fin` coordinates.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem IsLocalRegularLevelSetOfCodimAtLeast.image_continuousLinearEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {c : ℕ}
    (hS : IsLocalRegularLevelSetOfCodimAtLeast S c)
    (e : E ≃L[ℝ] F) :
    IsLocalRegularLevelSetOfCodimAtLeast (e '' S) c := by
  intro y hy
  obtain ⟨x, hxS, rfl⟩ := hy
  obtain ⟨m, hcm, U, hUopen, hxU, g, hg, hzero, hsurjWithin⟩ := hS x hxS
  let V : Set F := e '' U
  let g' : F → (Fin m → ℝ) := fun y ↦ g (e.symm y)
  have hVopen : IsOpen V := e.isOpenMap U hUopen
  have hexU : e x ∈ V := ⟨x, hxU, rfl⟩
  have hg' : ContDiffOn ℝ ⊤ g' V := by
    exact hg.comp (e.symm.contDiff.contDiffOn) (fun _ hy ↦ by
      obtain ⟨z, hzU, rfl⟩ := hy
      simpa using hzU)
  have hzero' : ∀ y ∈ V, y ∈ e '' S ↔ g' y = 0 := by
    intro y hyV
    obtain ⟨z, hzU, rfl⟩ := hyV
    simp only [g', e.symm_apply_apply]
    constructor
    · rintro ⟨w, hwS, hwe⟩
      have hwz : w = z := e.injective hwe
      exact (hzero z hzU).mp (hwz ▸ hwS)
    · intro hgz
      exact ⟨z, (hzero z hzU).mpr hgz, rfl⟩
  have hsurj' : ∀ y ∈ V, Function.Surjective (fderivWithin ℝ g' V y) := by
    intro y hyV
    obtain ⟨z, hzU, rfl⟩ := hyV
    have hgAt : ContDiffAt ℝ ⊤ g z :=
      (hg z hzU).contDiffAt (hUopen.mem_nhds hzU)
    have hgAt' : DifferentiableAt ℝ g (e.symm (e z)) := by
      simpa using hgAt.differentiableAt (by simp)
    have hcomp : fderiv ℝ g' (e z) =
        (fderiv ℝ g z).comp e.symm.toContinuousLinearMap := by
      calc
        fderiv ℝ g' (e z) = (fderiv ℝ g z).comp (fderiv ℝ e.symm (e z)) := by
          simpa only [g', e.symm_apply_apply] using
            (fderiv_comp' (f := e.symm) (g := g) (e z)
              hgAt' (e.symm.differentiableAt))
        _ = (fderiv ℝ g z).comp e.symm.toContinuousLinearMap := by
          rw [e.symm.fderiv]
    rw [fderivWithin_of_isOpen hVopen ⟨z, hzU, rfl⟩, hcomp]
    have hsurjG : Function.Surjective (fderiv ℝ g z) := by
      simpa only [fderivWithin_of_isOpen hUopen hzU] using hsurjWithin z hzU
    exact hsurjG.comp e.symm.surjective
  exact ⟨m, hcm, V, hVopen, hexU, g', hg', hzero', hsurj'⟩

noncomputable def FiniteRegularStratification.image_continuousLinearEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {c : ℕ}
    (hS : FiniteRegularStratification S c)
    (e : E ≃L[ℝ] F) :
    FiniteRegularStratification (e '' S) c where
  numberOfStrata := hS.numberOfStrata
  stratum i := e '' hS.stratum i
  pairwise_disjoint := by
    intro i _ j _ hij
    change Disjoint (e '' hS.stratum i) (e '' hS.stratum j)
    rw [Set.disjoint_left]
    rintro y ⟨x, hxi, rfl⟩ ⟨z, hzj, hzeq⟩
    have hxz : x = z := e.injective hzeq.symm
    exact Set.disjoint_left.mp
      (hS.pairwise_disjoint (mem_univ i) (mem_univ j) hij) hxi (hxz ▸ hzj)
  cover := by
    ext y
    constructor
    · rintro ⟨x, hxS, rfl⟩
      have hxUnion : x ∈ ⋃ i, hS.stratum i := by
        rw [← hS.cover]
        exact hxS
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxUnion
      exact mem_iUnion.mpr ⟨i, x, hxi, rfl⟩
    · intro hy
      obtain ⟨i, x, hxi, rfl⟩ := mem_iUnion.mp hy
      refine ⟨x, ?_, rfl⟩
      rw [hS.cover]
      exact mem_iUnion.mpr ⟨i, hxi⟩
  regular i := (hS.regular i).image_continuousLinearEquiv e

end

end GaloisForLFunctions.HTGeometry
