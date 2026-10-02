import GaloisForLFunctions.RHTower.CCMEulerBoundarySpectralChart

/-!
# The shell lost by actual Euler boundary transitions

The source chart identifies the whole transition kernel with the Fourier shell
between `max b P_S` and `P_T`. This identification includes both endpoint
chambers and retains the actual source-defined chart.
-/

noncomputable section

open IsDedekindDomain

namespace RHTower

private def restrictAmbientEquiv
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℂ F]
    (V : Submodule ℂ F) (e : E ≃L[ℂ] V) (p : Submodule ℂ E) (q : Submodule ℂ F)
    (hq : q ≤ V) (h : ∀ x : E, x ∈ p ↔ (e x : F) ∈ q) : p ≃L[ℂ] q where
  toFun x := ⟨e x, (h x).mp x.property⟩
  invFun y := ⟨e.symm ⟨y, hq y.property⟩, (h _).mpr (by
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact y.property)⟩
  map_add' x y := Subtype.ext (congrArg (fun v : V => (v : F)) (map_add e (x : E) (y : E)))
  map_smul' c x := Subtype.ext (congrArg (fun v : V => (v : F)) (map_smul e c (x : E)))
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (congrArg (fun v : V => (v : F)) (e.apply_symm_apply ⟨y, hq y.property⟩))
  continuous_toFun := (V.subtypeL.continuous.comp (e.continuous.comp p.subtypeL.continuous)).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp (q.subtypeL.continuous.subtype_mk _)).subtype_mk _
private theorem restrictAmbientEquiv_apply
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℂ F]
    (V : Submodule ℂ F) (e : E ≃L[ℂ] V) (p : Submodule ℂ E) (q : Submodule ℂ F)
    (hq : q ≤ V) (h : ∀ x : E, x ∈ p ↔ (e x : F) ∈ q) (x : p) :
    (restrictAmbientEquiv V e p q hq h x : F) = (e x : F) := rfl


private theorem cutoff_zero_of_le {s t : ℝ} (hst : s ≤ t) {u : evenSubspace}
    (hu : evenFourierCutoff t u = 0) : evenFourierCutoff s u = 0 := by
  calc
    evenFourierCutoff s u = evenFourierCutoff s (evenFourierCutoff t u) :=
      (DFunLike.congr_fun (evenFourierCutoff_mul_of_le s t hst) u).symm
    _ = 0 := by rw [hu, map_zero]

/-- A transition vanishes exactly when its actual spectral chart lies in the lost shell. -/
theorem ccmEulerBoundaryTransition_mem_kernel_iff_shell
    (S T : Finset (HeightOneSpectrum ℤ)) (hST : S ⊆ T) (b : ℝ) (hb : 0 < b)
    (y : ccmEulerBoundaryAnnulus T b 1) :
    y ∈ (ccmEulerBoundaryTransition S T hST b hb).ker ↔
      (ccmEulerBoundarySpectralEquiv T b hb y : evenSubspace) ∈
        ccmEulerBoundaryAnnulus ∅ (max b (ccmFiniteEulerCarrierScale S))
          (ccmFiniteEulerCarrierScale T) := by
  change ccmEulerBoundaryTransition S T hST b hb y = 0 ↔ _
  rw [ccmEulerBoundaryTransition_eq_zero_iff, mem_ccmEulerBoundaryAnnulus_empty_iff]
  have hv := (mem_ccmEulerBoundaryAnnulus_empty_iff b (ccmFiniteEulerCarrierScale T)
    (ccmEulerBoundarySpectralEquiv T b hb y : evenSubspace)).mp
      (ccmEulerBoundarySpectralEquiv T b hb y).property
  constructor
  · intro hy
    refine ⟨?_, hv.2⟩
    rcases le_total b (ccmFiniteEulerCarrierScale S) with h | h
    · simpa only [max_eq_right h] using hy
    · simpa only [max_eq_left h] using hv.1
  · intro hy
    exact cutoff_zero_of_le (le_max_right _ _) hy.1

/-- The exact bounded kernel-shell equivalence forced by the original source maps. -/
def ccmEulerBoundaryKernelShellEquiv (S T : Finset (HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (b : ℝ) (hb : 0 < b) :
    (ccmEulerBoundaryTransition S T hST b hb).ker ≃L[ℂ]
      ccmEulerBoundaryAnnulus ∅ (max b (ccmFiniteEulerCarrierScale S))
        (ccmFiniteEulerCarrierScale T) :=
  restrictAmbientEquiv (ccmEulerBoundaryAnnulus ∅ b (ccmFiniteEulerCarrierScale T))
    (ccmEulerBoundarySpectralEquiv T b hb) (ccmEulerBoundaryTransition S T hST b hb).ker
    (ccmEulerBoundaryAnnulus ∅ (max b (ccmFiniteEulerCarrierScale S))
      (ccmFiniteEulerCarrierScale T))
    (fun u hu => by
      have h := (mem_ccmEulerBoundaryAnnulus_empty_iff _ _ u).mp hu
      exact (mem_ccmEulerBoundaryAnnulus_empty_iff _ _ u).mpr
        ⟨cutoff_zero_of_le (le_max_left _ _) h.1, h.2⟩)
    (ccmEulerBoundaryTransition_mem_kernel_iff_shell S T hST b hb)

theorem ccmEulerBoundaryKernelShellEquiv_apply (S T : Finset (HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (b : ℝ) (hb : 0 < b)
    (y : (ccmEulerBoundaryTransition S T hST b hb).ker) :
    (ccmEulerBoundaryKernelShellEquiv S T hST b hb y : evenSubspace) =
      (ccmEulerBoundarySpectralEquiv T b hb y : evenSubspace) :=
  restrictAmbientEquiv_apply _ _ _ _ _ _ y

end RHTower
