import GaloisForLFunctions.RHTower.ProlateEvenEigenspaceQuadratic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The band operator diagonalizes the unit-band `L²` space

The Slepian band operator is compact and symmetric, so mathlib's spectral theorem for compact
self-adjoint operators makes the span of its eigenspaces dense.  Together with the orthogonality of
the eigenspaces this exhibits `L²[-1,1]` as their Hilbert sum, and every vector as the unconditional
sum of its eigencomponents.
-/

noncomputable section

open MeasureTheory

namespace RHTower

/-- The band operator is a symmetric endomorphism of the unit-band `L²` space. -/
theorem isSymmetric_bandOperatorL2 (c : ℝ) :
    ((GaloisForLFunctions.RHTower.bandOperatorL2 c :
      GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
        GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
      Module.End ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)).IsSymmetric :=
  fun x y => GaloisForLFunctions.RHTower.bandOperatorL2_symmetric c x y

/-- The corpus band eigenspace is the operator's eigenspace. -/
theorem bandEigenspace_eq_eigenspace (c lam : ℝ) :
    GaloisForLFunctions.RHTower.bandEigenspace c lam
      = Module.End.eigenspace
          ((GaloisForLFunctions.RHTower.bandOperatorL2 c :
            GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
              GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
            Module.End ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)) lam := by
  ext f
  rw [GaloisForLFunctions.RHTower.mem_bandEigenspace_iff, Module.End.mem_eigenspace_iff]
  exact Iff.rfl

/-- The operator eigenspaces of the band operator are complete. -/
theorem completeSpace_bandOperator_eigenspace (c lam : ℝ) :
    CompleteSpace (Module.End.eigenspace
      ((GaloisForLFunctions.RHTower.bandOperatorL2 c :
        GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
          GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
        Module.End ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)) lam) := by
  rw [← bandEigenspace_eq_eigenspace]
  exact GaloisForLFunctions.RHTower.completeSpace_bandEigenspace c lam

/-- **The eigenspaces of the band operator span a dense subspace.** -/
theorem bandEigenspaces_topologicalClosure (c : ℝ) :
    (⊤ : Submodule ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1))
      ≤ (⨆ μ : ℝ, Module.End.eigenspace
          ((GaloisForLFunctions.RHTower.bandOperatorL2 c :
            GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
              GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
            Module.End ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1))
          μ).topologicalClosure := by
  have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (GaloisForLFunctions.RHTower.isCompactOperator_bandOperatorL2 c)
    (isSymmetric_bandOperatorL2 c)
  exact (Submodule.topologicalClosure_eq_top_iff.mpr hbot).ge

/-- **The unit-band `L²` space is the Hilbert sum of the band eigenspaces.** -/
theorem isHilbertSum_bandEigenspaces (c : ℝ) :
    IsHilbertSum ℝ
      (fun μ : ℝ => (Module.End.eigenspace
        ((GaloisForLFunctions.RHTower.bandOperatorL2 c :
          GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
            GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
          Module.End ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)) μ :
        Submodule ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)))
      (fun μ : ℝ => (Module.End.eigenspace
        ((GaloisForLFunctions.RHTower.bandOperatorL2 c :
          GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
            GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
          Module.End ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)) μ).subtypeₗᵢ) := by
  haveI : ∀ μ : ℝ, CompleteSpace (Module.End.eigenspace
      ((GaloisForLFunctions.RHTower.bandOperatorL2 c :
        GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
          GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
        Module.End ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)) μ) :=
    fun μ => completeSpace_bandOperator_eigenspace c μ
  exact IsHilbertSum.mkInternal _
    ((isSymmetric_bandOperatorL2 c).orthogonalFamily_eigenspaces)
    (bandEigenspaces_topologicalClosure c)

/-- The `μ`-eigencomponent of a vector of the unit-band `L²` space. -/
def bandComponent (c : ℝ) (v : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) (μ : ℝ) :
    GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 :=
  (((isHilbertSum_bandEigenspaces c).linearIsometryEquiv v μ :
    Module.End.eigenspace
      ((GaloisForLFunctions.RHTower.bandOperatorL2 c :
        GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
          GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
        Module.End ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)) μ) :
    GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)

theorem bandComponent_mem (c : ℝ) (v : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
    (μ : ℝ) : bandComponent c v μ ∈ GaloisForLFunctions.RHTower.bandEigenspace c μ := by
  rw [bandEigenspace_eq_eigenspace]
  exact ((isHilbertSum_bandEigenspaces c).linearIsometryEquiv v μ).2

/-- **The eigencomponents sum to the vector.** -/
theorem hasSum_bandComponent (c : ℝ)
    (v : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
    HasSum (bandComponent c v) v := by
  have h := (isHilbertSum_bandEigenspaces c).hasSum_linearIsometryEquiv_symm
    ((isHilbertSum_bandEigenspaces c).linearIsometryEquiv v)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h

/-- Distinct eigencomponents are orthogonal to each eigenspace. -/
theorem inner_bandComponent_eq_zero (c : ℝ)
    (v w : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) {μ ν : ℝ} (hνμ : ν ≠ μ)
    (hw : w ∈ GaloisForLFunctions.RHTower.bandEigenspace c μ) :
    (inner ℝ (bandComponent c v ν) w : ℝ) = 0 := by
  have hfam := (isSymmetric_bandOperatorL2 c).orthogonalFamily_eigenspaces
  have hmem : bandComponent c v ν ∈ Module.End.eigenspace
      ((GaloisForLFunctions.RHTower.bandOperatorL2 c :
        GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
          GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
        Module.End ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)) ν := by
    rw [← bandEigenspace_eq_eigenspace]
    exact bandComponent_mem c v ν
  have hwmem : w ∈ Module.End.eigenspace
      ((GaloisForLFunctions.RHTower.bandOperatorL2 c :
        GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
          GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
        Module.End ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)) μ := by
    rw [← bandEigenspace_eq_eigenspace]
    exact hw
  exact hfam hνμ ⟨bandComponent c v ν, hmem⟩ ⟨w, hwmem⟩

/-- **The eigencomponent is the orthogonal projection.**  Pairing a vector against any element of
the `μ`-eigenspace only sees its `μ`-component. -/
theorem inner_eq_inner_bandComponent (c : ℝ)
    (v w : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) {μ : ℝ}
    (hw : w ∈ GaloisForLFunctions.RHTower.bandEigenspace c μ) :
    (inner ℝ v w : ℝ) = (inner ℝ (bandComponent c v μ) w : ℝ) := by
  classical
  have h0 : HasSum (fun ν : ℝ => (inner ℝ w (bandComponent c v ν) : ℝ)) (inner ℝ w v : ℝ) :=
    ContinuousLinearMap.hasSum (innerSL ℝ w) (hasSum_bandComponent c v)
  have h1 : HasSum (fun ν : ℝ => (inner ℝ (bandComponent c v ν) w : ℝ)) (inner ℝ v w : ℝ) := by
    have hfun : (fun ν : ℝ => (inner ℝ (bandComponent c v ν) w : ℝ))
        = fun ν : ℝ => (inner ℝ w (bandComponent c v ν) : ℝ) :=
      funext fun ν => real_inner_comm _ _
    rw [hfun, show (inner ℝ v w : ℝ) = (inner ℝ w v : ℝ) from real_inner_comm w v]
    exact h0
  have h3 : (fun ν : ℝ => (inner ℝ (bandComponent c v ν) w : ℝ))
      = fun ν : ℝ => if ν = μ then (inner ℝ (bandComponent c v μ) w : ℝ) else 0 := by
    funext ν
    by_cases hν : ν = μ
    · subst hν
      simp
    · simp [hν, inner_bandComponent_eq_zero c v w hν hw]
  rw [h3] at h1
  exact h1.unique (hasSum_ite_eq μ _)

/-- Pairing a vector against its own eigencomponent returns that component's squared norm. -/
theorem inner_self_bandComponent (c : ℝ)
    (v : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) (μ : ℝ) :
    (inner ℝ v (bandComponent c v μ) : ℝ) = ‖bandComponent c v μ‖ ^ 2 := by
  have h := inner_eq_inner_bandComponent c v (bandComponent c v μ) (bandComponent_mem c v μ)
  rw [h, real_inner_self_eq_norm_sq]

end RHTower
