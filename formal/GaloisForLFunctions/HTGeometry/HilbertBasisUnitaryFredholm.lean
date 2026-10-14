import GaloisForLFunctions.HTGeometry.FiniteSupportOperatorFredholm
import GaloisForLFunctions.RHTower.ApproximationNumberUnitary

/-! # Actual Fredholm determinants under a unitary change of Hilbert coordinates -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : Type*}

def unitaryHilbertBasis (b : HilbertBasis ι ℂ H) (u : H ≃ₗᵢ[ℂ] K) : HilbertBasis ι ℂ K :=
  HilbertBasis.ofRepr (u.symm.trans b.repr)

@[simp] theorem unitaryHilbertBasis_apply (b : HilbertBasis ι ℂ H)
    (u : H ≃ₗᵢ[ℂ] K) (i : ι) : unitaryHilbertBasis b u i = u (b i) := rfl

theorem memSchattenClass_unitaryPush_iff (p : ℝ) (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    RHTower.MemSchattenClass p (RHTower.unitaryPush u T) ↔ RHTower.MemSchattenClass p T := by
  simp only [RHTower.MemSchattenClass, RHTower.approxNumber_unitaryPush]

variable [DecidableEq ι]

theorem coordMatrix_unitaryHilbertBasis (b : HilbertBasis ι ℂ H)
    (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    RHTower.coordMatrix (unitaryHilbertBasis b u) (RHTower.unitaryPush u T) =
      RHTower.coordMatrix b T := by
  funext p
  simp only [RHTower.coordMatrix_apply, unitaryHilbertBasis_apply, RHTower.unitaryPush_apply,
    u.symm_apply_apply, u.inner_map_map]

variable [CompleteSpace H] [CompleteSpace K]

theorem opTrace_unitaryPush (b : HilbertBasis ι ℂ H) (u : H ≃ₗᵢ[ℂ] K)
    {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T) :
    ContinuousLinearMap.opTrace (RHTower.unitaryPush u T) = ContinuousLinearMap.opTrace T := by
  have hU := (memSchattenClass_unitaryPush_iff 1 u T).mpr hT
  rw [opTrace_eq_hsTraceDiag_coordMatrix (unitaryHilbertBasis b u) hU,
    opTrace_eq_hsTraceDiag_coordMatrix b hT, coordMatrix_unitaryHilbertBasis]

theorem fredholmDetOp_unitaryPush (b : HilbertBasis ι ℂ H) (u : H ≃ₗᵢ[ℂ] K)
    {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T) :
    RHTower.fredholmDetOp (unitaryHilbertBasis b u) (RHTower.unitaryPush u T) =
      RHTower.fredholmDetOp b T := by
  rw [RHTower.fredholmDetOp, RHTower.fredholmDetOp, RHTower.det2Op, RHTower.det2Op,
    coordMatrix_unitaryHilbertBasis, opTrace_unitaryPush b u hT]

end
end GaloisForLFunctions.HTGeometry
