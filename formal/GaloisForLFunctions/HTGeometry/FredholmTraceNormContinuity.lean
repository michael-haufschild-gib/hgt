import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitSelection
import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtContinuity
import GaloisForLFunctions.RHTower.MertensClockRelativeDeterminant

/-! # Continuity of the actual operator Fredholm determinant in trace norm

The established Schatten-one to Hilbert--Schmidt bound controls the coordinate
kernel. Entire determinant continuity and continuity of the actual operator
trace then give the ordinary Fredholm limit.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap _root_.RHTower HilbertSchmidt Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [DecidableEq ι]

theorem tendsto_fredholmDetOp_of_traceNorm_tendsto (b : HilbertBasis ι ℂ H)
    (A : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hA : ∀ n, MemSchattenClass 1 (A n)) (hT : MemSchattenClass 1 T)
    (ht : Tendsto (fun n => traceNorm H (A n - T)) atTop (𝓝 0)) :
    Tendsto (fun n => fredholmDetOp b (A n)) atTop (𝓝 (fredholmDetOp b T)) := by
  have hdiff (n : ℕ) := (hA n).one_sub hT
  have hcoord (n : ℕ) : coordMatrix b (A n) - coordMatrix b T = coordMatrix b (A n - T) := by
    funext p
    simp only [Pi.sub_apply, coordMatrix_apply, sub_apply, inner_sub_right]
  have hnorm (n : ℕ) : HilbertSchmidt.hsNorm (coordMatrix b (A n) - coordMatrix b T) ≤
      traceNorm H (A n - T) := by
    rw [hcoord]
    change Real.sqrt (HilbertSchmidt.hsNormSq (coordMatrix b (A n - T))) ≤ _
    calc
      _ ≤ Real.sqrt (ContinuousLinearMap.hsNormSq (A n - T)) :=
        Real.sqrt_le_sqrt (hsNormSq_coordMatrix_le b (hdiff n).one_isHilbertSchmidt)
      _ ≤ Real.sqrt (traceNorm H (A n - T) ^ 2) :=
        Real.sqrt_le_sqrt (hsNormSq_le_traceNorm_sq (hdiff n))
      _ = traceNorm H (A n - T) := Real.sqrt_sq (traceNorm_nonneg _)
  have hdet := tendsto_entireDet2_of_hsNorm_sub_tendsto_zero
    (fun n => coordMatrix b (A n)) (coordMatrix b T)
    (fun n => isHS_coordMatrix b (hA n).one_isHilbertSchmidt)
    (isHS_coordMatrix b hT.one_isHilbertSchmidt)
    (squeeze_zero (fun _ => Real.sqrt_nonneg _) hnorm ht) (-1)
  have htrace := opTrace_tendsto_of_traceNorm_tendsto hA hdiff ht
  exact hdet.mul (Complex.continuous_exp.continuousAt.tendsto.comp htrace)

end
end GaloisForLFunctions.HTGeometry
