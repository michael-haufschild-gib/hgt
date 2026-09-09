import GaloisForLFunctions.HTGeometry.EuclideanSobolevLaplacianGain
import GaloisForLFunctions.HTGeometry.L2DerivativeFourier

/-! A real-line distribution gains one Sobolev order from its actual first derivative. -/
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The real-line distributional Laplacian is the second derivative in the original unit direction. -/
theorem real_distribution_laplacian (u : 𝓢'(ℝ,ℂ)) :
    Δ u = ∂_{(1:ℝ)} (∂_{(1:ℝ)} u) := by
  ext ψ
  simp only [TemperedDistribution.laplacian_apply_apply,TemperedDistribution.lineDerivOp_apply_apply,
    LineDeriv.lineDerivOp_neg,neg_neg]
  congr 1
  ext x
  simp only [SchwartzMap.laplacian_apply,InnerProductSpace.laplacian_eq_iteratedDeriv_real,
    iteratedDeriv_succ,iteratedDeriv_zero,schwartz_lineDerivOp_one]
  have he : ((∂_{(1:ℝ)} ψ : 𝓢(ℝ,ℂ)) : ℝ → ℂ) = deriv (⇑ψ) := funext (schwartz_lineDerivOp_one ψ)
  rw [he]

/-- An admitted first derivative supplies one Sobolev order for the same original distribution. -/
theorem real_sobolev_gain_one {s : ℝ} {u : 𝓢'(ℝ,ℂ)}
    (hu : MemSobolev s 2 u) (hd : MemSobolev s 2 (∂_{(1:ℝ)} u)) :
    MemSobolev (s+1) 2 u := by
  have hu' : MemSobolev (s-1) 2 u := hu.mono (by linarith)
  have hd' : MemSobolev (s-1) 2 (Δ u) := by
    rw [real_distribution_laplacian]
    exact hd.lineDerivOp
  have he : s-1+2 = s+1 := by ring
  simpa only [he] using euclidean_sobolev_gain_two hu' hd'

end
end GaloisForLFunctions.HTGeometry
