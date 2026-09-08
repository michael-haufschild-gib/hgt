import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMClassicalGreen
import GaloisForLFunctions.HTGeometry.ComplexC2Laplacian

/-!
The actual planar Laplacian transforms by the squared complex derivative under a holomorphic chart change. The full second chain rule cancels the harmonic coordinate terms.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- The full real Laplacian transforms by the squared complex derivative under a holomorphic chart. -/
theorem planarLaplacian_holomorphic_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f (g z)) (hg : ContDiffAt ℂ 2 g z) :
    planarLaplacian (f ∘ g) z = (Complex.normSq (deriv g z) : ℂ)*planarLaplacian f (g z) := by
  simpa only [planarLaplacian, Fin.sum_univ_two, direction, Matrix.cons_val_zero,
    Matrix.cons_val_one, ComplexC2Laplacian.laplacian] using
    ComplexC2Laplacian.laplacian_holomorphic_comp hf hg

end
end RHTower.D4BMModularCore
