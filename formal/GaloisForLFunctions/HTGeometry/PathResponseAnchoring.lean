import GaloisForLFunctions.HTGeometry.PathLaplacianRootedCofactor
import GaloisForLFunctions.HilbertMetric.ResponseCompression

/-!
# Endogenous anchors on the existing path Laplacian

Araújo, arXiv:2609.05560, Theorem 2 separates translation from disagreement.
Here that reduction is applied to the corpus's path incidence matrix and weighted Hodge
Laplacian. Every displayed identity is global for the specified linear vector field.
-/

open Matrix
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric
noncomputable section

/-- Incidence annihilates every common displacement. -/
theorem pathDifferential_common_constant (n : ℕ) (b : ℝ) :
    pathDifferential ℝ n *ᵥ (fun _ => b) = 0 := by
  funext j
  simp [pathDifferential_mulVec]

/-- The path Laplacian annihilates the translation sector. -/
theorem pathLaplacian_common_constant (n : ℕ) (a b : ℝ) :
    pathLaplacian ℝ a n *ᵥ (fun _ => b) = 0 := by
  rw [pathLaplacian, smul_mulVec, ← mulVec_mulVec,
    pathDifferential_common_constant, mulVec_zero, smul_zero]

/-- Internal path forces have zero total force, for either sign of conductance. -/
theorem sum_pathLaplacian_mulVec (n : ℕ) (a : ℝ) (x : Fin (n + 1) → ℝ) :
    ∑ i, (pathLaplacian ℝ a n *ᵥ x) i = 0 := by
  have hz : (fun _ : Fin (n + 1) => (1 : ℝ)) ⬝ᵥ
      (((pathDifferential ℝ n)ᵀ * pathDifferential ℝ n) *ᵥ x) = 0 := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
      pathDifferential_common_constant, zero_dotProduct]
  rw [pathLaplacian, smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  simpa only [dotProduct, one_mul, mul_zero] using congrArg (a * ·) hz

/-- Centering the input does not change the internal path forces. -/
theorem pathLaplacian_centered (n : ℕ) (a : ℝ) (x : Fin (n + 1) → ℝ) :
    pathLaplacian ℝ a n *ᵥ (fun i => x i - hilbertCentroid x) =
      pathLaplacian ℝ a n *ᵥ x := by
  change pathLaplacian ℝ a n *ᵥ (x - fun _ => hilbertCentroid x) = _
  rw [mulVec_sub, pathLaplacian_common_constant, sub_zero]

/-- The shared represented mean acts as an endogenous anchor on a path. -/
def pathResponseVelocity {n : ℕ} (a lam b : ℝ) (x : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => -(1 - lam) * (pathLaplacian ℝ a n *ᵥ x) i + lam * (b - x i)

/-- The exact mean equation does not depend on the path conductance. -/
theorem hilbertCentroid_pathResponseVelocity (n : ℕ) (a lam b : ℝ)
    (x : Fin (n + 1) → ℝ) :
    hilbertCentroid (pathResponseVelocity a lam b x) = lam * (b - hilbertCentroid x) := by
  have hn : (Fintype.card (Fin (n + 1)) : ℝ) ≠ 0 := by positivity
  simp only [hilbertCentroid, pathResponseVelocity, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, sum_pathLaplacian_mulVec,
    mul_zero, zero_add, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Centered path evolution is independent of the represented mean. -/
theorem pathResponseVelocity_centered (n : ℕ) (a lam b : ℝ)
    (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    pathResponseVelocity a lam b x i - hilbertCentroid (pathResponseVelocity a lam b x) =
      -(1 - lam) *
        (pathLaplacian ℝ a n *ᵥ (fun j => x j - hilbertCentroid x)) i -
          lam * (x i - hilbertCentroid x) := by
  rw [hilbertCentroid_pathResponseVelocity, pathLaplacian_centered]
  unfold pathResponseVelocity
  ring

/-- Every edge sees the same homogeneous anchoring, whatever the shared summary. -/
theorem pathDifferential_responseVelocity (n : ℕ) (a lam b : ℝ)
    (x : Fin (n + 1) → ℝ) (j : Fin n) :
    (pathDifferential ℝ n *ᵥ pathResponseVelocity a lam b x) j =
      -(1 - lam) * (pathDifferential ℝ n *ᵥ (pathLaplacian ℝ a n *ᵥ x)) j -
        lam * (pathDifferential ℝ n *ᵥ x) j := by
  simp only [pathDifferential_mulVec, pathResponseVelocity]
  ring

/-- Prevalence changes are pure translation even on a non-complete interaction graph. -/
theorem pathResponseVelocity_anchor_difference (n : ℕ) (a lam b d : ℝ)
    (x : Fin (n + 1) → ℝ) :
    (fun i => pathResponseVelocity a lam b x i - pathResponseVelocity a lam d x i) =
      (fun _ => lam * (b - d)) := by
  funext i
  unfold pathResponseVelocity
  ring

/-- The response reduction transports through the corpus's rooted path integrator. -/
theorem pathResponseVelocity_recovered_edges (n : ℕ) (a lam b : ℝ)
    (r : Fin (n + 1)) (g : Fin n → ℝ) (j : Fin n) :
    (pathDifferential ℝ n *ᵥ pathResponseVelocity a lam b (pathPotential ℝ r g)) j =
      -(1 - lam) *
        (pathDifferential ℝ n *ᵥ (pathLaplacian ℝ a n *ᵥ pathPotential ℝ r g)) j -
          lam * g j := by
  rw [pathDifferential_responseVelocity, pathDifferential_mulVec_pathPotential]

end
end GaloisForLFunctions.HTGeometry
