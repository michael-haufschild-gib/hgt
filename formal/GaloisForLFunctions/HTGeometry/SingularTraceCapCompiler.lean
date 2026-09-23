import GaloisForLFunctions.HTGeometry.GaussianStableRankTraceCapCompiler
import Mathlib.Analysis.InnerProductSpace.Trace

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem sum_sq_singularValues_eq_sum_norm_orthonormalBasis
    {n : ℕ} {I E F : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (hn : Module.finrank ℝ E = n)
    (b : OrthonormalBasis I ℝ E) :
    (∑ i : Fin n, A.singularValues i ^ (2 : ℕ)) =
      ∑ i : I, ‖A (b i)‖ ^ (2 : ℕ) := by
  simp_rw [A.sq_singularValues_fin hn]
  rw [← A.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues hn]
  rw [LinearMap.trace_eq_sum_inner (A.adjoint ∘ₗ A) b]
  change (∑ i, inner ℝ (b i) ((A.adjoint ∘ₗ A) (b i))) = _
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.re_to_real, LinearMap.comp_apply,
    LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem singularValue_sq_le_of_norm_sq_le
    {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (hn : Module.finrank ℝ E = n)
    {cap : ℝ} (hcap : ∀ v, ‖A v‖ ^ (2 : ℕ) ≤ cap * ‖v‖ ^ (2 : ℕ))
    (i : Fin n) :
    A.singularValues i ^ (2 : ℕ) ≤ cap := by
  rw [A.sq_singularValues_fin hn]
  let b := A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  have heigen :=
    A.isSymmetric_adjoint_comp_self.hasEigenvector_eigenvectorBasis hn i
  have hnorm : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  calc
    A.isSymmetric_adjoint_comp_self.eigenvalues hn i =
        inner ℝ (b i) ((A.adjoint ∘ₗ A) (b i)) := by
      rw [heigen.apply_eq_smul, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hnorm]
      simp
    _ = ‖A (b i)‖ ^ (2 : ℕ) := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
        real_inner_self_eq_norm_sq]
    _ ≤ cap * ‖b i‖ ^ (2 : ℕ) := hcap (b i)
    _ = cap := by rw [hnorm]; ring

/-- Basis-trace/operator-cap compiler for genuine Gram stable rank. -/
theorem singularStableRatio_ge_of_basis_trace_norm_cap
    {n : ℕ} {I E F : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (hn : Module.finrank ℝ E = n)
    (b : OrthonormalBasis I ℝ E)
    {mass cap : ℝ} (hmassPos : 0 < mass) (hcapPos : 0 < cap)
    (hmass : mass ≤ ∑ i : I, ‖A (b i)‖ ^ (2 : ℕ))
    (hcap : ∀ v, ‖A v‖ ^ (2 : ℕ) ≤ cap * ‖v‖ ^ (2 : ℕ)) :
    mass / cap ≤
      (∑ i : Fin n, A.singularValues i ^ (2 : ℕ)) ^ (2 : ℕ) /
        ∑ i : Fin n, A.singularValues i ^ (4 : ℕ) := by
  have htrace : mass ≤ ∑ i : Fin n, A.singularValues i ^ (2 : ℕ) := by
    rw [sum_sq_singularValues_eq_sum_norm_orthonormalBasis A hn b]
    exact hmass
  have hsvCap : ∀ i : Fin n, A.singularValues i ^ (2 : ℕ) ≤ cap :=
    singularValue_sq_le_of_norm_sq_le A hn hcap
  have hpow : ∀ i : Fin n, (A.singularValues i ^ (2 : ℕ)) ^ (2 : ℕ) =
      A.singularValues i ^ (4 : ℕ) := fun i => by ring
  simpa only [hpow] using weightedStableRatio_ge_mass_div_cap
    (fun i : Fin n => A.singularValues i ^ (2 : ℕ))
    (fun i => sq_nonneg _) hmassPos hcapPos htrace hsvCap

end

end GaloisForLFunctions.HTGeometry
