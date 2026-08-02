import GaloisForLFunctions.HTGeometry.FiniteShadowCapacity
import GaloisForLFunctions.HTGeometry.MultivariateMultiIndexJet
import Mathlib.Topology.Instances.Matrix

/-!
# Finite-jet block peeling for quasi-Abelian Poincare series

The all-order extension of Abe's point-separation induction has a finite-dimensional algebraic
core.  Old packet columns give an invertible block `A`; normalized new columns tend to an
invertible target block `D` and to zero on the old packet.  The remaining block is irrelevant.
Continuity of the determinant therefore makes the full evaluation matrix invertible for a finite
damping parameter.

This file proves that core without an analytic surrogate.  Its hypotheses are literal convergence
of the actual evaluation matrices.  Later Poincare-series estimates have only to produce that
convergence.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A matrix family converging to a block-lower-triangular matrix with invertible diagonal blocks
is eventually invertible.  This is the exact determinant perturbation used when one local Artin
jet block is appended in the quasi-Abelian subgroup-rank induction. -/
theorem eventually_det_ne_zero_of_tendsto_fromBlocks_zero₁₂
    {K T ι κ : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {l : Filter T} (M : T → Matrix (ι ⊕ κ) (ι ⊕ κ) K)
    (A : Matrix ι ι K) (B : Matrix κ ι K) (D : Matrix κ κ K)
    (hM : Tendsto M l (nhds (Matrix.fromBlocks A 0 B D)))
    (hA : A.det ≠ 0) (hD : D.det ≠ 0) :
    ∀ᶠ t in l, (M t).det ≠ 0 := by
  have hdet : (Matrix.fromBlocks A 0 B D).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    exact mul_ne_zero hA hD
  have ht : Tendsto (fun t => (M t).det) l
      (nhds (Matrix.fromBlocks A 0 B D).det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp hM
  exact ht.eventually (eventually_ne_nhds hdet)

/-- If finitely many source vectors have an invertible evaluation matrix, the evaluation linear
map is surjective.  The proof constructs a preimage using the surjective matrix action, rather
than using a dimension count on the possibly infinite-dimensional source. -/
theorem linearMap_surjective_of_evaluationMatrix_det_ne_zero
    {K S ι : Type*} [Field K] [AddCommGroup S] [Module K S]
    [Fintype ι] [DecidableEq ι]
    (ev : S →ₗ[K] (ι → K)) (sections : ι → S)
    (hdet : (Matrix.of fun i j => ev (sections j) i).det ≠ 0) :
    Function.Surjective ev := by
  let M : Matrix ι ι K := Matrix.of fun i j => ev (sections j) i
  have hunit : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  intro y
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit y
  refine ⟨∑ j, c j • sections j, ?_⟩
  funext i
  rw [map_sum]
  simp only [LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simpa [M, Matrix.mulVec, dotProduct, mul_comm] using congrFun hc i

/-- **Finite local-Artin block peeling.**  Suppose actual source sections have evaluation matrices
which converge to the block matrix produced by an already interpolated packet and one normalized
new jet block.  If both diagonal blocks are invertible, the full evaluation map is surjective.

`NeBot l` expresses that the damping regime is nonempty (for Abe's construction it is `atTop`).
No finite-dimensionality is assumed for the section space. -/
theorem finiteJetPacketPeeling_surjective
    {K S T ι κ : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] [AddCommGroup S] [Module K S]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {l : Filter T} [NeBot l]
    (ev : S →ₗ[K] ((ι ⊕ κ) → K))
    (sections : T → (ι ⊕ κ) → S)
    (A : Matrix ι ι K) (B : Matrix κ ι K) (D : Matrix κ κ K)
    (hsections : Tendsto
      (fun t => Matrix.of fun i j => ev (sections t j) i) l
      (nhds (Matrix.fromBlocks A 0 B D)))
    (hA : A.det ≠ 0) (hD : D.det ≠ 0) :
    Function.Surjective ev := by
  have heventually := eventually_det_ne_zero_of_tendsto_fromBlocks_zero₁₂
    (fun t => Matrix.of fun i j => ev (sections t j) i) A B D hsections hA hD
  obtain ⟨t, ht⟩ := heventually.exists
  exact linearMap_surjective_of_evaluationMatrix_det_ne_zero ev (sections t) ht

/-- Local uniform convergence of finitely many entire columns implies convergence of every finite
mixed-jet evaluation matrix.  This is the exact analytic-to-algebraic handoff used before
`finiteJetPacketPeeling_surjective`: no derivative-limit hypothesis is needed separately. -/
theorem tendsto_multiIndexJetEvaluationMatrix_of_locallyUniform
    {T Row Col : Type*} {l : Filter T} {d : ℕ}
    [Fintype Row] [Fintype Col]
    (F : T → Col → MultivariateEntire d) (G : Col → MultivariateEntire d)
    (point : Row → Fin d → ℂ) (index : Row → Fin d →₀ ℕ)
    (hF : ∀ j, TendstoLocallyUniformly (fun t => (F t j).1) (G j).1 l) :
    Tendsto
      (fun t => Matrix.of fun i j => multiIndexJetEvalCLM (point i) (index i) (F t j)) l
      (nhds (Matrix.of fun i j => multiIndexJetEvalCLM (point i) (index i) (G j))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hFG : Tendsto (fun t => F t j) l (nhds (G j)) := by
    rw [tendsto_subtype_rng]
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr (hF j)
  exact (multiIndexJetEvalCLM (point i) (index i)).continuous.continuousAt.tendsto.comp hFG

end

end GaloisForLFunctions.HTGeometry
