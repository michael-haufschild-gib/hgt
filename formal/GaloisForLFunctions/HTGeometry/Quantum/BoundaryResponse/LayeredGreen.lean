import GaloisForLFunctions.HTGeometry.Quantum.BoundaryResponse.BoundaryNodalDomains
import GaloisForLFunctions.HTGeometry.Quantum.BoundaryResponse.SpectralGreen

/-!
# Green function poles of the layered network

The response matrix of the harmonic extension has a simple pole in its
shifted inverse at each color eigenvalue. Its coefficient is the outer
product of the color profile divided by the number of vertices of that color.
-/

open Filter Matrix
open scoped Topology Matrix

namespace GaloisForLFunctions.HTGeometry.WeightedGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The unnormalized Laplacian is the diagonal of weighted degrees minus
the conductance matrix. -/
def networkLaplacian (G : WeightedGraph V) : Matrix V V ℝ :=
  Matrix.diagonal G.mass - Matrix.of G.w

theorem isHermitian_networkLaplacian (G : WeightedGraph V) : G.networkLaplacian.IsHermitian := by
  change G.networkLaplacianᴴ = G.networkLaplacian
  ext v u
  simp only [networkLaplacian, Matrix.conjTranspose_apply, star_trivial, Matrix.sub_apply,
    Matrix.of_apply, G.w_symm u v]
  by_cases h : v = u
  · subst u
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem networkLaplacian_mulVec (G : WeightedGraph V) (x : V → ℝ) (v : V) :
    (G.networkLaplacian *ᵥ x) v = G.networkFlux x v := by
  rw [networkLaplacian, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
  simp only [networkFlux, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    mass, Matrix.mulVec, dotProduct, Matrix.of_apply]

end

end GaloisForLFunctions.HTGeometry.WeightedGraph

namespace GaloisForLFunctions.HTGeometry.BoundaryResponse

noncomputable section

/-- Matrix of the layered network's Dirichlet-to-Neumann map. -/
def layeredBoundaryLaplacian (K N : ℕ) : Matrix (LayeredBoundary K N) (LayeredBoundary K N) ℝ :=
  (layeredBoundaryGraph K N).networkLaplacian

theorem isHermitian_layeredBoundaryLaplacian (K N : ℕ) : (layeredBoundaryLaplacian K N).IsHermitian :=
  (layeredBoundaryGraph K N).isHermitian_networkLaplacian

theorem layeredBoundaryLaplacian_mulVec (K N : ℕ) (x : LayeredBoundary K N → ℝ)
    (v : LayeredBoundary K N) :
    (layeredBoundaryLaplacian K N *ᵥ x) v = layeredBoundaryResponse K N x v := by
  rw [layeredBoundaryLaplacian, WeightedGraph.networkLaplacian_mulVec]
  exact ((layeredBoundaryGraph K N).seriesNetwork_boundary_flux (layerBoundaryGraph K N) x v).symm

/-- The squared norm of a color profile counts its occupied boundary vertices. -/
theorem colorMode_dotProduct_self (K : ℕ) {N : ℕ} (i : Fin (N + 1)) :
    dotProduct (colorMode (K := K) i) (colorMode i) = 2 * ((K + 1 : ℕ) : ℝ) := by
  rw [dotProduct, Fintype.sum_prod_type]
  have h (j : Fin (N + 1)) (r : Bool × Fin (K + 1)) :
      colorMode i (j, r) * colorMode i (j, r) = if j = i then 1 else 0 := by
    by_cases hj : j = i
    · simp only [colorMode, if_pos hj]
      rcases r with ⟨s, r⟩
      cases s
      · change (1 : ℝ) * 1 = 1
        exact one_mul 1
      · change (-1 : ℝ) * -1 = 1
        rw [neg_mul_neg, one_mul]
    · simp only [colorMode, if_neg hj, mul_zero]
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, mul_ite, mul_one, mul_zero,
    Fintype.sum_ite_eq']

private theorem exists_spectralIndex_of_mulVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {μ : ℝ} {x : ι → ℝ}
    (hx : x ≠ 0) (he : A *ᵥ x = μ • x) : ∃ k, hA.eigenvalues k = μ := by
  by_contra! hn
  have hz : (A - μ • (1 : Matrix ι ι ℝ)) *ᵥ x = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he, sub_self]
  have h := congrArg (fun y => spectralGreen hA μ *ᵥ y) hz
  apply hx
  simpa only [Matrix.mulVec_mulVec, (spectralGreen_mul_shift hA μ hn).1, Matrix.one_mulVec,
    Matrix.mulVec_zero] using h

private theorem layeredBasis_colorMode (K N : ℕ) (i : Fin (N + 1)) (k : LayeredBoundary K N)
    (hk : (isHermitian_layeredBoundaryLaplacian K N).eigenvalues k = colorEigenvalue K i) :
    ∃ c : ℝ, c ≠ 0 ∧
      (⇑((isHermitian_layeredBoundaryLaplacian K N).eigenvectorBasis k) :
        LayeredBoundary K N → ℝ) = c • colorMode i := by
  let hA := isHermitian_layeredBoundaryLaplacian K N
  let b : LayeredBoundary K N → ℝ := hA.eigenvectorBasis k
  let level : Set.Ioo (0 : ℝ) (upperBoundaryLevel K N) :=
    ⟨colorEigenvalue K i, colorEigenvalue_bounds K i⟩
  have hnonzero : b ≠ 0 := by
    intro hb
    have h := hA.star_eigenvectorUnitary_mulVec k
    change (star (hA.eigenvectorUnitary : Matrix _ _ ℝ)) *ᵥ b = Pi.single k 1 at h
    rw [hb, Matrix.mulVec_zero] at h
    have he := congrFun h k
    exact zero_ne_one (by simpa only [Pi.zero_apply, Pi.single_eq_same] using he)
  have he : layeredBoundaryLaplacian K N *ᵥ b = (level : ℝ) • b := by
    change layeredBoundaryLaplacian K N *ᵥ b = colorEigenvalue K i • b
    rw [← hk]
    exact hA.mulVec_eigenvectorBasis k
  obtain ⟨j, hj, c, hc, hb⟩ :=
    (layeredBoundaryResponse_smallPositiveEigenpair_iff K N level b).mp
      ⟨hnonzero, fun v => by rw [← layeredBoundaryLaplacian_mulVec, he]; rfl⟩
  have hij : i = j := (strictMono_colorEigenvalue K N).injective hj
  subst j
  exact ⟨c, hc, hb⟩

/-- Exactly one vector in the orthonormal spectral basis has the specified
color eigenvalue. -/
theorem existsUnique_layeredSpectralIndex (K N : ℕ) (i : Fin (N + 1)) :
    ∃! k, (isHermitian_layeredBoundaryLaplacian K N).eigenvalues k = colorEigenvalue K i := by
  let hA := isHermitian_layeredBoundaryLaplacian K N
  let x : LayeredBoundary K N → ℝ := colorMode i
  have he : layeredBoundaryLaplacian K N *ᵥ x = colorEigenvalue K i • x := by
    funext v
    exact ((layeredBoundaryGraph K N).networkLaplacian_mulVec x v).trans
      (layeredBoundaryGraph_flux_colorMode K i v)
  obtain ⟨k, hk⟩ := exists_spectralIndex_of_mulVec_eq hA (colorMode_ne_zero K i) he
  refine ⟨k, hk, ?_⟩
  intro j hj
  by_contra hne
  obtain ⟨c, _, hc⟩ := layeredBasis_colorMode K N i k hk
  obtain ⟨d, hd, hb⟩ := layeredBasis_colorMode K N i j hj
  let U : Matrix (LayeredBoundary K N) (LayeredBoundary K N) ℝ := hA.eigenvectorUnitary
  have hc' : (star U) *ᵥ (c • x) = Pi.single k 1 := by
    rw [← hc]
    exact hA.star_eigenvectorUnitary_mulVec k
  have hd' : (star U) *ᵥ (d • x) = Pi.single j 1 := by
    rw [← hb]
    exact hA.star_eigenvectorUnitary_mulVec j
  have h₁ : c * ((star U) *ᵥ x) k = 1 := by
    rw [Matrix.mulVec_smul] at hc'
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] using congrFun hc' k
  have h₀ : d * ((star U) *ᵥ x) k = 0 := by
    rw [Matrix.mulVec_smul] at hd'
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm hne)] using congrFun hd' k
  rw [(mul_eq_zero.mp h₀).resolve_left hd, mul_zero] at h₁
  exact zero_ne_one h₁

/-- The spectral projector is the outer product of the corresponding color
mode, normalized by its squared norm. -/
theorem layeredBoundaryPoleProjector (K N : ℕ) (i : Fin (N + 1)) :
    spectralPoleProjector (isHermitian_layeredBoundaryLaplacian K N) (colorEigenvalue K i) =
      (2 * ((K + 1 : ℕ) : ℝ))⁻¹ • Matrix.vecMulVec (colorMode i) (colorMode i) := by
  let hA := isHermitian_layeredBoundaryLaplacian K N
  let U : Matrix (LayeredBoundary K N) (LayeredBoundary K N) ℝ := hA.eigenvectorUnitary
  let x : LayeredBoundary K N → ℝ := colorMode i
  let D : ℝ := 2 * ((K + 1 : ℕ) : ℝ)
  obtain ⟨k, hk, huniq⟩ := existsUnique_layeredSpectralIndex K N i
  obtain ⟨c, _, hc⟩ := layeredBasis_colorMode K N i k hk
  have hu (v : LayeredBoundary K N) : U v k = c * x v :=
    (hA.eigenvectorUnitary_apply v k).trans (congrFun hc v)
  have hunit : (∑ v, U v k * U v k) = 1 := by
    have h := congrFun (hA.star_eigenvectorUnitary_mulVec k) k
    simp only [Matrix.mulVec, dotProduct, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, star_trivial, Pi.single_eq_same] at h
    exact h
  have hnorm : (c * c) * D = 1 := by
    dsimp only [D]
    rw [← colorMode_dotProduct_self K i, dotProduct, Finset.mul_sum, ← hunit]
    apply Finset.sum_congr rfl
    intro v _
    rw [hu]
    ring
  have hcD : c * c = D⁻¹ := by
    have hD : D ≠ 0 := by dsimp only [D]; positivity
    rw [← one_div]
    exact (eq_div_iff hD).mpr hnorm
  ext v u
  rw [spectralPoleProjector_apply, Finset.sum_eq_single k, if_pos hk, mul_one,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, ← hcD]
  · change U v k * U u k = c * c * (x v * x u)
    rw [hu v, hu u]
    ring
  · intro j _ hj
    rw [if_neg (fun he => hj (huniq j he)), mul_zero]
  · exact fun h => (h (Finset.mem_univ k)).elim

/-- The actual harmonic boundary response has the predicted rank-one
Green function pole at each positive color eigenvalue. -/
theorem tendsto_layeredBoundaryShiftedInverse_colorPole (K N : ℕ) (i : Fin (N + 1)) :
    Tendsto (fun s => (colorEigenvalue K i - s) • (layeredBoundaryLaplacian K N -
      s • (1 : Matrix (LayeredBoundary K N) (LayeredBoundary K N) ℝ))⁻¹)
      (𝓝[≠] (colorEigenvalue K i))
      (𝓝 ((2 * ((K + 1 : ℕ) : ℝ))⁻¹ • Matrix.vecMulVec (colorMode i) (colorMode i))) := by
  rw [← layeredBoundaryPoleProjector K N i]
  exact tendsto_shiftedInverse_pole (isHermitian_layeredBoundaryLaplacian K N) (colorEigenvalue K i)

#print axioms layeredBoundaryLaplacian_mulVec
#print axioms existsUnique_layeredSpectralIndex
#print axioms layeredBoundaryPoleProjector
#print axioms tendsto_layeredBoundaryShiftedInverse_colorPole

end

end GaloisForLFunctions.HTGeometry.BoundaryResponse
