import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.CompletedPrimeBoundary

/-!
# The exact closed relation of the finite prime boundary

Above the arithmetic summability threshold, graph closure is precisely the
graph of the bounded Riesz extension. At and below the threshold, the explicit
vertical unit packet and density of finite chains force graph closure to be
the entire product. This distinguishes a closed relation from a closed operator.
-/

noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open RHTower EffectiveScalingGeometry

/-- The actual finite boundary graph as a complex linear subspace. -/
def primeWeightedGraphSubmodule (s : ℂ) (δ : ℝ) : Submodule ℂ (PrimeChainHilbert × ℂ) :=
  LinearMap.range ((primeWeightedChainEmbedding δ).prod (dirichletPrimeChainFunctional s))

theorem primeWeightedGraphSubmodule_coe (s : ℂ) (δ : ℝ) :
    (primeWeightedGraphSubmodule s δ : Set (PrimeChainHilbert × ℂ))=primeWeightedBoundaryGraph s δ := rfl

/-- At and below the threshold, the closed boundary relation is the whole product. -/
theorem primeWeightedBoundary_closure_eq_univ (s : ℂ) (δ : ℝ) (h : 2*s.re+δ ≤ 1) :
    closure (primeWeightedBoundaryGraph s δ)=Set.univ := by
  let T := (primeWeightedGraphSubmodule s δ).topologicalClosure
  have hT : (T : Set (PrimeChainHilbert × ℂ))=closure (primeWeightedBoundaryGraph s δ) := rfl
  have hu : ((0:PrimeChainHilbert),(1:ℂ))∈T := by
    rw [hT]
    exact primeWeightedBoundary_graph_closure_unit s δ h
  have hv (z : ℂ) : ((0:PrimeChainHilbert),z)∈T := by
    have hh := T.smul_mem z hu
    simpa only [Prod.smul_mk,smul_zero,smul_eq_mul,mul_one] using hh
  have hf (a) : (primeWeightedChainEmbedding δ a,(0:ℂ))∈T := by
    have hg : (primeWeightedChainEmbedding δ a,dirichletPrimeChainFunctional s a)∈T := by
      rw [hT]
      exact subset_closure ⟨a,rfl⟩
    have hh := T.sub_mem hg (hv (dirichletPrimeChainFunctional s a))
    simpa only [Prod.sub_mk,sub_zero,sub_self] using hh
  have hTc : IsClosed (T : Set (PrimeChainHilbert × ℂ)) := by
    rw [hT]
    exact isClosed_closure
  have hc : IsClosed {u : PrimeChainHilbert | (u,(0:ℂ))∈T} :=
    hTc.preimage (continuous_id.prodMk continuous_const)
  have hh (u : PrimeChainHilbert) : (u,(0:ℂ))∈T := by
    apply (closure_minimal (fun v hv => ?_) hc) (primeWeightedChainEmbedding_dense δ u)
    obtain ⟨a,rfl⟩ := hv
    exact hf a
  apply Set.eq_univ_of_forall
  intro z
  rw [←hT]
  have hz := T.add_mem (hh z.1) (hv z.2)
  simpa only [Prod.add_mk,add_zero,zero_add] using hz

/-- In the bounded region, closure retains exactly the graph of the arithmetic Riesz extension. -/
theorem primeWeightedBoundary_closure_eq_graph (s : ℂ) (δ : ℝ) (h : 1 < 2*s.re+δ) :
    closure (primeWeightedBoundaryGraph s δ)=
      {z : PrimeChainHilbert × ℂ | primeWeightedBoundaryExtension s δ h z.1=z.2} := by
  let φ := primeWeightedBoundaryExtension s δ h
  have hf (a) : φ (primeWeightedChainEmbedding δ a)=dirichletPrimeChainFunctional s a :=
    LinearMap.congr_fun (primeWeightedBoundaryExtension_finite s δ h) a
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro z ⟨a,rfl⟩
      exact hf a
    · exact isClosed_eq (φ.continuous.comp continuous_fst) continuous_snd
  · intro z hz
    have hc : IsClosed {u : PrimeChainHilbert | (u,φ u)∈closure (primeWeightedBoundaryGraph s δ)} :=
      isClosed_closure.preimage (continuous_id.prodMk φ.continuous)
    have hmem : (z.1,φ z.1)∈closure (primeWeightedBoundaryGraph s δ) := by
      apply (closure_minimal (fun v hv => ?_) hc) (primeWeightedChainEmbedding_dense δ z.1)
      obtain ⟨a,rfl⟩ := hv
      rw [hf]
      exact subset_closure ⟨a,rfl⟩
    change φ z.1=z.2 at hz
    simpa only [hz] using hmem

/-- The actual finite boundary graph is dense exactly where no closed extension exists. -/
theorem primeWeightedBoundaryGraph_dense_iff (s : ℂ) (δ : ℝ) :
    Dense (primeWeightedBoundaryGraph s δ) ↔ 2*s.re+δ ≤ 1 := by
  constructor
  · intro hd
    by_contra hn
    have h := lt_of_not_ge hn
    have hu := hd ((0:PrimeChainHilbert),(1:ℂ))
    rw [primeWeightedBoundary_closure_eq_graph s δ h] at hu
    change primeWeightedBoundaryExtension s δ h 0=1 at hu
    rw [map_zero] at hu
    exact zero_ne_one hu
  · intro h
    intro z
    rw [primeWeightedBoundary_closure_eq_univ s δ h]
    trivial

#print axioms primeWeightedGraphSubmodule_coe
#print axioms primeWeightedBoundary_closure_eq_univ
#print axioms primeWeightedBoundary_closure_eq_graph
#print axioms primeWeightedBoundaryGraph_dense_iff
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
