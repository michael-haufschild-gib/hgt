import GaloisForLFunctions.HTGeometry.PSDKernelOperations

/-!
# Positivity of a continuous kernel is decided on a dense test family

The energy of a finite node/coefficient system depends continuously on both the coefficients and
the nodes, so the closed condition of nonnegative energy propagates from a dense set of nodes and
coefficients to all of them.  A continuous Hermitian kernel is therefore positive semidefinite as
soon as it has nonnegative energy on one countable dense test family.
-/

noncomputable section

open Set Topology
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [TopologicalSpace X] {K : X → X → ℂ}

theorem continuous_kernelEnergy (hK : Continuous fun p : X × X => K p.1 p.2) (n : ℕ) :
    Continuous fun p : (Fin n → ℂ) × (Fin n → X) => kernelEnergy K p.1 p.2 := by
  simp only [kernelEnergy]
  refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
  refine Continuous.mul (Continuous.mul ?_ ?_) ?_
  · exact Complex.continuous_conj.comp ((continuous_apply j).comp continuous_fst)
  · exact (continuous_apply k).comp continuous_fst
  · have hpair : Continuous fun p : (Fin n → ℂ) × (Fin n → X) => (p.2 j, p.2 k) :=
      ((continuous_apply j).comp continuous_snd).prodMk ((continuous_apply k).comp continuous_snd)
    exact hK.comp hpair

set_option maxHeartbeats 1000000 in
/-- **Dense testing.**  A continuous Hermitian kernel is positive semidefinite as soon as every
finite system with coefficients in a dense set and nodes in a dense set has nonnegative energy. -/
theorem isPSDKernel_of_dense_energy (hherm : ∀ x y, conj (K x y) = K y x)
    (hK : Continuous fun p : X × X => K p.1 p.2)
    {sc : Set ℂ} (hsc : Dense sc) {sw : Set X} (hsw : Dense sw)
    (h : ∀ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → X),
      (∀ j, c j ∈ sc) → (∀ j, w j ∈ sw) → 0 ≤ (kernelEnergy K c w).re) :
    IsPSDKernel K := by
  refine isPSDKernel_of_forall_posSemidef hherm (fun n w => ?_)
  refine posSemidef_of_isHermitian_of_re_nonneg ?_ (fun c => ?_)
  · ext j k
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
    exact hherm _ _
  · rw [dotProduct_mulVec_kernelMatrix]
    have hdense : Dense ((Set.pi Set.univ fun _ : Fin n => sc)
        ×ˢ (Set.pi Set.univ fun _ : Fin n => sw)) :=
      (dense_pi Set.univ fun i _ => hsc).prod (dense_pi Set.univ fun i _ => hsw)
    have hclosed : IsClosed {p : (Fin n → ℂ) × (Fin n → X) | 0 ≤ (kernelEnergy K p.1 p.2).re} :=
      isClosed_le continuous_const (Complex.continuous_re.comp (continuous_kernelEnergy hK n))
    have hsub : ((Set.pi Set.univ fun _ : Fin n => sc) ×ˢ (Set.pi Set.univ fun _ : Fin n => sw))
        ⊆ {p : (Fin n → ℂ) × (Fin n → X) | 0 ≤ (kernelEnergy K p.1 p.2).re} := by
      rintro ⟨c', w'⟩ ⟨hc', hw'⟩
      exact h n c' w' (fun j => hc' j (Set.mem_univ j)) (fun j => hw' j (Set.mem_univ j))
    have hmem : (c, w) ∈ closure ((Set.pi Set.univ fun _ : Fin n => sc)
        ×ˢ (Set.pi Set.univ fun _ : Fin n => sw)) := by
      rw [hdense.closure_eq]
      exact Set.mem_univ _
    have hres : (c, w) ∈ {p : (Fin n → ℂ) × (Fin n → X) | 0 ≤ (kernelEnergy K p.1 p.2).re} :=
      closure_minimal hsub hclosed hmem
    exact hres

end GaloisForLFunctions.HTGeometry
