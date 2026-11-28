import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators.Hamiltonian

/-! # The measured prime number operators determine the full Hamiltonian graph -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators

open Filter Topology ModeCapacities CoassociativeSplitting
open scoped LinearPMap

private def coreGraph : Core →ₗ[ℂ] Gas × Gas := embed.prod (embed.comp coreEnergy)

private theorem basisGraph (i : ℕ+) (c : ℂ) :
    (c • HilbertSchmidt.lpBasis ℕ+ i, ((energy i:ℂ)*c) • HilbertSchmidt.lpBasis ℕ+ i) ∈
      LinearMap.range coreGraph := by
  refine ⟨c • ket (label.symm i),?_⟩
  apply Prod.ext
  · change embed (c • ket (label.symm i)) = _
    rw [map_smul,embed_ket,label.apply_symm_apply,HilbertSchmidt.lpBasis_apply]
  · change embed (coreEnergy (c • ket (label.symm i))) = _
    rw [map_smul,coreEnergy_ket,map_smul,map_smul,embed_ket,label.apply_symm_apply,
      HilbertSchmidt.lpBasis_apply,smul_smul,mul_comm c]

private theorem core_closure : closure (LinearMap.range coreGraph : Set (Gas × Gas)) =
    (hamiltonian.graph : Set (Gas × Gas)) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (HTGeometry.maximalRealDiagonal_isClosed energy)
    rintro _ ⟨f,rfl⟩
    obtain ⟨g,inc,act⟩ := physical_energy f
    exact hamiltonian.mem_graph_iff.mpr ⟨g,inc,act⟩
  · intro xy hg
    obtain ⟨g,inc,act⟩ := hamiltonian.mem_graph_iff.mp hg
    have eqn : ((g:Gas), hamiltonian g) = xy := Prod.ext inc act
    rw [← eqn]
    let b := HilbertSchmidt.lpBasis ℕ+
    have expansion := (b.hasSum_repr (g:Gas)).prodMk (b.hasSum_repr (hamiltonian g))
    apply isClosed_closure.mem_of_tendsto expansion
    apply Filter.Eventually.of_forall
    intro S
    apply subset_closure
    apply (LinearMap.range coreGraph).sum_mem
    intro i _
    exact basisGraph i ((g:Gas) i)

/-- Closing the finite measured number-operator graph recovers both
the maximal domain and the action of the self-adjoint gas Hamiltonian. -/
theorem measured_graph (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (line : s.re=1/2) :
    closure (Set.range fun f : Core => (embed f, embed (modeEnergy (kernel s u v) (activeModes f) f))) =
      (hamiltonian.graph : Set (Gas × Gas)) := by
  have same (f : Core) : embed (modeEnergy (kernel s u v) (activeModes f) f) = embed (coreEnergy f) := by
    obtain ⟨g,gi,ga⟩ := sum_number s hu hv line f
    obtain ⟨w,wi,wa⟩ := physical_energy f
    have gw : g=w := Subtype.ext (gi.trans wi.symm)
    exact ga.symm.trans ((congrArg (fun x : hamiltonian.domain => hamiltonian x) gw).trans wa)
  simp only [same]
  exact core_closure

#print axioms measured_graph

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators
