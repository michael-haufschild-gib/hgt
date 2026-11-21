import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum

/-! # Continuous spectral labels pinned to a diagonal doublet reference -/
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

/-- Labels at a diagonal parameter may be assigned to the computational
states even at collisions. Sorting gives continuous labels away from the
reference without choosing any eigenvectors. -/
theorem continuous_levels {I X : Type*} [Fintype I] [DecidableEq I]
    [TopologicalSpace X] [FirstCountableTopology X] (F : X → Matrix I I ℂ) (hF : Continuous F)
    (hH : ∀ v, (F v).IsHermitian) (b : X) (d : I → ℝ)
    (hd : F b=diagonal (fun i => (d i:ℂ))) :
    ∃ E : I → X → ℝ, (∀ i, Continuous (E i)) ∧ (∀ i, E i b=d i) ∧
      ∀ v, (F v).charpoly=∏ i, (Polynomial.X-Polynomial.C (E i v:ℂ)) := by
  classical
  let e := Fintype.equivFin I
  let G := fun v => Matrix.reindex e e (F v)
  have hg : Continuous G := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (e.symm j)).comp ((continuous_apply (e.symm i)).comp hF)
  have hh (v : X) : (G v).IsHermitian := (hH v).reindex e
  let a := fun i => d (e.symm i)
  let k := e.trans (Tuple.sort a).symm
  let L v := sortedTuple (hh v).eigenvalues
  have hc : Continuous L := continuous_sortedTuple_eigenvalues hg hh
  have hbase : L b=sortedTuple a := by
    apply eq_of_monotone_of_sum_pow_eq (monotone_sortedTuple _) (monotone_sortedTuple _)
    intro p
    rw [sum_pow_sortedTuple,sum_pow_sortedTuple,sum_pow_eigenvalues_eq_trace_pow_re]
    change ((Matrix.reindex e e (F b)^p).trace).re=_
    rw [trace_pow_reindex,hd,Matrix.diagonal_pow,Matrix.trace_diagonal,Complex.re_sum]
    simp only [Pi.pow_apply,←Complex.ofReal_pow,Complex.ofReal_re]
    exact (Equiv.sum_comp e.symm (fun i => d i ^ p)).symm
  refine ⟨fun i v => L v (k i),fun i => (continuous_apply (k i)).comp hc,?_,?_⟩
  · intro i
    change L b (k i) = d i
    rw [hbase]
    simp [sortedTuple,k,a]
  · intro v
    have h := (hh v).charpoly_eq
    change (Matrix.reindex e e (F v)).charpoly = _ at h
    rw [Matrix.charpoly_reindex] at h
    rw [h]
    exact (Equiv.prod_comp (k.trans (Tuple.sort (hh v).eigenvalues))
      (fun i => Polynomial.X-Polynomial.C ((hh v).eigenvalues i:ℂ))).symm

#print axioms continuous_levels
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
