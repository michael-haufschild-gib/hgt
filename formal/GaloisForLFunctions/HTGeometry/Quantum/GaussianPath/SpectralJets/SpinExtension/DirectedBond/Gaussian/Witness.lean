import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.ProductRank
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.NumberedSlice
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.AmbientPacket
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.DetectorGerm

/-! # A nonzero integral spectral detector at order two per spin minus one -/
open Matrix MvPolynomial Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- Include the constant row once to test rank modulo global energy shifts. -/
def detectorRows {D m : ℕ} (k : Fin D) (w : Fin D→List (Fin m)) (i : Fin D) :=
  if i=k then none else some (w i)

theorem detectorRows_bound {D m L : ℕ} (k : Fin D) (w : Fin D→List (Fin m))
    (h : ∀ i, (w i).length≤L) : ∀ i v, v∈detectorRows k w i → v.length≤L := by
  intro i v hv
  by_cases hi : i=k
  · simp [detectorRows,hi] at hv
  · rw [detectorRows,if_neg hi] at hv
    cases Option.some.inj hv
    exact h i

/-- A single product Hamiltonian witnesses nonvanishing for the full Gaussian
Pauli pencil. All nonconstant rows use only directed bonds and the final field. -/
theorem product_detector_witness (n : ℕ) (j : Bool) :
    ∃ (B : Fin (n+1)→ℕ) (k : Fin (2^(n+1))) (v : Fin (2^(n+1))→List (Fin (n+1))),
      (∀ i, ∃ u, Suffix n u ∧ v i=letters j u) ∧
      (∀ i, (v i).length≤2*n+order j) ∧
      ∃ θ : Coordinates (n+1)→ℝ, synthesis (chainPauliFin (n+1)) (fun a => (θ a:ℂ)) =
        reindex (qubitConfigFin (n+1)) (qubitConfigFin (n+1)) (background n B 0) ∧
        eval₂Hom GaussianInt.toComplex (fun a => (θ a:ℂ))
        (pathDetector (n+1) (2*n+order j) (detectorRows k (fun i => (v i).map (fieldIndex n))))≠0 := by
  obtain ⟨B,k,f,hi,hf,hd⟩ := product_full_projective_rank n
  obtain ⟨v,hv,hl,hm⟩ := hd j
  obtain ⟨θ,hθ⟩ := numbered_slice n B
  let q := qubitConfigFin (n+1)
  let P := chainPauliFin (n+1)
  let x : Coordinates (n+1)→ℂ := fun a => θ a
  let ι := fieldIndex n
  let e (l : Fin (2^(n+1))) := f (q.symm l)
  have hs (l) : AnalyticAt ℂ (e l) 0 ∧ ∀ᶠ y in 𝓝 0,
      matrixCharpolyRelation (synthesis P (embed x ι y),e l y)=0 := by
    refine ⟨(hf (q.symm l)).1,?_⟩
    filter_upwards [(hf (q.symm l)).2] with y hy
    rw [←hθ y]
    simpa only [matrixCharpolyRelation,←Matrix.eval_charpoly,Matrix.charpoly_reindex] using hy
  obtain ⟨F,hFi,hF,he⟩ := ambient_slice_packet P x ι e (hi.comp q.symm.injective) hs
  let w (i : Fin (2^(n+1))) := (v (q.symm i)).map ι
  have hb (i) : (v (q.symm i)).length≤2*n+order j := hl _
  have hw (i) : (w i).length≤2*n+order j := by simpa [w] using hb i
  refine ⟨B,q k,fun i => v (q.symm i),fun i => hv (q.symm i),hb,θ,?_,?_⟩
  · simpa only [embed_zero,chain,map_zero,Prod.fst_zero,Prod.snd_zero,zero_smul,add_zero] using (hθ 0).symm
  apply detector_of_germs (integralGenerators (n+1)) GaussianInt.toComplex x F hFi
  · intro l
    simpa only [generators_map,synthesis_apply] using hF l
  · exact detectorRows_bound (q k) w hw
  · let T := of fun i l => if i=k then (1:ℂ) else mixed (v i) (f l) 0
    have heq : (of fun i l => rowValue (detectorRows (q k) w i) (F l) x) = reindex q q T := by
      ext i l
      by_cases h : i=q k
      · subst i
        simp [T,detectorRows,rowValue,Matrix.reindex_apply,Matrix.submatrix_apply]
      · have h' : q.symm i≠k := fun h₁ => h ((q.apply_symm_apply i).symm.trans (congrArg q h₁))
        simp only [T,w,detectorRows,if_neg h,rowValue,Option.elim_some,Matrix.of_apply,
          Matrix.reindex_apply,Matrix.submatrix_apply,if_neg h',he,e]
    rw [heq,Matrix.det_reindex_self]
    exact hm

/-- The same fixed rows give a nonzero polynomial on the unrestricted real
coefficient space of the path ensemble. -/
theorem physical_detector_witness (n : ℕ) (j : Bool) :
    ∃ (k : Fin (2^(n+1))) (v : Fin (2^(n+1))→List (Fin (n+1))),
      (∀ i, ∃ u, Suffix n u ∧ v i=letters j u) ∧
      (∀ i, (v i).length≤2*n+order j) ∧
      ∃ θ : Coordinates (n+1)→ℝ, eval₂Hom GaussianInt.toComplex (fun a => (θ a:ℂ))
        (pathDetector (n+1) (2*n+order j) (detectorRows k (fun i => (v i).map (fieldIndex n))))≠0 := by
  obtain ⟨_,k,v,hv,hl,θ,_,hd⟩ := product_detector_witness n j
  exact ⟨k,v,hv,hl,θ,hd⟩

#print axioms product_detector_witness
#print axioms physical_detector_witness
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
