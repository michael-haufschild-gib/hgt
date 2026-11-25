import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.SpectralCoordinates.EntryFunctions
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.SpectralCoordinates.ProjectorWeights
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.OrbitContacts
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeHardGapLaw

/-! # Rational contact equations force dependence of the relative eigenphases -/

open Matrix Finset
open scoped ComplexConjugate Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.SpectralCoordinates
noncomputable section
variable {F : Type*} [Field F] [Algebra F ℂ]

private theorem relative_character {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (E : Bits N → ℝ) (k : Bits N) (t : ℝ) :
    fourier 1 (RHTower.zeroAnchoredPhase d (RHTower.projectivePhysicalPhaseFlow (E ∘ e.symm) t) (e k))=
      anchorPhase E k t/anchorPhase E (e.symm 0) t := by
  rw [RHTower.fourier_projectiveChoiPhase_eq_exp,anchorPhase,anchorPhase,←Complex.exp_sub]
  congr 1
  generalize h : e k=i
  have hk : e.symm i=k := by rw [←h,e.symm_apply_apply]
  rw [←hk]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.cases_succ,RHTower.zeroProjectiveFrequency,Function.comp_apply,Complex.ofReal_mul,Complex.ofReal_sub]
    ring

/-- A nontrivial polynomial equation on the relative evolution gives an
algebraic dependence among the relative unit phases over any field
containing the Hamiltonian entries, its simple energies, and i. -/
theorem contact_dependent {R : Type*} [CommRing R] (κ : R →+* ℝ) {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (H : selfAdjoint (Square (Bits N)))
    (K : IntermediateField F ℂ) (hκ : ∀ r, (κ r:ℂ)∈K) (hI : Complex.I∈K) (hH : EntriesIn K H.val)
    (hE : ∀ k, (H.2.isHermitian.eigenvalues k:ℂ)∈K) (hinj : Function.Injective H.2.isHermitian.eigenvalues)
    (p : EntryPolynomial N R) (v : ℝ) (hz : entryEval κ (relativeOrbit e H v) p=0)
    (hn : ∃ u, entryEval κ (relativeOrbit e H u) p≠0) :
    let E := H.2.isHermitian.eigenvalues
    let b := e.symm 0
    ¬AlgebraicIndependent K (fun i : {j // j≠b} => anchorPhase E i.val v / anchorPhase E b v) := by
  intro E b hfree
  let z (t : ℝ) (i : {j // j≠b}) := anchorPhase E i.val t/anchorPhase E b t
  let S := phaseFunctionRing K z
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let c (i j k : Bits N) := V.val i k*(V⁻¹).val k j
  let q (k : Bits N) (t : ℝ) := anchorPhase E k t/anchorPhase E b t
  have hm (i j k) : c i j k∈K := projector_weight_mem K H.2.isHermitian hH hE hinj i j k
  have hc (i j k) : conj (c i j k)=c j i k := by
    change conj (V.val i k*conj (V.val j k))=V.val j k*conj (V.val i k)
    rw [map_mul,Complex.conj_conj,mul_comm]
  have hnorm (k) (t : ℝ) : ‖q k t‖=1 := by
    simp [q,anchorPhase,norm_div,Complex.norm_exp]
  have hq (k : Bits N) : q k∈S ∧ (fun t => conj (q k t))∈S := by
    by_cases hk : k=b
    · subst k
      have h1 : q b=1 := funext fun t => div_self (Complex.exp_ne_zero _)
      rw [h1]
      simpa only [Pi.one_apply,map_one] using And.intro S.one_mem S.one_mem
    · refine ⟨coordinate_mem_phaseFunctionRing K z ⟨k,hk⟩,?_⟩
      simp_rw [←Complex.inv_eq_conj (hnorm k _)]
      exact invCoordinate_mem_phaseFunctionRing K z ⟨k,hk⟩ fun t => norm_ne_zero_iff.mp (by rw [hnorm]; exact one_ne_zero)
  have he (i j : Bits N) (t : ℝ) : relativeOrbit e H t i j=∑ k, c i j k*q k t := by
    change ((V.val*diagonal _)*(V⁻¹).val) i j=_
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mul_diagonal,relative_character e E]
    dsimp only [c,q,b]
    ring
  have hu (i j) : (fun t => relativeOrbit e H t i j)∈S ∧ (fun t => conj (relativeOrbit e H t i j))∈S := by
    constructor
    · simp_rw [he]
      change (∑ k, (fun _ : ℝ => c i j k) * q k)∈S
      exact S.sum_mem fun k _ => S.mul_mem (constant_mem_phaseFunctionRing K z ⟨_,hm i j k⟩) (hq k).1
    · simp_rw [he,map_sum,map_mul,hc]
      change (∑ k, (fun _ : ℝ => c j i k)*(fun t => conj (q k t)))∈S
      exact S.sum_mem fun k _ => S.mul_mem (constant_mem_phaseFunctionRing K z ⟨_,hm j i k⟩) (hq k).2
  have h := (eval_zero_iff K z (polynomial_mem K z κ hκ (relativeOrbit e H) hI hu p) hfree).mp (by exact_mod_cast hz)
  obtain ⟨u,hu⟩ := hn
  exact hu (by exact_mod_cast h u)

#print axioms contact_dependent
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.SpectralCoordinates

