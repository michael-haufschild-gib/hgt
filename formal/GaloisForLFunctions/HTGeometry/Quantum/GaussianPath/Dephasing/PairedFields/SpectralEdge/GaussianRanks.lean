import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.GaussianFields
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor

/-! # Gaussian first-moment bound for each individual ranked energy -/

open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
noncomputable section

/-- Each ranked energy has mean absolute value at most the number of local
Pauli coefficients. The bound uses their variance and is uniform in rank. -/
theorem gaussian_rank_energy (n : ℕ) (j : Fin (n+2) → Bool) :
    let E (x : Coeff n) := (generator x).2.isHermitian.eigenvalues j
    Integrable E (fieldLaw n) ∧ (∫ x, |E x| ∂fieldLaw n) ≤ Fintype.card (PathLabel n) := by
  intro E
  let I := Fin (n+2) → Bool
  let e : Fin (Fintype.card I) ≃ I := Fintype.equivOfCardEq (Fintype.card_fin _)
  let H (x : Coeff n) := (generator x).2.isHermitian
  let A (x : Coeff n) := Matrix.reindex e.symm e.symm (generator x).val
  let S (x : Coeff n) := sortedTuple (((H x).reindex e.symm).eigenvalues)
  have hcont : Continuous (fun x : Coeff n => (generator x).val) := by
    simp only [generator,pathHamiltonian_eq_sum]
    fun_prop
  have hA : Continuous A := continuous_pi fun i => continuous_pi fun k =>
    (continuous_apply (e k)).comp ((continuous_apply (e i)).comp hcont)
  have hS : Continuous S := continuous_sortedTuple_eigenvalues hA _
  have hv (x : Coeff n) : (fun k => (H x).eigenvalues₀ k.rev)=S x := by
    apply eq_of_monotone_of_sum_pow_eq
    · exact fun _ _ hij => (H x).eigenvalues₀_antitone (Fin.rev_le_rev.mpr hij)
    · exact monotone_sortedTuple _
    · intro p
      rw [show S x=sortedTuple ((H x).eigenvalues ∘ e) from sortedTuple_eigenvalues_reindex e.symm (H x),
        sum_pow_sortedTuple]
      apply (Equiv.sum_comp (Fin.revPerm (n:=Fintype.card I)) (fun k => (H x).eigenvalues₀ k^p)).trans
      apply sum_congr rfl
      intro k _
      change _=(H x).eigenvalues₀ (e.symm (e k))^p
      rw [e.symm_apply_apply]
  have hE : Continuous E := by
    apply ((continuous_apply (e.symm j).rev).comp hS).congr
    intro x
    rw [Function.comp_apply,←hv]
    change (H x).eigenvalues₀ (e.symm j).rev.rev = _
    rw [Fin.rev_rev]
    rfl
  let Q (x : Coeff n) := ∑ i, (1+(x i)^2)/2
  have hi : Integrable (fun t : ℝ => t^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ:=0) (v:=1) 2 (by simp)).integrable_sq
  let γ := gaussianReal 0 1
  have hp (i : PathLabel n) := measurePreserving_eval (fun _ : PathLabel n => γ) i
  have hq (i : PathLabel n) : Integrable (fun x : Coeff n => (1+(x i)^2)/2) (fieldLaw n) :=
    ((integrable_const (1:ℝ)).add ((hp i).integrable_comp_of_integrable hi)).div_const 2
  have hQ : Integrable Q (fieldLaw n) := integrable_finsetSum _ fun i _ => hq i
  have hmajor (x : Coeff n) : |E x| ≤ Q x := by
    apply (abs_eigenvalue_le_l2_opNorm (H x) j).trans
    change ‖pathHamiltonian (WithLp.toLp 2 x)‖ ≤ _
    rw [pathHamiltonian_eq_sum]
    apply (norm_sum_le ..).trans
    apply sum_le_sum
    intro l _
    rw [norm_smul,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs]
    change |x l| ≤ (1+(x l)^2)/2
    nlinarith only [sq_nonneg (|x l|-1),sq_abs (x l)]
  have hiE : Integrable E (fieldLaw n) := hQ.mono' hE.aestronglyMeasurable (ae_of_all _ hmajor)
  refine ⟨hiE,(integral_mono hiE.abs hQ hmajor).trans_eq ?_⟩
  change (∫ x : Coeff n, ∑ i, (1+(x i)^2)/2 ∂fieldLaw n)=_
  rw [integral_finsetSum _ (fun i _ => hq i)]
  have hm (i : PathLabel n) : (∫ x : Coeff n, (1+(x i)^2)/2 ∂fieldLaw n)=1 := by
    have he := integral_map (μ:=fieldLaw n) (hp i).measurable.aemeasurable
      (f:=fun z : ℝ => z^2) (by fun_prop)
    rw [(hp i).map_eq,gaussianZero_integral_sq] at he
    change (1:ℝ)=∫ x : Coeff n, (x i)^2 ∂fieldLaw n at he
    have hi' : Integrable (fun x : Coeff n => (x i)^2) (fieldLaw n) := (hp i).integrable_comp_of_integrable hi
    rw [integral_div,integral_add (integrable_const (1:ℝ)) hi',
      integral_const,probReal_univ,one_smul,←he]
    norm_num
  simp only [hm,sum_const,card_univ,nsmul_eq_mul,mul_one]

#print axioms gaussian_rank_energy
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
