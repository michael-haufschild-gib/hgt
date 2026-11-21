import GaloisForLFunctions.HTGeometry.PatchChainPullback
import GaloisForLFunctions.HTGeometry.PathShellPatchTransport
import GaloisForLFunctions.HTGeometry.SpectralEnsembleEigenvalueBound
import GaloisForLFunctions.HTGeometry.IncubationTubeTransport

/-! # Spectral gap mass of a sparse Pauli path -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FluxOccupation
noncomputable section

/-- A centered packet's second moment forces total positive pair separation.
This estimate uses a bound on the spectral width only. -/
theorem centered_gap_mass {I : Type*} [Fintype I] (E : I → ℝ) {W : ℝ}
    (hc : ∑ i, E i=0) (hw : ∀ i j, E i-E j ≤ W) :
    (Fintype.card I:ℝ)*(∑ i, E i^2) ≤ W*(∑ p : I×I, max 0 (E p.1-E p.2)) := by
  let S := ∑ p : I×I, max 0 (E p.1-E p.2)
  have hdirect : (∑ i, ∑ j, max 0 (E i-E j))=S :=
    (Fintype.sum_prod_type (fun p : I×I => max 0 (E p.1-E p.2))).symm
  have hflip : (∑ i, ∑ j, max 0 (E j-E i))=S := by rw [Finset.sum_comm]; exact hdirect
  have hd (i : I) : (∑ j, (E i-E j)^2)=(Fintype.card I:ℝ)*E i^2+(∑ j, E j^2) := by
    simp only [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      ←Finset.mul_sum,hc,mul_zero,sub_zero]
  have hv : (∑ i, ∑ j, (E i-E j)^2)=2*((Fintype.card I:ℝ)*(∑ i, E i^2)) := by
    simp only [hd,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,two_mul]
  have hpair (i j : I) :
      (E i-E j)^2 ≤ W*max 0 (E i-E j)+W*max 0 (E j-E i) := by
    rcases le_total (E j) (E i) with h | h
    · rw [max_eq_right (sub_nonneg.mpr h),max_eq_left (sub_nonpos.mpr h),mul_zero,add_zero,sq]
      exact mul_le_mul_of_nonneg_right (hw i j) (sub_nonneg.mpr h)
    · rw [max_eq_left (sub_nonpos.mpr h),max_eq_right (sub_nonneg.mpr h),mul_zero,zero_add,sub_sq_comm,sq]
      exact mul_le_mul_of_nonneg_right (hw j i) (sub_nonneg.mpr h)
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hpair i j
  rw [hv] at hh
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  rw [hflip,hdirect] at hh
  change _ ≤ W*S+W*S at hh
  change _ ≤ W*S
  linarith only [hh]

/-- The signed eigenvalues of a path sum to zero and their mean square
is exactly the sum of the squared coupling strengths. -/
theorem path_spectral_moments {n : ℕ} (u : PathShell n) :
    let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
    (∑ j, E j)=0 ∧ (∑ j, E j^2)=((2^(n+2):ℕ):ℝ)*(∑ l : PathLabel n, (u l)^2) := by
  intro E
  have hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  have htrace : (pathHamiltonian u).trace=0 := by
    rw [pathHamiltonian_eq_sum,Matrix.trace_sum]
    exact Finset.sum_eq_zero fun l _ => by rw [Matrix.trace_smul,finitePauliMatrix_trace_eq_zero_of_ne_identity _ (pathWord_ne_identity l),smul_zero]
  have ht := trace_pow_eq_sum_eigenvalues_pow hH 1
  simp only [pow_one,htrace] at ht
  constructor
  · simpa only [Complex.zero_re,Complex.re_sum,Complex.ofReal_re] using (congrArg Complex.re ht).symm
  · rw [show (∑ j, E j^2)=((pathHamiltonian u)^2).trace.re from sum_sq_eigenvalues_eq_trace_sq_re hH]
    have hs := hsNormSq_matrix_eq_trace (pathHamiltonian u)
    rw [hH.eq,←sq] at hs
    rw [←hs,Complex.ofReal_re,pathHamiltonian_eq_sum,hsNormSq_pauliCombination pathWord_injective]
    push_cast
    rfl

#print axioms centered_gap_mass
#print axioms path_spectral_moments
end
end GaloisForLFunctions.HTGeometry.FluxOccupation
