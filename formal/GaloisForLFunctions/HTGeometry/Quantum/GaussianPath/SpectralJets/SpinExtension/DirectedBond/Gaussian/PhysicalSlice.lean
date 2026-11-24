import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.PauliChain
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.Labels

/-! # The sparse spectral witness as an affine slice of physical Pauli coefficients -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

private theorem onsite_mem (n b : ℕ) (q : Fin 3) (r : ℝ) :
    ((r:ℂ)*height b) • lastPauli n q ∈ pauliChainSpan (n+1) := by
  let c := r*((b:ℝ)+1)
  have he : (c:ℂ)=(r:ℂ)*height b := by simp [c,height]
  have hs : (c:ℂ) • lastPauli n q = c • lastPauli n q := by
    ext i j
    exact Complex.real_smul.symm
  rw [←he,hs]
  exact (pauliChainSpan _).smul_mem c (pauliSiteSpan_le_pauliChainSpan _ _ (lastPauli_mem n q))

private theorem product_mem {n : ℕ} (H : Register n) (hH : H∈pauliChainSpan n) (b : ℕ) :
    onRegister n (physical H 0 ((3/5)*height b) ((4/5)*height b)) ∈ pauliChainSpan (n+1) := by
  rw [onRegister_physical,map_zero,add_zero]
  have hz := onsite_mem n b 2 (3/5)
  have hx := onsite_mem n b 0 (4/5)
  push_cast at hz hx
  exact (pauliChainSpan _).add_mem ((pauliChainSpan _).add_mem (couple_one_mem_pauliChainSpan hH) hz) hx

theorem background_zero_mem (n : ℕ) (B : Fin (n+1)→ℕ) : background n B 0∈pauliChainSpan (n+1) := by
  induction n with
  | zero => exact product_mem 0 (Submodule.zero_mem _) _
  | succ n ih =>
    simp only [background,map_zero,baseNext,Prod.fst_zero,Prod.snd_zero,zero_smul]
    exact product_mem _ (ih _) _

private theorem couple_complex_smul (n : ℕ) (B : Matrix Bool Bool ℂ) (c : ℂ) (A : Register n) :
    coupleSnoc n B (c • A)=c • coupleSnoc n B A := by
  ext i j
  simp [layerMatrixCoupling,mul_assoc]

private def edgeSum (n : ℕ) (p : Controls n) := ∑ i, p i • finitePauliMatrix (edgeLabel n i).1

private theorem edgeSum_step (n : ℕ) (p : Controls (n+1)) :
    edgeSum (n+1) p = coupleSnoc (n+1) (boolPauliOption none) (edgeSum n (splitControls n p).1) +
      (splitControls n p).2 • coupleSnoc (n+1) (finiteQubitPauli 2) (lastPauli n 0) := by
  rw [edgeSum,Fin.sum_univ_castSucc]
  unfold edgeSum
  rw [map_sum]
  simp only [edgeLabel,Fin.lastCases_castSucc,Fin.lastCases_last,matrix_liftedLabel,matrix_lastBondLabel,couple_complex_smul]
  rfl

private theorem affine_background (n : ℕ) (B : Fin (n+1)→ℕ) (p : Controls n) :
    background n B p=background n B 0+edgeSum n p := by
  induction n with
  | zero => simp [background,edgeSum]
  | succ n ih =>
    change onRegister (n+1) (baseNext _ _ _ (splitControls n p)) =
      onRegister (n+1) (baseNext _ _ _ (splitControls n 0))+edgeSum (n+1) p
    simp only [baseNext,onRegister_physical,map_zero,Prod.fst_zero,Prod.snd_zero,zero_smul,add_zero]
    rw [ih _ (splitControls n p).1,map_add,couple_complex_smul,edgeSum_step]
    abel

/-- All bond and endpoint displacements are literal numbered Pauli directions
at the fixed product background. -/
theorem chain_affine (n : ℕ) (B : Fin (n+1)→ℕ) (p : Controls (n+1)) :
    chain B p=background n B 0+∑ i, p i • finitePauliMatrix (fieldLabels n i).1 := by
  rw [chain,affine_background,Fin.sum_univ_castSucc]
  simp only [fieldLabels,Fin.snoc_castSucc,Fin.snoc_last,matrix_terminalLabel,edgeSum]
  exact add_assoc _ _ _

#print axioms chain_affine
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
