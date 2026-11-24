import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.PauliChain

/-! # Linear dependence of the product background on its onsite splittings -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

private def siteAxis (n : ℕ) := (3/5:ℝ) • lastPauli n 2+(4/5:ℝ) • lastPauli n 0

private theorem siteAxis_mem (n : ℕ) : siteAxis n∈pauliChainSpan (n+1) := by
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (pauliSiteSpan_le_pauliChainSpan _ _ (lastPauli_mem n 2))
  · exact Submodule.smul_mem _ _ (pauliSiteSpan_le_pauliChainSpan _ _ (lastPauli_mem n 0))

/-- The tilted axis supported at one site of the full register. -/
def siteTerm : (n : ℕ) → Fin (n+1) → Register (n+1)
  | 0,_ => siteAxis 0
  | n+1,s => Fin.lastCases (siteAxis (n+1))
      (fun i => coupleSnoc (n+1) (boolPauliOption none) (siteTerm n i)) s

theorem siteTerm_mem (n : ℕ) (s : Fin (n+1)) : siteTerm n s∈pauliChainSpan (n+1) := by
  induction n with
  | zero => exact siteAxis_mem _
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) s
    · simpa only [siteTerm,Fin.lastCases_last] using siteAxis_mem (n+1)
    · simpa only [siteTerm,Fin.lastCases_castSucc] using couple_one_mem_pauliChainSpan (ih i)

private theorem append_site (n : ℕ) (H : Register n) (b : ℕ) :
    onRegister n (physical H 0 ((3/5)*height b) ((4/5)*height b)) =
      coupleSnoc n (boolPauliOption none) H+((b+1:ℕ):ℝ) • siteAxis n := by
  rw [onRegister_physical,map_zero,add_zero,siteAxis,smul_add,smul_smul,smul_smul,add_assoc]
  have hr (c : ℝ) (A : Register (n+1)) : c • A=(c:ℂ) • A := by
    ext i j; exact Complex.real_smul
  simp only [hr,Complex.ofReal_mul,Nat.cast_add,Nat.cast_one,Complex.ofReal_add,Complex.ofReal_natCast,
    Complex.ofReal_one,Complex.ofReal_div,Complex.ofReal_ofNat,height]
  congr 2 <;> congr 1 <;> ring

/-- Only the local field strengths enter the constant part of the pencil.
Each physical coefficient lift can therefore be chosen affine in the strengths. -/
theorem product_site_sum (n : ℕ) (B : Fin (n+1)→ℕ) :
    background n B 0=∑ s, ((B s+1:ℕ):ℝ) • siteTerm n s := by
  induction n with
  | zero => simp only [background,append_site,map_zero,zero_add,Fin.sum_univ_one,siteTerm]
  | succ n ih =>
    rw [background,map_zero,baseNext]
    simp only [Prod.fst_zero,Prod.snd_zero,zero_smul,append_site]
    rw [ih,map_sum,Fin.sum_univ_castSucc]
    simp only [map_smul,siteTerm,Fin.lastCases_castSucc,Fin.lastCases_last]

#print axioms product_site_sum
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
