import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.DisconnectedSpectra.Rectangle
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.DisconnectedSpectra.ProductPacket
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # No nonzero Gaussian evolution is a tensor product in any basis -/
open MeasureTheory Matrix
open scoped Kronecker
namespace GaloisForLFunctions.HTGeometry.DisconnectedSpectra
noncomputable section

private def energyPhase (t E : ℝ) : ℂ := Complex.exp (-(Complex.I*((t:ℂ)*(E:ℂ))))

private theorem mixed_gap_zero {a b c d t : ℝ}
    (h : energyPhase t a*energyPhase t d=energyPhase t b*energyPhase t c) :
    (((((a-b)-(c-d))*t/(2*Real.pi)):ℝ) : UnitAddCircle)=0 := by
  simp only [energyPhase,←Complex.exp_add] at h
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hI := congrArg Complex.im hk
  simp only [Complex.add_im,Complex.neg_im,Complex.I_mul_im,Complex.mul_im,Complex.mul_re,Complex.intCast_re,
    Complex.intCast_im,Complex.ofReal_re,Complex.ofReal_im,Complex.ofNat_re,Complex.ofNat_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,add_zero,zero_add,sub_zero,mul_one] at hI
  apply (AddCircle.coe_eq_zero_iff (p:=(1:ℝ))).mpr
  refine ⟨-k,?_⟩
  rw [zsmul_eq_mul,Int.cast_neg,mul_one,eq_div_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
  linarith only [hI]

/-- The full Gaussian spectrum excludes exact product matrices even
after arbitrary unitary conjugation and relabelling. This holds at every
nonzero time and allows both tensor factors to be chosen at that time. -/
theorem gaussian_no_tensor_product :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ m n : ℕ, 2 ≤ m → 3 ≤ n → ∀ e : Fin m × Fin n ≃ (Fin (k+3)→Bool),
      ∀ t : ℝ, t≠0 → ∀ (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
        (V : Matrix.unitaryGroup (Fin m × Fin n) ℂ),
        A ⊗ₖ B ≠ V.val*diagonal (fun i => energyPhase t (E (e i)))*star V.val := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω k
  intro E m n hm hn e t ht A B V he
  obtain ⟨a,b,p,hp⟩ := tensor_product_packet A B _ V he
  let F := E ∘ (p.trans e)
  let x : Fin m := ⟨0,by omega⟩
  let y : Fin m := ⟨1,by omega⟩
  let o : Fin n := ⟨0,by omega⟩
  let g (j : Fin n) := F (x,j)-F (y,j)
  have hxy : x≠y := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  have hfreq := row_gap_independent F ((hω k).comp_equiv (p.trans e)) hxy
  have hmp : MaximallyProjectiveEnergy g := fun w _ hw => hfreq w hw
  apply ht (hmp.no_nonzeroExactAnchoredReturn o (by simpa only [Fintype.card_fin] using hn) t ?_)
  funext j
  apply mixed_gap_zero
  change energyPhase t (E (e (p (x,j.val))))*energyPhase t (E (e (p (y,o))))=
    energyPhase t (E (e (p (y,j.val))))*energyPhase t (E (e (p (x,o))))
  rw [hp,hp,hp,hp]
  ring

#print axioms gaussian_no_tensor_product
end
end GaloisForLFunctions.HTGeometry.DisconnectedSpectra
