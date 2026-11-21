import GaloisForLFunctions.HTGeometry.HypercubeWalshDiagonalisation
import GaloisForLFunctions.HTGeometry.PauliTwoLocalLabels
import GaloisForLFunctions.HTGeometry.PathDiagonalCarrier

/-! # A simple transverse endpoint preserving global spin reversal -/
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

/-- Onsite X fields with base-three weights. -/
def transverseShell (n : ℕ) : PathShell n := WithLp.toLp 2 fun l => match l with
  | .inl (i,a) => if a=0 then (3:ℝ)^i.val else 0
  | .inr _ => 0

/-- The onsite Pauli generator acts by the weighted single-spin flips. -/
theorem transverse_matrix (n : ℕ) :
    pathHamiltonian (transverseShell n) = Walsh.transverseOnly (fun i => ((3:ℝ)^i.val:ℂ)) := by
  have hb (e : Fin (n+1)) (ab : Fin 3 × Fin 3) : transverseShell n (.inr (e,ab))=0 := rfl
  have ha (i : Fin (n+2)) (a : Fin 3) :
      transverseShell n (.inl (i,a)) = if a=0 then (3:ℝ)^i.val else 0 := rfl
  ext s t
  simp only [pathHamiltonian,edgePart,hb,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,add_zero,
    onsitePart,Fintype.sum_prod_type,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Walsh.transverseOnly,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (0:Fin 3)]
  · change ((transverseShell n (.inl (i,0)):ℝ):ℂ)*finitePauliMatrix (pauliXLabel i) s t = _
    rw [ha,if_pos rfl,finitePauliMatrix_pauliXLabel]
    split <;> simp
  · intro a _ hne
    rw [ha,if_neg hne,Complex.ofReal_zero,zero_mul]
  · simp

/-- At the transverse endpoint all 2ᴺ levels are simple. Conjugation by
the Walsh transform gives the diagonal signed sums of the field weights. -/
theorem transverse_simple (n : ℕ) : (pathHamiltonian (transverseShell n)).charpoly.Separable := by
  let w (i : Fin (n+2)) := (3:ℝ)^i.val
  let E (s : Fin (n+2) → Bool) := (Walsh.transverseEnergy w s:ℂ)
  let W := Walsh.walshMatrix (n+2)
  let H := pathHamiltonian (transverseShell n)
  have hW : W*W=1 := Walsh.walshMatrix_mul_self _
  have he : H*W = W*diagonal E := by
    dsimp only [H]
    rw [transverse_matrix]
    simpa only [W,E,w,Complex.ofReal_pow] using Walsh.transverseOnly_mul_walsh w
  have hH : H=W*diagonal E*W := by rw [←he,mul_assoc,hW,mul_one]
  change H.charpoly.Separable
  rw [hH,Matrix.charpoly_mul_comm (W*diagonal E) W,←mul_assoc,hW,one_mul,Matrix.charpoly_diagonal]
  apply Polynomial.separable_prod_X_sub_C_iff.mpr
  intro s t hst
  by_contra hn
  have h := Walsh.transverseEnergy_separated (w := fun i => (3:ℝ)^i) (fun _ => by positivity)
    (fun i => by simp only [pow_succ,mul_comm (3:ℝ),le_refl]) s t hn
  have h' : Walsh.transverseEnergy w s = Walsh.transverseEnergy w t := Complex.ofReal_inj.mp hst
  change (3:ℝ)^0 ≤ |Walsh.transverseEnergy w s-Walsh.transverseEnergy w t| at h
  rw [h',sub_self,abs_zero,pow_zero] at h
  exact one_ne_zero (le_antisymm h zero_le_one)

#print axioms transverse_simple
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
