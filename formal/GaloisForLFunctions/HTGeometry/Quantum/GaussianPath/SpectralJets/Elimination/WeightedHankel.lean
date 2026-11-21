import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.TraceGram
import GaloisForLFunctions.HTGeometry.ConstitutiveThreeRealizationPacket

/-! # Elimination of one root variable by a weighted Hankel determinant -/
open Matrix MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι : Type*} [Fintype ι] {D : ℕ}

/-- Product over a full root packet, multiplied by its discriminant. -/
def rootProduct (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (b : MvPolynomial (Option ι) ℂ) : MvPolynomial ι ℂ :=
  (Matrix.of fun i j : Fin D => spectralSum M (b*X none^(i.val+j.val))).det

theorem rootProduct_degree (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (b : MvPolynomial (Option ι) ℂ) :
    (rootProduct M b).totalDegree ≤ D*(b.totalDegree+2*D) := by
  apply determinant_degree
  intro i j
  apply (spectralSum_degree M hM _).trans
  apply (totalDegree_mul _ _).trans
  apply Nat.add_le_add_left
  have hp := totalDegree_pow (X (R := ℂ) (none : Option ι)) (i.val+j.val)
  rw [totalDegree_X,mul_one] at hp
  exact hp.trans (by have hi := i.isLt; have hj := j.isLt; omega)

/-- Evaluation equals the ordinary product times a factor independent of b. -/
theorem eval_rootProduct (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι → ℂ) (E : Fin D → ℂ)
    (ht : ∀ k : ℕ, eval x (M^k).trace = ∑ j, E j^k) (b : MvPolynomial (Option ι) ℂ) :
    eval x (rootProduct M b) = (Matrix.vandermonde E).det^2 *
      ∏ j, eval (fun o : Option ι => o.elim (E j) x) b := by
  let v (j : Fin D) := eval (fun o : Option ι => o.elim (E j) x) b
  rw [rootProduct,RingHom.map_det,← det_packetHankelSq E v]
  apply congrArg Matrix.det
  ext i j
  change eval₂Hom (RingHom.id ℂ) x (spectralSum M (b*X none^(i.val+j.val))) = ∑ a, v a*E a^(i.val+j.val)
  have h := eval_spectralSum M (RingHom.id ℂ) x E ht (b*X none^(i.val+j.val))
  simpa only [eval₂_id,map_mul,map_pow,eval_X,Option.elim_none,v] using h

/-- At a simple spectrum, elimination records precisely the existence of a
root where the original polynomial vanishes. -/
theorem eval_rootProduct_eq_zero_iff (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι → ℂ) (E : Fin D → ℂ) (hi : Function.Injective E)
    (ht : ∀ k : ℕ, eval x (M^k).trace = ∑ j, E j^k) (b : MvPolynomial (Option ι) ℂ) :
    eval x (rootProduct M b) = 0 ↔ ∃ j, eval (fun o : Option ι => o.elim (E j) x) b = 0 := by
  classical
  rw [eval_rootProduct M x E ht]
  have hV := pow_ne_zero 2 (Matrix.det_vandermonde_ne_zero_iff.mpr hi)
  simp [hV,Finset.prod_eq_zero_iff]

#print axioms rootProduct_degree
#print axioms eval_rootProduct_eq_zero_iff
end
end GaloisForLFunctions.HTGeometry.SpectralJets
