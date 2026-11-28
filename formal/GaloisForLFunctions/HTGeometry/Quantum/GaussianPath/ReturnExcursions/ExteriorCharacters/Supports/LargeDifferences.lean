import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.Correlation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.HalfDegree
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.PrincipalWeights
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DistinctSubsets

/-! # Macroscopic energy differences in a half-degree character -/

open Matrix Finset Filter
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Coefficient of the oscillatory term for one subset, including its
energy phase and the principal minor of the circuit's adjoint. -/
def amplitude (A : Matrix I I ℂ) (p : I → ℂ) (S : Finset I) : ℂ :=
  (A.submatrix (Subtype.val : S → I) Subtype.val).det*∏ i ∈ S, p i

/-- At a half-degree character of the size forced by a physical fit,
the signed contribution from pairs differing on more than a quarter of
all levels already exceeds half the full lower bound. -/
theorem large_differences (n : ℕ) (hn : 2^n*(3/2:ℝ)^(4*n) ≤
    (1/2:ℝ)*((4*n).choose (2*n):ℝ)*(199/200)^(4*n))
    (hd : Fintype.card I=4*n) (W : unitary (Matrix I I ℂ)) (p : I → ℂ) (hp : ∀ i, ‖p i‖=1)
    (h : ((4*n).choose (2*n):ℝ)*(199/200)^(2*n)≤‖subsetCharacter W.val p (2*n)‖) :
    (1/2:ℝ)*((4*n).choose (2*n):ℝ)^2*(199/200)^(4*n) ≤
      farCorrelation (univ.powersetCard (2*n)) (amplitude W.val p) n := by
  let F := (univ : Finset I).powersetCard (2*n)
  let B : ℝ := (4*n).choose (2*n)
  have hc : (F.card:ℝ)=B := by simp [F,B,hd]
  have hB : 0≤B := Nat.cast_nonneg _
  have ha (S : Finset I) : ‖amplitude W.val p S‖≤1 := by
    simpa only [amplitude,norm_mul,norm_prod,hp,prod_const_one,mul_one] using
      (principal_weight_le W S)
  have ht := far_correlation_floor F (amplitude W.val p) (fun S _ => ha S) n
  rw [hc,hd] at ht
  have hs := pow_le_pow_left₀ (mul_nonneg hB (by positivity : (0:ℝ)≤(199/200)^(2*n))) h 2
  rw [mul_pow,←pow_mul,show 2*n*2=4*n by omega] at hs
  change B^2*(199/200)^(4*n)≤‖∑ S ∈ F, amplitude W.val p S‖^2 at hs
  have hprice := mul_le_mul_of_nonneg_left hn hB
  change 1/2*B^2*(199/200)^(4*n)≤_
  apply le_trans _ ht
  linarith only [hs,hprice]

#print axioms large_differences
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
