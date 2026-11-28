import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! # Four rotations about involutions implement a Lie bracket -/

open Matrix Complex
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Pulses
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

private theorem rotate_dist (P : Mat I) (hP : ‖P‖≤1) {a b : ℝ}
    (hb : 0≤b) (ha : |a-1|≤b) :
    ‖(a:ℂ) • (1:Mat I)+(-Complex.I*(b:ℂ)) • P-1‖≤2*b := by
  have he : (a:ℂ) • (1:Mat I)+(-Complex.I*(b:ℂ)) • P-1=
      ((a:ℂ)-1) • (1:Mat I)+(-Complex.I*(b:ℂ)) • P := by
    rw [sub_smul,one_smul]; abel
  rw [he]
  apply (norm_add_le ..).trans
  rw [norm_smul,norm_smul,norm_one,mul_one,norm_mul,norm_neg,Complex.norm_I,one_mul,
    ←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hb]
  linarith only [ha,mul_le_mul_of_nonneg_left hP hb]

/-- The exact difference of the two pulse orders is $b^2[Q,P]$.
Multiplying by the inverse pulses changes this tangent by at most $8b^3$. -/
theorem commutator_error (A B : unitary (Mat I)) (P Q : Mat I)
    (hp : ‖P‖≤1) (hq : ‖Q‖≤1) {a b : ℝ} (hb : 0≤b) (ha : |a-1|≤b)
    (hA : A.val=(a:ℂ) • 1+(-Complex.I*(b:ℂ)) • P)
    (hB : B.val=(a:ℂ) • 1+(-Complex.I*(b:ℂ)) • Q) :
    ‖(A*B*A⁻¹*B⁻¹).val-(1+(b^2:ℝ) • (Q*P-P*Q))‖≤8*b^3 := by
  let S := Q*P-P*Q
  have hs : ‖S‖≤2 := by
    have h₁ := (norm_mul_le Q P).trans (mul_le_mul hq hp (norm_nonneg _) zero_le_one)
    have h₂ := (norm_mul_le P Q).trans (mul_le_mul hp hq (norm_nonneg _) zero_le_one)
    exact (norm_sub_le ..).trans (by linarith)
  have hid : A.val*B.val-B.val*A.val=(b^2:ℝ) • S := by
    rw [hA,hB]
    simp only [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,smul_smul,one_mul,mul_one]
    have hcoef : (-Complex.I*(b:ℂ))*(-Complex.I*(b:ℂ))= -((b:ℂ)^2) := by
      linear_combination (norm := ring) (b:ℂ)^2*Complex.I_mul_I
    simp only [hcoef,S,←Complex.coe_smul,Complex.ofReal_pow,smul_sub,neg_smul]
    rw [mul_comm (a:ℂ) (-Complex.I*(b:ℂ))]
    abel
  let V := A⁻¹*B⁻¹
  have hV : ‖V.val-1‖≤4*b := by
    have hz (X : unitary (Mat I)) : ‖(X⁻¹).val-1‖=‖X.val-1‖ := by
      change ‖star X.val-1‖=_
      rw [←star_one (R:=Mat I),←star_sub,norm_star,star_one]
    have he : V.val-1=((A⁻¹).val-1)*(B⁻¹).val+((B⁻¹).val-1) := by
      change (A⁻¹).val*(B⁻¹).val-1=_
      noncomm_ring
    rw [he]
    apply (norm_add_le ..).trans
    rw [CStarRing.norm_mul_mem_unitary _ (B⁻¹).2,hz,hz,hA,hB]
    linarith only [rotate_dist P hp hb ha,rotate_dist Q hq hb ha]
  have hz : B.val*A.val*V.val=1 := by
    change ((B*A)*(A⁻¹*B⁻¹)).val=1
    simp only [mul_assoc,mul_inv_cancel_left, mul_inv_cancel,OneMemClass.coe_one]
  have he : (A*B*A⁻¹*B⁻¹).val-(1+(b^2:ℝ) • S)=
      ((b^2:ℝ) • S)*(V.val-1) := by
    change A.val*B.val*(A⁻¹).val*(B⁻¹).val-_=_
    rw [mul_assoc (A.val*B.val)]
    change A.val*B.val*V.val-_=_
    conv_lhs => rw [←hz]
    rw [←hid]
    noncomm_ring
  rw [he]
  apply (norm_mul_le ..).trans
  rw [norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (b^2*2)*(4*b) := mul_le_mul (mul_le_mul_of_nonneg_left hs (sq_nonneg _))
      hV (norm_nonneg _) (by positivity)
    _ = _ := by ring

#print axioms commutator_error
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Pulses
