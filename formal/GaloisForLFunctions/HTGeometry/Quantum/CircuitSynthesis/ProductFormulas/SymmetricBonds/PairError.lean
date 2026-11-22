import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.Conjugation

/-! # Symmetric product error from two nested commutators -/
open NormedSpace
namespace GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
noncomputable section
open LocalPatches
variable {R : Type*} [CStarAlgebra R]
local instance : NormedAlgebra ℚ R := .restrictScalars ℚ ℂ R

/-- Conjugating the derivative defect of the symmetric product exposes
two linear terms which cancel exactly. No small-generator restriction is needed. -/
theorem symmetric_pair_error (a b : R) (ha : a∈skewAdjoint R) (hb : b∈skewAdjoint R) (t : ℝ) (ht : 0≤t) :
    ‖exp (t • a)*exp (t • b)*exp (t • a)-exp (t • (a+b+a))‖ ≤
      t^3*(‖bracketStep a (bracketStep a b)‖+‖bracketStep (-b) (bracketStep (-b) a)‖) := by
  let K := a+b+a
  let A (s : ℝ) := exp (s • a)
  let B (s : ℝ) := exp (s • b)
  let P (s : ℝ) := exp (s • (-K))
  let D (s : ℝ) := (conjugate (-b) a s-a)-(conjugate a b s-b)
  let f (s : ℝ) := P s*A s*B s*A s
  have heq : bracketStep (-b) a=bracketStep a b := by unfold bracketStep; noncomm_ring
  let M := ‖bracketStep a (bracketStep a b)‖+‖bracketStep (-b) (bracketStep (-b) a)‖
  have hM : 0≤M := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hD (s : ℝ) (hs : 0≤s) : ‖D s‖≤s^2*M := by
    have he : D s = (conjugate (-b) a s-a-s • bracketStep (-b) a) -
        (conjugate a b s-b-s • bracketStep a b) := by rw [heq]; dsimp only [D]; abel
    rw [he]
    apply (norm_sub_le ..).trans
    exact (add_le_add (conjugate_remainder (-b) a ((skewAdjoint R).neg_mem hb) s hs)
      (conjugate_remainder a b ha s hs)).trans_eq (by dsimp only [M]; ring)
  have factor (s : ℝ) : A s*D s*B s=A s*B s*a-a*A s*B s-b*A s*B s+A s*b*B s := by
    have h₁ : A s*conjugate a b s=b*A s := by
      dsimp only [A,conjugate]; rw [←mul_assoc,←mul_assoc,flow_inverse,one_mul]
    have h₂ : conjugate (-b) a s*B s=B s*a := by
      have h := flow_inverse (-b) s
      rw [neg_neg] at h
      dsimp only [B,conjugate,neg_neg]; rw [mul_assoc _ (exp (s • (-b))),h,mul_one]
    have hc : Commute (A s) a := ((Commute.refl a).smul_left s).exp_left
    calc _ = A s*(conjugate (-b) a s*B s) - (A s*a)*B s - (A s*conjugate a b s)*B s + A s*b*B s := by
                dsimp only [D]; noncomm_ring
         _ = _ := by rw [h₁,h₂,hc.eq,mul_assoc (A s) (B s) a]
  let g (s : ℝ) := P s*(A s*D s*B s)*A s
  have hd (s : ℝ) : HasDerivAt f (g s) s := by
    have h := (((hasDerivAt_exp_smul_const (-K) s).fun_mul (hasDerivAt_exp_smul_const' a s)).fun_mul
      (hasDerivAt_exp_smul_const' b s)).fun_mul (hasDerivAt_exp_smul_const' a s)
    convert h using 1
    dsimp only [g]; rw [factor]; dsimp only [A,B,P,K]; noncomm_ring
  have hK : K∈skewAdjoint R := (skewAdjoint R).add_mem ((skewAdjoint R).add_mem ha hb) ha
  have hbound (s : ℝ) (hs : s∈Set.Ico 0 t) : ‖g s‖ ≤ t^2*M := by
    dsimp only [g]
    rw [CStarRing.norm_mul_mem_unitary _ (flow_unitary _ ha s),
      CStarRing.norm_mem_unitary_mul _ (flow_unitary _ ((skewAdjoint R).neg_mem hK) s),
      CStarRing.norm_mul_mem_unitary _ (flow_unitary _ hb s),CStarRing.norm_mem_unitary_mul _ (flow_unitary _ ha s)]
    exact (hD s hs.1).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.1 hs.2.le _) hM)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (fun s _ => (hd s).hasDerivWithinAt) hbound t ⟨ht,le_rfl⟩
  have hzero : f 0=1 := by simp [f,A,B,P]
  rw [hzero,sub_zero] at h
  have he : exp (t • K)*(f t-1)=A t*B t*A t-exp (t • K) := by
    simp only [f,P,mul_sub,mul_one,←mul_assoc,flow_inverse,one_mul]
  rw [←he,CStarRing.norm_mem_unitary_mul _ (flow_unitary _ hK t)]
  exact h.trans_eq (by change t^2*M*t=t^3*M; ring)

#print axioms symmetric_pair_error
end
end GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
