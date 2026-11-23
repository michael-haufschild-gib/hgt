import GaloisForLFunctions.HTGeometry.CharFunCubicMoments

/-! # Gaussian comparison for the normalized trace of one centered spectral packet -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

/-- The normalized characteristic function of a finite energy list. -/
def energyCharacteristic {I : Type*} [Fintype I] (E : I → ℝ) (t : ℝ) : ℂ :=
  (Fintype.card I : ℂ)⁻¹ * ∑ i, Complex.exp (((t*E i:ℝ):ℂ)*Complex.I)

private theorem scalar_gaussian_error {v A : ℝ} (hv : 0≤v) (hA : 0≤A) (hvar : v≤A^2) (t : ℝ) :
    |exp (-(t^2*v/2))-(1-t^2*v/2)| ≤ |t|^3*A*v := by
  let x := t^2*v/2
  have hx : 0≤x := by dsimp only [x]; positivity
  have hlo : 1-x ≤ exp (-x) := by simpa only [sub_eq_add_neg,add_comm] using add_one_le_exp (-x)
  have hi : exp (-x)*(1+x) ≤ 1 := by
    rw [exp_neg,←div_eq_inv_mul,div_le_one (exp_pos x)]
    exact (add_comm ..).le.trans (add_one_le_exp x)
  have hlin : exp (-x) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  change |exp (-x)-(1-x)| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hsq : exp (-x)-(1-x) ≤ x^2 := by
    nlinarith only [hi,mul_le_mul_of_nonneg_right hlo hx]
  have ht : |t|^2 = t^2 := sq_abs _
  by_cases h : 1≤ |t| *A
  · have hm := mul_le_mul_of_nonneg_right h hx
    dsimp only [x] at *
    nlinarith only [hm,hlin,ht,mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) 3) hA) hv,
      congrArg (fun z => z* |t| *A*v) ht]
  · have hb : t^2*v ≤ |t| *A := by
      calc t^2*v ≤ |t|^2*A^2 := by rw [ht]; exact mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
           _ = (|t| *A)*(|t| *A) := by ring
           _ ≤ |t| *A := mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hA) (le_of_not_ge h)
    have hm := mul_le_mul_of_nonneg_right hb hx
    dsimp only [x] at *
    nlinarith only [hsq,hm,sq_nonneg (t^2*v),mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) 3) hA) hv,
      congrArg (fun z => z* |t| *A*v) ht]

/-- For a centered finite spectral list of variance v and radius at most A,
the third-order error in replacing its characteristic function by the Gaussian
one is at most three times |t|³ A v. -/
theorem packet_gaussian_error {I : Type*} [Fintype I] [Nonempty I] (E : I → ℝ)
    {v A : ℝ} (hv : 0≤v) (hA : 0≤A) (hvar : v≤A^2)
    (h₁ : ∑ i, E i=0) (h₂ : ∑ i, E i^2=(Fintype.card I:ℝ)*v)
    (hb : ∀ i, |E i| ≤ A) (t : ℝ) :
    ‖energyCharacteristic E t-(exp (-(t^2*v/2)):ℂ)‖ ≤ 3* |t|^3*A*v := by
  let d := Fintype.card I
  have hd : (0:ℝ)<d := Nat.cast_pos.mpr Fintype.card_pos
  have hd' : (d:ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  let X (i : I) : ℂ := Complex.exp (((t*E i:ℝ):ℂ)*Complex.I)
  let Q (i : I) : ℂ := 1+((t*E i:ℝ):ℂ)*Complex.I-((t*E i:ℝ):ℂ)^2/2
  have hQ : ∑ i, Q i=(d:ℂ)*((1-t^2*v/2:ℝ):ℂ) := by
    have h₁' : ∑ i, (E i:ℂ)=0 := by exact_mod_cast h₁
    have h₂' : ∑ i, (E i:ℂ)^2=(d:ℂ)*(v:ℂ) := by exact_mod_cast h₂
    simp only [Q,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_div,
      Complex.ofReal_ofNat,Complex.ofReal_pow,sum_sub_distrib,sum_add_distrib,sum_const,
      card_univ,nsmul_eq_mul,mul_one,←Finset.sum_mul,←Finset.mul_sum,mul_pow,Finset.sum_div]
    rw [h₁',h₂']
    dsimp only [d]
    ring
  have hh : ∑ i, ‖X i-Q i‖ ≤ (2* |t|^3*A)*((d:ℝ)*v) := by
    rw [←h₂,Finset.mul_sum]
    apply sum_le_sum
    intro i _
    have h := norm_cexp_mul_I_sub_quadratic_le (t*E i)
    have he : |E i|^3 ≤ A*E i^2 := by
      rw [pow_succ,sq_abs,mul_comm]
      exact mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)
    rw [abs_mul,mul_pow] at h
    calc ‖X i-Q i‖ ≤ 2*(|t|^3* |E i|^3) := h
         _ = (2* |t|^3)* |E i|^3 := (mul_assoc ..).symm
         _ ≤ _ := (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring)
  have hcen : energyCharacteristic E t-((1-t^2*v/2:ℝ):ℂ)=(d:ℂ)⁻¹*∑ i, (X i-Q i) := by
    rw [sum_sub_distrib,hQ,mul_sub,←mul_assoc,inv_mul_cancel₀ hd',one_mul]
    rfl
  have hc : ‖energyCharacteristic E t-((1-t^2*v/2:ℝ):ℂ)‖ ≤ 2* |t|^3*A*v := by
    rw [hcen,norm_mul,norm_inv,Complex.norm_natCast,←div_eq_inv_mul,div_le_iff₀ hd]
    exact (norm_sum_le _ _).trans (hh.trans_eq (by ring))
  have hg := scalar_gaussian_error hv hA hvar t
  have h := norm_sub_le_norm_sub_add_norm_sub (energyCharacteristic E t)
    ((1-t^2*v/2:ℝ):ℂ) (exp (-(t^2*v/2)):ℂ)
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm (1-_)] at h
  linarith only [h,hc,hg]

#print axioms packet_gaussian_error
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
