import GaloisForLFunctions.RHTower.ThetaCuspRatioIntegerReflections
import GaloisForLFunctions.RHTower.ThetaCuspRatioSourceIncidence
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

theorem integerReflection_eq (n : ℕ) :
    integerReflection n=C ((6:ℂ)^(n+2))*reflectionJet n := by
  unfold integerReflection reflectionJet
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i≤n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have he : i+1+(n-i+1)=n+2 := by omega
  have hp : (6:ℂ)^(i+1)*(6:ℂ)^(n-i+1)=(6:ℂ)^(n+2) := by
    rw [← pow_add,he]
  rw [integerJet_eq,integerJet_eq]
  apply MvPolynomial.funext
  intro v
  simp only [map_mul,eval_C,map_pow,map_neg,map_one,map_natCast]
  rw [← hp]
  ring

theorem integerSignedMoment_eq (r : ℕ) :
    integerSignedMoment r=C ((6:ℂ)^(2*r+2))*signedMoment r := by
  unfold integerSignedMoment signedMoment
  rw [integerReflection_eq]
  apply MvPolynomial.funext
  intro v
  simp only [map_mul,eval_C,map_pow,map_neg,map_one]
  ring

theorem integerThirdMinor_eq : integerThirdMinor=C ((6:ℂ)^24)*thirdMinor := by
  unfold integerThirdMinor thirdMinor
  simp_rw [integerSignedMoment_eq]
  apply MvPolynomial.funext
  intro v
  norm_num only [map_add,map_mul,map_sub,map_pow,eval_C,map_ofNat]
  ring

private theorem integerField_eq (i : Coord) : integerField i=6*field i := by
  apply MvPolynomial.funext
  intro v
  have hq := sourceJet_zero_eval v
  simp only [sourceJet,map_sub,eval_X] at hq
  have hq' := sub_right_inj.mp hq
  cases i <;> norm_num [integerField,field,tau,hq'] <;> ring

theorem integerLie_eq (P : Poly) : integerLie P=6*lie P := by
  unfold integerLie lie
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integerField_eq]
  ring

private theorem lie_Cmul (c : ℂ) (P : Poly) : lie (C c*P)=C c*lie P := by
  simp [lie,pderiv_mul,pderiv_C,Finset.mul_sum,mul_assoc]

theorem integerThirdSlope_eq : integerThirdSlope=C ((6:ℂ)^26)*thirdSlope := by
  unfold integerThirdSlope thirdSlope
  simp only [integerJet_eq,integerThirdMinor_eq,integerLie_eq,lie_Cmul]
  apply MvPolynomial.funext
  intro v
  norm_num only [map_sub,map_mul,map_pow,eval_C,map_ofNat]
  ring

theorem integerSlope_partial_eq (v : Coord → ℂ) (i : Coord) :
    eval v (pderiv i integerThirdSlope)=(6:ℂ)^26*eval v (pderiv i thirdSlope) := by
  rw [integerThirdSlope_eq]
  simp [pderiv_mul,pderiv_C]

end
end HTGeometry.ThetaRatioSource
