import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioSquareSlopeFactor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioInfinitySlope
import Mathlib.RingTheory.Coprime.Lemmas
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

theorem polynomial_ext_clock_nonzero {P Q : Poly}
    (he : ∀ h r t : ℂ, h≠0 → eval (basePoint h r t) P=eval (basePoint h r t) Q) : P=Q := by
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero Coord.U)
  apply MvPolynomial.funext
  intro v
  simp only [map_mul,eval_X]
  by_cases hv:v .U=0
  · simp [hv]
  · have hb : basePoint (v .U) (v .K) (v .J)=v := by funext i; cases i <;> rfl
    rw [←hb]
    exact congrArg (fun z : ℂ => v .U*z) (he _ _ _ hv)

theorem sourcePolynomial_regularization (P : Poly) :
    ∃ n : ℕ, ∃ Q : Poly, ∀ h r t : ℂ, h≠0 →
      h^n*eval (sourcePoint h r t) P=eval (basePoint h r t) Q := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0,C c,by simp⟩
  | add p q hp hq =>
    obtain ⟨m,A,hA⟩ := hp
    obtain ⟨n,B,hB⟩ := hq
    refine ⟨m+n,(X Coord.U)^n*A+(X Coord.U)^m*B,?_⟩
    intro h r t hh
    simp only [map_add,map_mul,map_pow,eval_X,basePoint]
    calc
      h^(m+n)*(eval (sourcePoint h r t) p+eval (sourcePoint h r t) q)=
        h^n*(h^m*eval (sourcePoint h r t) p)+h^m*(h^n*eval (sourcePoint h r t) q) := by rw [pow_add]; ring
      _ = _ := by rw [hA _ _ _ hh,hB _ _ _ hh]
  | mul_X p i hp =>
    obtain ⟨n,A,hA⟩ := hp
    cases i with
    | U =>
      refine ⟨n,A*driftSquare,?_⟩
      intro h r t hh
      simp only [map_mul,eval_X,sourcePoint]
      rw [←mul_assoc,hA _ _ _ hh]
      simp [driftSquare,basePoint]
    | K =>
      refine ⟨n+1,A,?_⟩
      intro h r t hh
      simp only [map_mul,eval_X,sourcePoint,pow_succ]
      calc
        h^n*h*(eval (sourcePoint h r t) p*h⁻¹)=h^n*eval (sourcePoint h r t) p := by field_simp
        _ = _ := hA _ _ _ hh
    | J =>
      refine ⟨n,A*(C (1/3:ℂ)*deficit),?_⟩
      intro h r t hh
      simp only [map_mul,eval_X,sourcePoint]
      rw [←mul_assoc,hA _ _ _ hh]
      simp only [deficit,map_sub,map_one,map_mul,eval_C,eval_X,basePoint]
      ring

theorem driftSquare_coprime_clock : IsCoprime driftSquare (X Coord.U) := by
  refine ⟨C (1/9:ℂ),C (1/9:ℂ)*X Coord.K*X Coord.U,?_⟩
  apply MvPolynomial.funext
  intro v
  norm_num [driftSquare]
  ring

theorem scaledSlope_driftSquare_dvd : driftSquare ∣ scaledSlope := by
  obtain ⟨n,R,hR⟩ := sourcePolynomial_regularization reducedSlope
  have he : (X Coord.U)^n*scaledSlope=driftSquare*((X Coord.U)^19*R) := by
    apply polynomial_ext_clock_nonzero
    intro h r t hh
    simp only [map_mul,map_pow,eval_X,basePoint]
    rw [←scaledSlope_eq h r t hh,slope_seam_factor]
    simp only [map_mul,eval_X,sourcePoint]
    calc
      h^n*(h^19*((9-r*h^2)*eval (sourcePoint h r t) reducedSlope))=
        (9-r*h^2)*(h^19*(h^n*eval (sourcePoint h r t) reducedSlope)) := by ring
      _ = _ := by rw [hR _ _ _ hh]; simp [driftSquare,basePoint]
  have hd : driftSquare ∣ (X Coord.U)^n*scaledSlope := ⟨(X Coord.U)^19*R,he⟩
  exact (driftSquare_coprime_clock.pow_right).dvd_of_dvd_mul_left hd

def reducedScaledSlope : Poly := scaledSlope_driftSquare_dvd.choose

theorem scaledSlope_drift_factor : scaledSlope=driftSquare*reducedScaledSlope :=
  scaledSlope_driftSquare_dvd.choose_spec

end
end HTGeometry.ThetaRatioInfinity
