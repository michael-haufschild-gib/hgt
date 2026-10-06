import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticClockSourceCore
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem clockPolynomial_regularization (P : Poly) :
    ∃ n : ℕ, ∃ Q : Poly, ∀ h v z : ℂ, h≠0 →
      h^n*eval (basePoint v h⁻¹ z) P=eval (basePoint h v z) Q := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0,C c,by simp⟩
  | add p q hp hq =>
    obtain ⟨m,A,hA⟩ := hp
    obtain ⟨n,B,hB⟩ := hq
    refine ⟨m+n,(X Coord.U)^n*A+(X Coord.U)^m*B,?_⟩
    intro h v z hh
    simp only [map_add,map_mul,map_pow,eval_X,basePoint]
    calc
      h^(m+n)*(eval (basePoint v h⁻¹ z) p+eval (basePoint v h⁻¹ z) q)=
        h^n*(h^m*eval (basePoint v h⁻¹ z) p)+h^m*(h^n*eval (basePoint v h⁻¹ z) q) := by rw [pow_add]; ring
      _ = _ := by rw [hA _ _ _ hh,hB _ _ _ hh]
  | mul_X p i hp =>
    obtain ⟨n,A,hA⟩ := hp
    cases i with
    | U =>
      refine ⟨n,A*X Coord.K,?_⟩
      intro h v z hh
      simp only [map_mul,eval_X,basePoint]
      rw [←mul_assoc,hA _ _ _ hh]
    | K =>
      refine ⟨n+1,A,?_⟩
      intro h v z hh
      simp only [map_mul,eval_X,basePoint,pow_succ]
      calc
        h^n*h*(eval (basePoint v h⁻¹ z) p*h⁻¹)=h^n*eval (basePoint v h⁻¹ z) p := by field_simp
        _ = _ := hA _ _ _ hh
    | J =>
      refine ⟨n,A*X Coord.J,?_⟩
      intro h v z hh
      simp only [map_mul,eval_X,basePoint]
      rw [←mul_assoc,hA _ _ _ hh]

theorem compactSlope_drift_dvd : driftSquare ∣ compactSlope := by
  obtain ⟨n,R,hR⟩ := clockPolynomial_regularization reducedSlope
  have he : (X Coord.U)^n*compactSlope=
      driftSquare*((X Coord.U)^20*defectLift R) := by
    apply polynomial_ext_clock_nonzero
    intro h r z hh
    simp only [map_mul,map_pow,eval_X,basePoint]
    rw [compactSlope_eval h r z hh,slope_seam_factor]
    simp only [map_mul,eval_X,basePoint,defectLift_eval]
    rw [←hR _ _ _ hh]
    norm_num [driftSquare,basePoint]
    ring
  have hd : driftSquare ∣ (X Coord.U)^n*compactSlope :=
    ⟨(X Coord.U)^20*defectLift R,he⟩
  exact (driftSquare_coprime_clock.pow_right).dvd_of_dvd_mul_left hd

def compactReducedSlope : Poly := compactSlope_drift_dvd.choose

theorem compactSlope_drift_factor : compactSlope=driftSquare*compactReducedSlope :=
  compactSlope_drift_dvd.choose_spec

theorem compactReducedSlope_eval (h r z : ℂ) (hh : h≠0) :
    eval (basePoint h r z) compactReducedSlope=
      h^20*eval (basePoint (9-r*h^2) h⁻¹ z) reducedSlope := by
  obtain ⟨n,R,hR⟩ := clockPolynomial_regularization reducedSlope
  have hd : driftSquare≠0 := by
    intro hd
    have hz := congrArg (eval (basePoint 0 0 0)) hd
    norm_num [driftSquare,basePoint] at hz
  have he : driftSquare*((X Coord.U)^n*compactReducedSlope)=
      driftSquare*((X Coord.U)^20*defectLift R) := by
    rw [mul_left_comm,←compactSlope_drift_factor]
    apply polynomial_ext_clock_nonzero
    intro h r z hh
    simp only [map_mul,map_pow,eval_X,basePoint]
    rw [compactSlope_eval h r z hh,slope_seam_factor]
    simp only [map_mul,eval_X,basePoint,defectLift_eval]
    rw [←hR _ _ _ hh]
    norm_num [driftSquare,basePoint]
    ring
  have hc := congrArg (eval (basePoint h r z)) (mul_left_cancel₀ hd he)
  simp only [map_mul,map_pow,eval_X,basePoint,defectLift_eval] at hc
  rw [←hR _ _ _ hh] at hc
  apply mul_left_cancel₀ (pow_ne_zero n hh)
  calc
    _ = h^20*(h^n*eval (basePoint (9-r*h^2) h⁻¹ z) reducedSlope) := hc
    _ = _ := by ring

end
end HTGeometry.ThetaRatioKineticContraction
