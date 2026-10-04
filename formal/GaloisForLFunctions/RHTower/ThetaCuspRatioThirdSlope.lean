import GaloisForLFunctions.RHTower.ThetaCuspRatioSourceIncidence
/-! # Exact polynomial numerator for the actual normalized third-minor slope

The source derivative is identified without a sign premise. Positivity of
this numerator along the actual modular orbit remains open.
-/

namespace RHTower.ThetaRatioSourceIncidence
noncomputable section
open MvPolynomial HTGeometry.ThetaRatioSource ThetaCuspModularRatio Filter Topology

private theorem state_derivative {x : ℝ} (hx : 0≤x) (i : Coord) :
    HasDerivAt (fun y => state y i) (eval (state x) (field i)) x := by
  have hq := sourceJet_zero_eval (state x)
  simp only [sourceJet,map_sub,eval_X] at hq
  have hq' := sub_right_inj.mp hq
  cases i with
  | U =>
      convert (du hx).ofReal_comp using 1 <;> first | rfl | simp [state,field,tau,t]
  | K =>
      convert (dk hx).ofReal_comp using 1 <;> first | rfl | norm_num [state,field,hq']
  | J =>
      have hk : k x≠0 := by linarith [k_gt hx]
      have hj : HasDerivAt J
          (k x^2*t x-6*k x-4+2*u x*(k x+2/3)*J x) x := by
        convert dJ hx using 1
        dsimp [D]
        field_simp [hk]
      convert hj.ofReal_comp using 1 <;> first | rfl | norm_num [state,field,tau,t,hq']

theorem eval_derivative {x : ℝ} (hx : 0≤x) (P : Poly) :
    HasDerivAt (fun y => eval (state y) P) (eval (state x) (lie P)) x := by
  have h := HTGeometry.hasDerivAt_mvPolynomial_eval_curve_real P
    (fun i y => state y i) (fun i => eval (state x) (field i)) x (state_derivative hx)
  simpa only [lie,map_sum,map_mul] using h

/-- Exact slope of the actual normalized odd third minor; its sign remains to prove. -/
theorem normalized_third_slope {x : ℝ} (hx : 0<x) :
    deriv ThetaCuspOddDirectionTransport.normalizedD x=
      (eval (state x) thirdSlope/((k x:ℂ)-1/6)^7).re := by
  have hp : (k x:ℂ)-1/6≠0 := by
    have h : k x-1/6≠0 := by linarith [k_gt hx.le]
    convert Complex.ofReal_ne_zero.mpr h using 1 <;> push_cast <;> norm_num
  have h0 : eval (state x) (sourceJet 0)≠0 := by
    simpa only [sourceJet_zero_eval,state] using hp
  have hd := (eval_derivative hx.le thirdMinor).div
    ((eval_derivative hx.le (sourceJet 0)).pow 6) (pow_ne_zero 6 h0)
  simp only [Pi.pow_apply] at hd
  have hf : HasDerivAt (fun y => eval (state y) thirdMinor/
        (eval (state y) (sourceJet 0))^6)
      (eval (state x) thirdSlope/((k x:ℂ)-1/6)^7) x := by
    convert hd using 1 <;> first | rfl | skip
    all_goals
      simp only [thirdSlope,map_sub,map_mul,map_ofNat,sourceJet_zero_eval,state]
      generalize ((k x:ℂ)-1/6)=p at hp ⊢
      field_simp [hp] <;> ring
  have hn : HasDerivAt (fun y => (ThetaCuspOddDirectionTransport.normalizedD y:ℂ))
      (eval (state x) thirdSlope/((k x:ℂ)-1/6)^7) x := by
    apply hf.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [normalized_third hy.le,sourceJet_zero_eval]
    rfl
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hn
  change HasDerivAt ThetaCuspOddDirectionTransport.normalizedD _ x at hr
  exact hr.deriv

end
end RHTower.ThetaRatioSourceIncidence
