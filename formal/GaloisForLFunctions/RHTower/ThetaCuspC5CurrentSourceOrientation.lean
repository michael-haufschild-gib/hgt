import GaloisForLFunctions.RHTower.ThetaCuspC5CurrentSourceQuadrature
/-! The remaining third-source coefficient in the complete Peano current is
strictly positive throughout the actual chamber. The enrichment and clock
remain tied to the same source. The complete current sign is still open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section

private theorem positive_from_derivative {f g : ℝ → ℝ} (h0 : f 0=0)
    (hd : ∀ z, HasDerivAt f (g z) z) (hg : ∀ z, 0 < z → 0 < g z)
    {z : ℝ} (hz : 0 < z) : 0 < f z := by
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro x _; exact (hd x).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hd x).deriv]
      exact hg x (by simpa only [interior_Ici,mem_Ioi] using hx)
  simpa only [h0] using hm (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) hz.le hz

/-- A rational lower clock envelope preserving the small-displacement term. -/
theorem clock_coth_gt_rationalLower {z : ℝ} (hz : 0 < z) :
    (3+2*z^2)/(3+z^2) < z*Real.cosh z/Real.sinh z := by
  have htangent (x : ℝ) (hx : 0 < x) : 0 < x*Real.cosh x-Real.sinh x := by
    have hd (s : ℝ) : HasDerivAt (fun r=>r*Real.cosh r-Real.sinh r) (s*Real.sinh s) s := by
      convert! ((hasDerivAt_id s).mul (Real.hasDerivAt_cosh s)).sub (Real.hasDerivAt_sinh s) using 1
      dsimp only [id_eq]
      ring
    exact positive_from_derivative (by simp) hd
      (fun s hs=>mul_pos hs (Real.sinh_pos_iff.mpr hs)) hx
  let H:=fun x : ℝ=>(3+x^2)*x*Real.cosh x-(3+2*x^2)*Real.sinh x
  have hd (x : ℝ) : HasDerivAt H
      (x*(x*Real.cosh x-Real.sinh x)+x^3*Real.sinh x) x := by
    have h:=hasDerivAt_id x
    convert! (((((h.pow 2).const_add 3).mul h).mul (Real.hasDerivAt_cosh x)).sub
      ((((h.pow 2).const_mul 2).const_add 3).mul (Real.hasDerivAt_sinh x))) using 1
    dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply,Pi.add_apply]
    ring
  have hh : 0 < H z := positive_from_derivative (by simp [H]) hd
    (fun x hx=>add_pos (mul_pos hx (htangent x hx))
      (mul_pos (pow_pos hx 3) (Real.sinh_pos_iff.mpr hx))) hz
  apply (div_lt_div_iff₀ (by positivity : (0:ℝ)<3+z^2) (Real.sinh_pos_iff.mpr hz)).mpr
  dsimp only [H] at hh
  nlinarith only [hh]

private theorem delta_coefficient_algebra {Z a g b h C : ℝ}
    (hZ : 0 < Z) (hg : 1 ≤ g) (hga : g ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (hgh : 15*g*h ≤ Z^2)
    (hC : (2*a+b)/(1+a)*(1+12*Z)/(1+6*Z) < C) :
    0 < ((1+h)*(9+12*Z)+g*(16+36*h))*(5*C-9)/25+2*(2*a+b)*(1+h) := by
  have ha : 1 ≤ a := hg.trans hga
  have ha1 : 0 ≤ a-1 := sub_nonneg.mpr ha
  have hg1 : 0 ≤ g-1 := sub_nonneg.mpr hg
  have hag : 0 ≤ a-g := sub_nonneg.mpr hga
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hg0 : 0 < g := lt_of_lt_of_le (by norm_num) hg
  have hden : 0 < (1+a)*(1+6*Z) := by positivity
  have hCmul : (2*a+b)*(1+12*Z)<C*((1+a)*(1+6*Z)) := by
    have he : (2*a+b)/(1+a)*(1+12*Z)/(1+6*Z)=
        ((2*a+b)*(1+12*Z))/((1+a)*(1+6*Z)) := by
      field_simp [(by positivity : (1+a) ≠ 0),(by positivity : (1+6*Z) ≠ 0)]
    rw [he] at hC
    exact (div_lt_iff₀ hden).mp hC
  have hClow : 0 < C*((1+a)*(1+6*Z))-2*a*(1+12*Z) := by
    have hp : 0 ≤ b*(1+12*Z) := by positivity
    nlinarith only [hCmul,hp]
  let R:=a-9+(66*a-54)*Z
  let N0:=100*(a-g)^2+(216*g+109)*(a-g)+(g-1)*(116*g+81)
  let N1:=1404+3462*(a-1)+192*(g-1)+600*(a-1)^2+1056*(a-1)*(g-1)
  let N2:=144+792*(a-1)
  let N:=N0+N1*Z+N2*Z^2
  have hN0 : 0 ≤ N0 := by dsimp only [N0]; positivity
  have hN1 : 0 < N1 := by dsimp only [N1]; positivity
  have hN2 : 0 < N2-12 := by dsimp only [N2]; linarith only [ha1]
  have hreserve : 0 < N-12*Z^2 := by
    have he : N-12*Z^2=N0+N1*Z+(N2-12)*Z^2 := by dsimp only [N]; ring
    rw [he]
    exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hN0 (mul_pos hN1 hZ))
      (mul_nonneg hN2.le (sq_nonneg Z))
  have hN : 0 < N := by nlinarith only [hreserve,sq_nonneg Z]
  have hR : 0 ≤ R+9 := by
    have hh' : 0 < 66*a-54 := by linarith only [ha]
    dsimp only [R]
    nlinarith only [ha0, mul_pos hh' hZ]
  have hbad := mul_nonneg (show 0 ≤ 20*g*h by positivity) hR
  have hpay : 0 ≤ h*N := mul_nonneg hh hN.le
  have hfull : 0 < (1+h)*N+20*g*h*R := by
    nlinarith only [hreserve,hbad,hpay,hgh]
  let Abar:=(1+h)*(9+12*Z)+g*(16+36*h)
  have hA : 0 < Abar := by dsimp only [Abar]; positivity
  have hcorrection : 0 < 5*Abar*(C*((1+a)*(1+6*Z))-2*a*(1+12*Z))+
      50*b*(1+h)*((1+a)*(1+6*Z)) := by positivity
  have hid : 25*(Abar*(5*C-9)/25+2*(2*a+b)*(1+h))*((1+a)*(1+6*Z))=
      (1+h)*N+20*g*h*R+
        (5*Abar*(C*((1+a)*(1+6*Z))-2*a*(1+12*Z))+
          50*b*(1+h)*((1+a)*(1+6*Z))) := by
    dsimp only [Abar,N,N0,N1,N2,R]
    ring
  have hp := add_pos hfull hcorrection
  rw [←hid] at hp
  have hp' := (mul_pos_iff_of_pos_right hden).mp hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0:ℝ)<25)).mp hp'

local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "c" => thetaCuspLogCurvature
local notation "Q" => thetaCuspReflectedLogAction
local notation "Z" => curvatureShapeAction
local notation "a" => curvatureShapeAlpha
local notation "g" => curvatureShapeGamma
local notation "b" => curvatureShapeBeta
local notation "C" => intrinsicClockLogElasticity
local notation "y" => completedFirstDenominator
local notation "d" => completedLocalDenominator
local notation "k" => denominatorClockRate

private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)
private theorem e_pos (u t : ℝ) : 0 < e u t := by
  unfold completedCurvatureEven
  exact div_pos (add_pos (thetaCuspLogCurvature_pos (u+t)) (thetaCuspLogCurvature_pos (u-t))) (by norm_num)
private theorem beta_nonneg (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ b u t := by
  have hp : 0 ≤ shapeCurvatureSlope u t := by
    unfold shapeCurvatureSlope
    exact div_nonneg (sub_nonneg.mpr (thetaCuspLogCurvatureJet_strictMono.monotone (by linarith))) (by norm_num)
  unfold curvatureShapeBeta
  exact div_nonneg (mul_nonneg (sq_nonneg t) hp) (E_pos u ht).le

/-- The actual integrated clock retains at least the constant-source action. -/
theorem denominatorClockCoordinate_energy_lower (u : ℝ) {t : ℝ} (ht : 0 < t) :
    18*Z u t ≤ (k u*y u t)^2 := by
  have hgap := centerCurvature_le_completedCurvatureEven u ht.le
  have hgap0 := sub_nonneg.mpr hgap
  have hE := E_pos u ht
  have hid : (y u t)^2-4*c u*Z u t=
      (E u t-t*e u t)^2+4*t*E u t*(e u t-c u) := by
    unfold completedFirstDenominator curvatureShapeAction
    ring
  have hnonneg : 0 ≤ (y u t)^2-4*c u*Z u t := by rw [hid]; positivity
  have hh:=mul_nonneg (sq_nonneg (k u)) hnonneg
  have hk:=denominatorClockRate_sq u
  have he : (k u*y u t)^2-18*Z u t=
      (k u)^2*((y u t)^2-4*c u*Z u t) := by
    linear_combination 2*Z u t*hk
  nlinarith only [hh,he]

/-- Actual clock lower envelope, retaining all reflected shape variables. -/
theorem intrinsicClockLogElasticity_lower (u : ℝ) {t : ℝ} (ht : 0 < t) :
    (2*a u t+b u t)/(1+a u t)*(1+12*Z u t)/(1+6*Z u t) < C u t := by
  have hE:=E_pos u ht
  have hZ : 0 < Z u t := mul_pos ht hE
  have ha : 0 < a u t := div_pos (mul_pos ht (e_pos u t)) hE
  have hb:=beta_nonneg u ht
  have hD : 0 < 2*a u t+b u t := by positivity
  have hT : 0 < (2*a u t+b u t)/(1+a u t) := by positivity
  let z:=k u*y u t
  have hz : 0 < z := mul_pos (denominatorClockRate_pos u) (completedFirstDenominator_pos u ht)
  have hsq : 18*Z u t ≤ z^2 := denominatorClockCoordinate_energy_lower u ht
  have hscalar : (1+12*Z u t)/(1+6*Z u t) ≤ (3+2*z^2)/(3+z^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hsq]
  have hc:=mul_lt_mul_of_pos_left (hscalar.trans_lt (clock_coth_gt_rationalLower hz)) hT
  have hy : 0 < E u t+t*e u t := add_pos hE (mul_pos ht (e_pos u t))
  have hratio : (2*a u t+b u t)/(1+a u t)=t*d u t/y u t := by
    unfold curvatureShapeAlpha curvatureShapeBeta completedFirstDenominator completedLocalDenominator shapeCurvatureSlope
    field_simp [hE.ne',hy.ne']
  have he : (2*a u t+b u t)/(1+a u t)*(z*Real.cosh z/Real.sinh z)=C u t := by
    rw [hratio]
    unfold intrinsicClockLogElasticity denominatorClockProfileJet denominatorClockProfile
    dsimp only [z]
    field_simp [(completedFirstDenominator_pos u ht).ne',
      (denominatorClockProfile_pos u ht).ne']
  rw [he] at hc
  convert! hc using 1 <;> ring

private theorem gamma_bounds {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    1 ≤ g u t ∧ g u t ≤ a u t := by
  have hQ:=thetaCuspReflectedLogAction_pos (u:=u) ht
  have hE:=E_pos u ht
  have hgpos : 0 < g u t := div_pos (mul_pos ht hE) hQ
  have hg : 1 ≤ g u t := by
    have hh:=two_mul_action_le_velocity_of_jetTwo_nonneg ht htu
      (fun x _=>(thetaCuspLogCurvatureJetTwo_pos_all x).le)
    unfold thetaCuspReflectedActionVelocity at hh
    rw [show thetaCuspReflectedLogJetOne u t=2*E u t by rw [completedDecayEvenPrimitive_eq]; ring] at hh
    unfold curvatureShapeGamma
    exact (le_div_iff₀ hQ).mpr (by linarith only [hh])
  have hd : 0 < t*deriv (g u) t := by
    rw [(hasDerivAt_curvatureShapeGamma u ht).deriv]
    exact mul_pos ht (div_pos (curvatureShapeGamma_current_pos ht htu) (sq_pos_of_pos hQ))
  rw [curvatureShapeGamma_evolution u ht] at hd
  have hinner := (mul_pos_iff_of_pos_left hgpos).mp hd
  exact ⟨hg,by linarith only [hg,hinner]⟩

/-- Exact coefficient of the third source after removing the fourth-source Peano block. -/
def enrichedPeanoDeltaCoefficient (u t : ℝ) : ℝ :=
  ((1+(Q u t)^2/15)*(9+12*Z u t)+g u t*(16+36*(Q u t)^2/15))*(5*C u t-9)/25+
    2*(2*a u t+b u t)*(1+(Q u t)^2/15)

/-- The remaining third source is globally favorable in the actual complete current. -/
theorem enrichedPeanoDeltaCoefficient_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < enrichedPeanoDeltaCoefficient u t := by
  rcases gamma_bounds ht htu with ⟨hg,hga⟩
  have hZ : 0 < Z u t := mul_pos ht (E_pos u ht)
  have hQ:=thetaCuspReflectedLogAction_pos (u:=u) ht
  have hQZ : Q u t ≤ Z u t := by
    change 1 ≤ Z u t/Q u t at hg
    simpa only [one_mul] using (le_div_iff₀ hQ).mp hg
  have hgh : 15*g u t*((Q u t)^2/15) ≤ (Z u t)^2 := by
    have hid : 15*g u t*((Q u t)^2/15)=Z u t*Q u t := by
      unfold curvatureShapeGamma curvatureShapeAction
      field_simp [hQ.ne']
    rw [hid]
    nlinarith only [mul_le_mul_of_nonneg_left hQZ hZ.le]
  have hh:=delta_coefficient_algebra hZ hg hga (beta_nonneg u ht)
    (by positivity : 0 ≤ (Q u t)^2/15) hgh (intrinsicClockLogElasticity_lower u ht)
  convert! hh using 1
  unfold enrichedPeanoDeltaCoefficient
  ring

/-- Lower-jet part of the exact Peano remainder, keeping the actual clock. -/
def enrichedCurrentLowerJetRemainder (u t : ℝ) : ℝ :=
  actionPowerPeanoRemainderKernel 16 (Z u t) (a u t) (g u t) (b u t) 0 (C u t)+
    (Q u t)^2/15*
      actionPowerPeanoRemainderKernel 36 (Z u t) (a u t) (g u t) (b u t) 0 (C u t)

theorem enrichedCurrentPeanoRemainder_delta_identity (u t : ℝ) :
    enrichedCurrentPeanoRemainder u t=enrichedCurrentLowerJetRemainder u t+
      enrichedPeanoDeltaCoefficient u t*curvatureShapeDelta u t := by
  unfold enrichedCurrentPeanoRemainder enrichedCurrentLowerJetRemainder
    actionPowerPeanoRemainderKernel enrichedPeanoDeltaCoefficient
  ring

/-- The full third-source contribution in the Peano remainder is strictly positive. -/
theorem enrichedCurrentPeanoRemainder_gt_lowerJet {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    enrichedCurrentLowerJetRemainder u t < enrichedCurrentPeanoRemainder u t := by
  have hd : 0 < curvatureShapeDelta u t := by
    have hr : 0 < shapeCurvatureSecond u t := by
      unfold shapeCurvatureSecond
      exact div_pos (add_pos (thetaCuspLogCurvatureJetTwo_pos_all (u+t))
        (thetaCuspLogCurvatureJetTwo_pos_all (u-t))) (by norm_num)
    unfold curvatureShapeDelta
    exact div_pos (mul_pos (pow_pos ht 3) hr) (E_pos u ht)
  rw [enrichedCurrentPeanoRemainder_delta_identity]
  linarith only [mul_pos (enrichedPeanoDeltaCoefficient_pos ht htu) hd]

end
end RHTower.ThetaCuspDefect
