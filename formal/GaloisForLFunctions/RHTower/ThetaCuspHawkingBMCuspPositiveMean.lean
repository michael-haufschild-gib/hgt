import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspOrbitMeasurability

/-! Actual horizontal means of the positive majorants, with their original completion factors. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
open D4BMJointSource D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

/-- The original completion factor is nonzero in its actual right convergence half-plane. -/
theorem cuspCompletedLambda_ne_zero {s : ℂ} (hs : 1 < s.re) : reflectedCompletedLambda s ≠ 0 := by
  exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
    (riemannZeta_ne_zero_of_one_lt_re hs)

/-- The ratio of actual completion norms used in both strip majorants. -/
def cuspReflectionNorm (r : ℝ) : ℝ :=
  ‖reflectedCompletedLambda (2*(r:ℂ)-1)‖ / ‖reflectedCompletedLambda (2*(r:ℂ))‖

theorem cuspReflectionNorm_nonneg (r : ℝ) : 0 ≤ cuspReflectionNorm r := by
  unfold cuspReflectionNorm
  positivity

/-- The positive full row sum is the original scalar divided by its nonzero completion. -/
theorem positiveCuspRows_coe_eq_scalar_div (r : ℝ) (hr : 1 < r) (z : UpperHalfPlane) :
    (positiveCuspRows r z : ℂ) = scalar ((r:ℂ)-1/2) (coordinates z) /
      reflectedCompletedLambda (2*(r:ℂ)) := by
  apply (eq_div_iff (cuspCompletedLambda_ne_zero (by simp; linarith : 1 < (2*(r:ℂ)).re))).mpr
  simpa only [mul_comm] using positiveCuspRows_completed r hr z

theorem positiveCuspRows_continuous (r : ℝ) (hr : 1 < r) : Continuous (positiveCuspRows r) := by
  have hc : Continuous (fun z : UpperHalfPlane => scalar ((r:ℂ)-1/2) (coordinates z)) :=
    (cuspLeg_contDiffOn .scalar ((r:ℂ)-1/2)).continuousOn.comp_continuous
      (by unfold coordinates; fun_prop) (fun z => z.im_pos)
  have he : positiveCuspRows r = fun z =>
      (scalar ((r:ℂ)-1/2) (coordinates z) / reflectedCompletedLambda (2*(r:ℂ))).re := by
    funext z
    rw [← positiveCuspRows_coe_eq_scalar_div r hr z]
    rfl
  rw [he]
  exact Complex.continuous_re.comp (hc.div_const _)

/-- At high height the positive lower kernel retains precisely the nonparabolic power rows. -/
theorem positiveLowCuspRows_eq_sub (r : ℝ) (hr : 1 < r)
    (z : UpperHalfPlane) (hz : 2 ≤ z.im) :
    positiveLowCuspRows r z = positiveCuspRows r z-z.im^r := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sub,Complex.ofReal_cpow z.im_pos.le r]
  apply mul_left_cancel₀ (cuspCompletedLambda_ne_zero (by simp; linarith : 1 < (2*(r:ℂ)).re))
  rw [mul_sub,positiveCuspRows_completed r hr z,positiveLowCuspRows_coe r hr z]
  exact lowCuspPower_periodize_completed ⟨(r:ℂ),hr⟩ z hz

private theorem point_im (x y : ℝ) (hy : 0 < y) :
    (ofComplex (⟨x,y⟩:ℂ)).im = y := by
  rw [ofComplex_apply_of_im_pos (by simpa using hy)]
  rfl

private theorem point_coordinates (x y : ℝ) (hy : 0 < y) :
    coordinates (ofComplex (⟨x,y⟩:ℂ)) = ![x,y] := by
  rw [ofComplex_apply_of_im_pos (by simpa using hy)]
  rfl

private theorem point_continuous (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => ofComplex (⟨x,y⟩:ℂ)) := by
  have he : (fun x : ℝ => ofComplex (⟨x,y⟩:ℂ)) =
      fun x : ℝ => (⟨(⟨x,y⟩:ℂ),hy⟩:UpperHalfPlane) := by
    funext x
    exact ofComplex_apply_of_im_pos hy
  rw [he]
  have hm : Continuous (fun x : ℝ => (⟨x,y⟩:ℂ)) := by
    have he : (fun x : ℝ => (⟨x,y⟩:ℂ)) = fun x : ℝ => (x:ℂ)+(y:ℂ)*Complex.I := by
      funext x
      exact Complex.ext (by simp) (by simp)
    rw [he]
    fun_prop
  exact hm.upperHalfPlaneMk (fun _ => hy)

theorem positiveCuspRows_horizontal_integrable (r : ℝ) (hr : 1 < r) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun x : ℝ => positiveCuspRows r (ofComplex (⟨x,y⟩:ℂ))) (Ico (0:ℝ) 1) :=
  ((positiveCuspRows_continuous r hr).comp (point_continuous y hy)).integrableOn_Icc.mono_set Ico_subset_Icc_self

theorem positiveLowCuspRows_horizontal_integrable (r : ℝ) (hr : 1 < r) {y : ℝ} (hy : 2 ≤ y) :
    IntegrableOn (fun x : ℝ => positiveLowCuspRows r (ofComplex (⟨x,y⟩:ℂ))) (Ico (0:ℝ) 1) := by
  have hy0 : 0 < y := by linarith
  have he (x : ℝ) : positiveLowCuspRows r (ofComplex (⟨x,y⟩:ℂ)) =
      positiveCuspRows r (ofComplex (⟨x,y⟩:ℂ))-y^r := by
    rw [positiveLowCuspRows_eq_sub r hr _ (by rw [point_im x y hy0]; exact hy),point_im x y hy0]
  simp_rw [he]
  exact (positiveCuspRows_horizontal_integrable r hr hy0).sub (integrable_const _)

/-- The actual completed full positive mean is the original two-Weyl constant part. -/
theorem positiveCuspRows_completed_mean (r : ℝ) (hr : 1 < r) {y : ℝ} (hy : 0 < y) :
    reflectedCompletedLambda (2*(r:ℂ))*
      ((∫ x in Ico (0:ℝ) 1, positiveCuspRows r (ofComplex (⟨x,y⟩:ℂ)) : ℝ):ℂ) =
      principal ((r:ℂ)-1/2) ![0,y] := by
  have hiCast : (∫ x in Ico (0:ℝ) 1, (positiveCuspRows r (ofComplex (⟨x,y⟩:ℂ)):ℂ)) =
      ((∫ x in Ico (0:ℝ) 1, positiveCuspRows r (ofComplex (⟨x,y⟩:ℂ)) : ℝ):ℂ) := integral_ofReal
  rw [← hiCast,← integral_const_mul]
  have he (x : ℝ) : reflectedCompletedLambda (2*(r:ℂ))*(positiveCuspRows r (ofComplex (⟨x,y⟩:ℂ)):ℂ) =
      scalar ((r:ℂ)-1/2) ![x,y] := by
    rw [positiveCuspRows_completed r hr,point_coordinates x y hy]
  simp_rw [he]
  exact cuspScalar_unit_interval_mean _ hy

/-- The positive reverse kernel has the exact original reflected mean, without cancellation of norms. -/
theorem positiveLowCuspRows_mean (r : ℝ) (hr : 1 < r) {y : ℝ} (hy : 2 ≤ y) :
    (∫ x in Ico (0:ℝ) 1, positiveLowCuspRows r (ofComplex (⟨x,y⟩:ℂ))) =
      cuspReflectionNorm r*y^(1-r) := by
  have hy0 : 0 < y := by linarith
  have hn : ‖reflectedCompletedLambda (2*(r:ℂ))‖ ≠ 0 := norm_ne_zero_iff.mpr
    (cuspCompletedLambda_ne_zero (by simp; linarith : 1 < (2*(r:ℂ)).re))
  have he := lowCuspPower_completed_mean ⟨(r:ℂ),hr⟩ y hy
  simp_rw [← positiveLowCuspRows_coe r hr] at he
  have hiCast : (∫ x in Ico (0:ℝ) 1, (positiveLowCuspRows r (ofComplex (⟨x,y⟩:ℂ)):ℂ)) =
      ((∫ x in Ico (0:ℝ) 1, positiveLowCuspRows r (ofComplex (⟨x,y⟩:ℂ)) : ℝ):ℂ) := integral_ofReal
  rw [integral_const_mul,hiCast] at he
  have hh := congrArg norm he
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun x => positiveLowCuspRows_nonneg r _)),
    Complex.norm_cpow_eq_rpow_re_of_pos hy0] at hh
  have hp : (1-(r:ℂ)).re = 1-r := by simp
  change ‖reflectedCompletedLambda (2*(r:ℂ))‖*(∫ x in Ico (0:ℝ) 1,
    positiveLowCuspRows r (ofComplex (⟨x,y⟩:ℂ))) =
    ‖reflectedCompletedLambda (2*(r:ℂ)-1)‖*y^((1-(r:ℂ)).re) at hh
  rw [hp] at hh
  apply (mul_left_cancel₀ hn)
  rw [hh,cuspReflectionNorm]
  field_simp

private theorem principal_power (s : ℂ) (y : ℝ) :
    principal (s-1/2) ![0,y] =
      reflectedCompletedLambda (2*s-1)*(y:ℂ)^(1-s)+reflectedCompletedLambda (2*s)*(y:ℂ)^s := by
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantCoefficient,
    d4BMCompletedEisensteinCuspConstantMaassFactor,d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCuspSign,Bool.false_eq_true,if_false,if_true,mul_one]
  norm_num only
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  rw [show (2:ℂ)*(s-1/2)=2*s-1 by ring,
    show (1:ℂ)+(2*s-1)=2*s by ring,
    show (1/2:ℂ)+(-1)*(s-1/2)=1-s by ring,
    show (1/2:ℂ)+1*(s-1/2)=s by ring]

/-- The full positive mean has the integrable lower-strip two-power bound from its actual constant term. -/
theorem positiveCuspRows_mean_le (r : ℝ) (hr : 1 < r) {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0:ℝ) 1, positiveCuspRows r (ofComplex (⟨x,y⟩:ℂ))) ≤
      y^r+cuspReflectionNorm r*y^(1-r) := by
  have hn : 0 < ‖reflectedCompletedLambda (2*(r:ℂ))‖ := norm_pos_iff.mpr
    (cuspCompletedLambda_ne_zero (by simp; linarith : 1 < (2*(r:ℂ)).re))
  have he := positiveCuspRows_completed_mean r hr hy
  rw [principal_power] at he
  have he' := congrArg norm he
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun x => positiveCuspRows_nonneg r _))] at he'
  have ht : ‖reflectedCompletedLambda (2*(r:ℂ)-1)*(y:ℂ)^(1-(r:ℂ))+
      reflectedCompletedLambda (2*(r:ℂ))*(y:ℂ)^(r:ℂ)‖ ≤
      ‖reflectedCompletedLambda (2*(r:ℂ)-1)‖*y^(1-r)+
        ‖reflectedCompletedLambda (2*(r:ℂ))‖*y^r := by
    calc
      _ ≤ ‖reflectedCompletedLambda (2*(r:ℂ)-1)*(y:ℂ)^(1-(r:ℂ))‖+
          ‖reflectedCompletedLambda (2*(r:ℂ))*(y:ℂ)^(r:ℂ)‖ := norm_add_le _ _
      _ = _ := by simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,
        Complex.sub_re,Complex.one_re,Complex.ofReal_re]
  rw [← he'] at ht
  have hc : ‖reflectedCompletedLambda (2*(r:ℂ)-1)‖*y^(1-r)+
      ‖reflectedCompletedLambda (2*(r:ℂ))‖*y^r =
      ‖reflectedCompletedLambda (2*(r:ℂ))‖*(y^r+cuspReflectionNorm r*y^(1-r)) := by
    unfold cuspReflectionNorm
    field_simp
    ring
  rw [hc] at ht
  exact (mul_le_mul_iff_right₀ hn).mp (by simpa only [mul_comm] using ht)

end
end RHTower.D4BMModularCore
