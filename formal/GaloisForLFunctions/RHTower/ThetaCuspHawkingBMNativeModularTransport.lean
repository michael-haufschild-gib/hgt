import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeResidualAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCellGermExtension
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullCovectorModular
import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactKDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Modular transport of the literal hyperbolic theta mean and causal residual. -/
open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups
namespace RHTower.D4BMNativeCircle
open GaloisForLFunctions.HTGeometry D4BMGlobalAngularResponse D4BMModularCore
open GaloisForLFunctions.RHTower
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem rotation_matrix (phi : ℝ) :
    ((realSphericalRotation phi : SL2R) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos phi,-Real.sin phi;Real.sin phi,Real.cos phi] := by
  simp [realSphericalRotation,realCircleToSphericalK,realCircleRotation,Circle.coe_exp,
    Complex.exp_mul_I,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

private theorem rotation_surjective (k : upperHalfPlaneStabilizer) :
    ∃ phi : ℝ, realSphericalRotation phi = k := by
  obtain ⟨phi,hphi⟩ := Circle.exp_surjective (realSphericalKToCircle k)
  refine ⟨phi,?_⟩
  rw [realSphericalRotation,hphi,realCircleToSphericalK_realSphericalKToCircle]

private def circlePoint (d theta : ℝ) (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(circle d theta (coordinates z) 0:ℂ)+Complex.I*(circle d theta (coordinates z) 1:ℂ), by
    simpa using circle_pos d theta z⟩

private theorem circlePoint_coordinates (d theta : ℝ) (z : UpperHalfPlane) :
    coordinates (circlePoint d theta z) = circle d theta (coordinates z) := by
  ext i
  fin_cases i <;> simp [coordinates,circlePoint]

/-- Literal normalized average of an upper-half-plane field over the native
circle about its actual base point. -/
def circleAverage (F : UpperHalfPlane → ℂ) (d : ℝ) (z : UpperHalfPlane) : ℂ :=
  average (fun theta => F (circlePoint d theta z))

/-- The literal circle average in the upper-half-plane chart is the original
`(X, log Y)` circle average. -/
theorem circleAverage_coordinates (F : (Fin 2 → ℝ) → ℂ) (d : ℝ) (z : UpperHalfPlane) :
    circleAverage (fun w => F (coordinates w)) d z =
      average (fun theta => F (logCircle d theta z.re (Real.log z.im))) := by
  unfold circleAverage
  apply congrArg average
  funext theta
  change F (coordinates (circlePoint d theta z)) = _
  rw [circlePoint_coordinates]
  simp only [logCircle,coordinates,Real.exp_log z.im_pos]

private def radiusPoint (d : ℝ) : UpperHalfPlane :=
  ⟨Complex.I*(Real.exp d:ℂ),by
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,one_mul,zero_add]
    exact Real.exp_pos d⟩

private theorem section_action (z w : UpperHalfPlane) :
    ((z.toSL2R • w : UpperHalfPlane) : ℂ) = (z.re:ℂ)+(z.im:ℂ)*(w:ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hy : Real.sqrt z.im ≠ 0 := Real.sqrt_ne_zero'.mpr z.im_pos
  have hyc : (Real.sqrt z.im:ℂ) ≠ 0 := by exact_mod_cast hy
  simp only [UpperHalfPlane.coe_toSL2R,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,Algebra.algebraMap_self, RingHom.id_apply,
    Complex.ofReal_zero,Complex.ofReal_div,Complex.ofReal_one,zero_mul,zero_add]
  field_simp
  have hs : (Real.sqrt z.im:ℂ)^(2 : ℕ)=(z.im:ℂ) := by exact_mod_cast Real.sq_sqrt z.im_pos.le
  linear_combination (w:ℂ)*hs

private theorem radius_denominator (d phi : ℝ) :
    Real.cos phi^(2 : ℕ) + (Real.exp d)^(2 : ℕ)*Real.sin phi^(2 : ℕ) =
      Real.exp d*denominator d (2*phi) := by
  have he : Real.exp d*Real.cosh d-Real.exp d*Real.sinh d=1 := by
    rw [← mul_sub,Real.cosh_sub_sinh,← Real.exp_add]
    simp
  have he2 : Real.exp d^(2 : ℕ) = 1+2*Real.exp d*Real.sinh d := by
    rw [← Real.cosh_add_sinh]
    nlinarith [Real.cosh_sq_sub_sinh_sq d]
  dsimp [denominator]
  rw [Real.cos_two_mul]
  linear_combination Real.sin phi^(2 : ℕ)*he2 +
    (1+2*Real.exp d*Real.sinh d)*(Real.cos_sq_add_sin_sq phi) - he

private theorem rotation_radius (d phi : ℝ) :
    ((realSphericalRotation phi : SL2R) • radiusPoint d : UpperHalfPlane) =
      circlePoint d (2*phi) UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hd := (denominator_pos d (2*phi)).ne'
  have he := (Real.exp_pos d).ne'
  have he2 : Real.exp d^(2 : ℕ)-1 = 2*Real.exp d*Real.sinh d := by
    rw [← Real.cosh_add_sinh]
    nlinarith [Real.cosh_sq_sub_sinh_sq d]
  simp only [rotation_matrix,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Algebra.algebraMap_self,RingHom.id_apply]
  apply Complex.ext
  · simp only [radiusPoint,circlePoint,circle,coordinates,offset,height,
      UpperHalfPlane.coe_mk,UpperHalfPlane.I_re,UpperHalfPlane.I_im,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      Complex.div_re,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_neg,Complex.neg_re,
      Complex.neg_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,one_mul,
      zero_add,add_zero,sub_zero,neg_zero]
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      zero_mul,mul_zero,one_mul,zero_add,add_zero,sub_zero]
    rw [show Real.cos phi*Real.cos phi+(Real.sin phi*Real.exp d)*(Real.sin phi*Real.exp d)=
      Real.exp d*denominator d (2*phi) by nlinarith [radius_denominator d phi]]
    rw [Real.sin_two_mul]
    field_simp
    linear_combination Real.sin phi*Real.cos phi*he2
  · simp only [radiusPoint,circlePoint,circle,coordinates,offset,height,
      UpperHalfPlane.coe_mk,UpperHalfPlane.I_re,UpperHalfPlane.I_im,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      Complex.div_im,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_neg,Complex.neg_re,
      Complex.neg_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,one_mul,
      zero_add,add_zero,sub_zero,neg_zero]
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      zero_mul,mul_zero,one_mul,zero_add,add_zero,sub_zero]
    rw [show Real.cos phi*Real.cos phi+(Real.sin phi*Real.exp d)*(Real.sin phi*Real.exp d)=
      Real.exp d*denominator d (2*phi) by nlinarith [radius_denominator d phi]]
    field_simp
    nlinarith [Real.cos_sq_add_sin_sq phi]

private theorem circlePoint_action (d theta : ℝ) (z : UpperHalfPlane) :
    circlePoint d theta z = z.toSL2R •
      ((realSphericalRotation (theta/2) : SL2R) • radiusPoint d) := by
  have hr := rotation_radius d (theta/2)
  rw [show 2*(theta/2)=theta by ring] at hr
  rw [hr]
  apply UpperHalfPlane.ext
  rw [section_action]
  simp [circlePoint,circle,coordinates]
  ring

private theorem circlePoint_transport (g : SL2R) (z : UpperHalfPlane) :
    ∃ phi : ℝ, ∀ d theta : ℝ,
      g • circlePoint d theta z = circlePoint d (theta+2*phi) (g • z) := by
  obtain ⟨phi,hphi⟩ := rotation_surjective (sectionCocycle g z)
  refine ⟨phi,?_⟩
  intro d theta
  rw [circlePoint_action,circlePoint_action]
  have hk : g*z.toSL2R = (g • z).toSL2R*(realSphericalRotation phi : SL2R) := by
    rw [hphi,sectionCocycle_identity]
  rw [← mul_smul g z.toSL2R,hk,mul_smul]
  rw [← mul_smul (realSphericalRotation phi : SL2R),← Subgroup.coe_mul,
    ← realSphericalRotation_add]
  congr 3; ring_nf

private theorem integral_modular_action (g : SL(2,ℤ)) (z : UpperHalfPlane) :
    (g : SL2R) • z = g • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

private theorem source_circlePoint (q : XiZeroCopy) (d theta : ℝ) (z : UpperHalfPlane) :
    source q d theta z.re (Real.log z.im) =
      fullSquarePotential q (coordinates (circlePoint d theta z)) := by
  rw [circlePoint_coordinates]
  simp only [source,logCircle,coordinates,Real.exp_log z.im_pos]

/-- A modular transformation changes the angle of the literal theta circle source by
one fixed shift, independent of radius and integration angle. -/
theorem source_modular_shift (q : XiZeroCopy) (g : SL(2,ℤ)) (z : UpperHalfPlane) :
    ∃ phi : ℝ, ∀ d theta : ℝ,
      source q d (theta+phi) (g • z).re (Real.log (g • z).im) =
        source q d theta z.re (Real.log z.im) := by
  obtain ⟨phi,hphi⟩ := circlePoint_transport (g : SL2R) z
  refine ⟨2*phi,?_⟩
  intro d theta
  have hh := hphi d theta
  simp only [integral_modular_action] at hh
  rw [source_circlePoint,source_circlePoint,← hh,fullSquarePotential_modular]

private theorem average_shift {f : ℝ → ℂ}
    (hf : Function.Periodic f (2*Real.pi)) (c : ℝ) :
    average (fun theta => f (c+theta)) = average f := by
  have hz : (0:ℝ) ≤ 2*Real.pi := by positivity
  unfold average
  rw [← intervalIntegral.integral_of_le hz,← intervalIntegral.integral_of_le hz]
  congr 1
  rw [intervalIntegral.integral_comp_add_left]
  simpa only [add_zero,zero_add] using hf.intervalIntegral_add_eq c 0

private theorem circlePoint_periodic (d theta : ℝ) (z : UpperHalfPlane) :
    circlePoint d (theta + 2 * Real.pi) z = circlePoint d theta z := by
  apply UpperHalfPlane.ext
  simp [circlePoint,circle,offset,height,denominator,Real.sin_add_two_pi,
    Real.cos_add_two_pi]

/-- A modular-invariant upper-half-plane field has a modular-invariant literal
native-circle average. The result retains the radius and the actual circle
chart; only its angular origin is shifted. -/
theorem circleAverage_modular (F : UpperHalfPlane → ℂ)
    (hF : ∀ g : SL(2,ℤ), ∀ z : UpperHalfPlane, F (g • z) = F z)
    (d : ℝ) (g : SL(2,ℤ)) (z : UpperHalfPlane) :
    circleAverage F d (g • z) = circleAverage F d z := by
  obtain ⟨phi,hphi⟩ := circlePoint_transport (g : SL2R) z
  let f : ℝ → ℂ := fun theta => F (circlePoint d theta (g • z))
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro theta
    dsimp only [f]
    rw [circlePoint_periodic]
  calc
    circleAverage F d (g • z) = average f := rfl
    _ = average (fun theta => f (2 * phi + theta)) := (average_shift hf (2 * phi)).symm
    _ = average (fun theta => F (circlePoint d theta z)) := by
      apply congrArg average
      funext theta
      dsimp only [f]
      rw [show 2 * phi + theta = theta + 2 * phi by ring]
      change F (circlePoint d (theta + 2 * phi)
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g • z)) = _
      rw [← hphi d theta]
      exact hF g (circlePoint d theta z)
    _ = circleAverage F d z := rfl

/-- The original normalized theta circle mean is modular invariant for every real
radius, with the original chart and angular measure. -/
theorem mean_modular (q : XiZeroCopy) (d : ℝ) (g : SL(2,ℤ)) (z : UpperHalfPlane) :
    mean q d (g • z).re (Real.log (g • z).im) = mean q d z.re (Real.log z.im) := by
  obtain ⟨phi,hphi⟩ := source_modular_shift q g z
  have hp : Function.Periodic (fun theta => source q d theta (g • z).re (Real.log (g • z).im))
      (2*Real.pi) := by
    intro theta
    simp [source,logCircle,circle,offset,height,denominator,Real.sin_add_two_pi,Real.cos_add_two_pi]
  unfold mean
  rw [← average_shift hp phi]
  congr 1
  funext theta
  simpa only [add_comm phi theta] using hphi d theta

end
end RHTower.D4BMNativeCircle

namespace RHTower.D4BMNativeResponse
open GaloisForLFunctions.HTGeometry D4BMGlobalAngularResponse D4BMModularCore
open D4BMNativeCircle D4BMJointSource D4BMJointWave D4BMCausalKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem fullNullResponse_mean (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : UpperHalfPlane) :
    fullNullResponse q s amplitude p r z.re (Real.log z.im) =
      (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        mean q (Real.arcosh (max 1 (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2))))
          z.re (Real.log z.im)*oddSource s amplitude ((a+b)/2) ((a-b)/2) := by
  change (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
    ((1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..(2*Real.pi),
      source q (Real.arcosh (max 1 (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2))))
        theta z.re (Real.log z.im))*oddSource s amplitude ((a+b)/2) ((a-b)/2) = _
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  rfl

/-- The complete literal causal theta response is modular invariant in its angular
variable, at every real pair of null endpoints. -/
theorem fullNullResponse_modular (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ)
    (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    fullNullResponse q s amplitude p r (A • z).re (Real.log (A • z).im) =
      fullNullResponse q s amplitude p r z.re (Real.log z.im) := by
  rw [fullNullResponse_mean,fullNullResponse_mean]
  simp_rw [mean_modular]

private theorem residual_low (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ)
    (z : UpperHalfPlane) (hz : z.im < 2) :
    fullNullResidual q s amplitude p r z.re (Real.log z.im) =
      fullNullResponse q s amplitude p r z.re (Real.log z.im) := by
  simp only [fullNullResidual,Real.exp_log z.im_pos]
  have hh (i : Fin 3) : cutoffPower (principalExponent q i) ![z.re,z.im]=0 :=
    cutoffPower_low _ _ hz.le
  simp only [hh,mul_zero,Finset.sum_const_zero,sub_zero]

private theorem residual_translate (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ)
    (n : ℤ) (z : UpperHalfPlane) :
    fullNullResidual q s amplitude p r (T^n • z).re (Real.log (T^n • z).im) =
      fullNullResidual q s amplitude p r z.re (Real.log z.im) := by
  simp only [fullNullResidual,fullNullResponse_modular]
  congr 1
  simp only [cutoffPower,cutoff,Matrix.cons_val_one,ModularGroup.im_T_zpow_smul]

/-- Every closed-cell overlap preserves the full germ of the literal residual,
including the three original cutoff powers and their derivatives. -/
theorem fullNullResidual_cell_compatible (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) :
    CellGermCompatible (fun z => fullNullResidual q s amplitude p r z.re (Real.log z.im)) := by
  intro gamma z hz hgamma
  induction gamma using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hgamma ⊢
    by_cases hc : A 1 0 = 0
    · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      dsimp only
      rw [hn]
      exact residual_translate q s amplitude p r n w
    · obtain ⟨hl,hr⟩ := nonparabolic_cell_overlap_low A hc z hz hgamma
      have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hl
      have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
        (isOpen_lt (UpperHalfPlane.continuous_im.comp
          (show Continuous (fun w : UpperHalfPlane => A • w) by
            simp_rw [sl_moeb]; exact continuous_const_smul _)) continuous_const).mem_nhds hr
      filter_upwards [hleft,hright] with w hw hAw
      rw [residual_low q s amplitude p r _ hAw,residual_low q s amplitude p r _ hw,
        fullNullResponse_modular]

/-- Modular extension of the literal causal residual through its complete closed-cell germs. -/
def globalNativeResidual (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z => fullNullResidual q s amplitude p r z.re (Real.log z.im))

/-- The constructed extension is invariant under every actual modular transformation. -/
theorem globalNativeResidual_invariant (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ)
    (gamma : PSL2Z) (z : UpperHalfPlane) :
    globalNativeResidual q s amplitude p r (gamma • z) = globalNativeResidual q s amplitude p r z :=
  cellGermExtension_invariant _ (fullNullResidual_cell_compatible q s amplitude p r) gamma z

/-- The extension retains the original residual on a full neighborhood of every
closed-cell point, including all seams and elliptic corners. -/
theorem globalNativeResidual_germ (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    globalNativeResidual q s amplitude p r =ᶠ[𝓝 z]
      (fun w => fullNullResidual q s amplitude p r w.re (Real.log w.im)) :=
  cellGermExtension_germ _ (fullNullResidual_cell_compatible q s amplitude p r) z hz

/-- The global modular field equals the literal residual at every point of the closed cell. -/
theorem globalNativeResidual_eq_on_fd (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    globalNativeResidual q s amplitude p r z =
      fullNullResidual q s amplitude p r z.re (Real.log z.im) :=
  (globalNativeResidual_germ q s amplitude p r z hz).eq_of_nhds

/-- The actual joint L² residual has the globally modular representative, in its
original radial/modular product measure. -/
theorem nativeJointResidual_global_ae (q : XiZeroCopy) (s amplitude : ℂ) (tau : ℝ) :
    (nativeJointResidual q s amplitude tau : ℝ × UpperHalfPlane → ℂ) =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      (fun z => globalNativeResidual q s amplitude (tau+z.1) (tau-z.1) z.2) := by
  filter_upwards [nativeJointResidual_original_ae q s amplitude tau,
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)] with z hz hfd
  rw [globalNativeResidual_eq_on_fd q s amplitude _ _ z.2 hfd]
  exact hz

end
end RHTower.D4BMNativeResponse
