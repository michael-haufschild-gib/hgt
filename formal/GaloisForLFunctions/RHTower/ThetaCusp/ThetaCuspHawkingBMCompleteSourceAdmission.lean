import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMWeightedResponseAdmission
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullSourceCircleGrowth
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularMasterCurrent

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMQuadraticMixedSource D4BMNativeCircle
noncomputable section
set_option autoImplicit false

private theorem height_envelope_le (z : ℍ) {R : ℝ} (hR : 0 ≤ R)
    (hz : dist z I ≤ R) : max 1 (max z.im (1/z.im)) ≤ Real.exp R := by
  have hu : z.im ≤ Real.exp R := by
    have h := im_le_im_mul_exp_dist z I
    simp only [I_im,one_mul] at h
    exact h.trans (Real.exp_le_exp.mpr hz)
  have hl : 1/z.im ≤ Real.exp R := by
    apply (div_le_iff₀ z.im_pos).mpr
    have h := im_le_im_mul_exp_dist I z
    simp only [I_im,dist_comm I z] at h
    exact h.trans (by rw [mul_comm]; gcongr)
  exact max_le (Real.one_le_exp_iff.mpr hR) (max_le hu hl)

private theorem radial_admission_of_height_square (f : ℍ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z : ℍ, ‖f z‖ ≤ C*(max 1 (max z.im (1/z.im)))^2)
    (p : ℝ) (hp : 3 < p) :
    Integrable (fun z : ℍ => Real.exp (-p*dist z I)*‖f z‖) := by
  apply radial_weight_integrable_of_ball_bound f hf (8*C) 3 p (by norm_num) hp
  intro R hR
  letI : IsFiniteMeasure ((volume : Measure ℍ).restrict (Metric.closedBall I R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall I R).measure_lt_top⟩
  have hi : IntegrableOn (fun z => ‖f z‖) (Metric.closedBall I R) :=
    hf.norm.continuousOn.integrableOn_compact (isCompact_closedBall I R)
  have hbR (z : ℍ) (hz : z ∈ Metric.closedBall I R) :
      ‖f z‖ ≤ C*(Real.exp R)^2 := by
    exact (hb z).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (height_envelope_le z hR hz) 2) hC)
  calc
    _ ≤ ∫ _z : ℍ in Metric.closedBall I R, C*(Real.exp R)^2 :=
      setIntegral_mono_on hi (integrable_const _) measurableSet_closedBall hbR
    _ = C*(Real.exp R)^2*volume.real (Metric.closedBall I R) := by
      rw [setIntegral_const,smul_eq_mul,mul_comm]
    _ ≤ C*(Real.exp R)^2*(8*Real.exp R) :=
      mul_le_mul_of_nonneg_left (hyperbolic_ball_real_volume_le R) (by positivity)
    _ = (8*C)*Real.exp (3*R) := by
      rw [show 3*R = R+R+R by ring,Real.exp_add,Real.exp_add]
      ring

private theorem powerResponse_high_norm (lambda p A : ℂ) (hp : p.re ≤ 2)
    (z : Fin 2 → ℝ) (hz : 1 ≤ z 1) :
    ‖powerResponse lambda p A z‖ ≤ ‖A/(p*(p-1)-lambda)‖*(z 1)^2 := by
  rw [powerResponse,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hz hp

private theorem cuspResponse_high_norm (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 1 ≤ z 1 →
      ‖cuspResponse q branch z‖ ≤ C*(z 1)^2 := by
  let r : ℂ := q.1
  let L := parameter q branch
  let A := d4BMCompletedEisensteinCuspConstantCoefficient (center q) true
  let D := d4BMCompletedEisensteinCuspConstantCoefficient (center q) false
  let C0 := ‖A^2/((2*r)*(2*r-1)-L)‖
  let C1 := ‖(2*A*D)/(1*(1-1)-L)‖
  let C2 := ‖D^2/((2-2*r)*(2-2*r-1)-L)‖
  refine ⟨‖L/2‖*(C0+C1+C2),by positivity,?_⟩
  intro z hz
  have hs := xi_divisor_support_re_mem_open_unit q.1
  have hp : (2*r).re ≤ 2 := by dsimp [r]; norm_num; linarith [hs.2]
  have hm : (2-2*r).re ≤ 2 := by dsimp [r]; norm_num; linarith [hs.1]
  have h0 := powerResponse_high_norm L (2*r) (A^2) hp z hz
  have h1 := powerResponse_high_norm L 1 (2*A*D) (by norm_num) z hz
  have h2 := powerResponse_high_norm L (2-2*r) (D^2) hm z hz
  change ‖(L/2)*(powerResponse L (2*r) (A^2) z+
    powerResponse L 1 (2*A*D) z+powerResponse L (2-2*r) (D^2) z)‖ ≤ _
  rw [norm_mul,mul_assoc ‖L/2‖ (C0+C1+C2) ((z 1)^2)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖powerResponse L (2*r) (A^2) z‖+
      ‖powerResponse L 1 (2*A*D) z‖+‖powerResponse L (2-2*r) (D^2) z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C0*(z 1)^2+C1*(z 1)^2+C2*(z 1)^2 := add_le_add (add_le_add h0 h1) h2
    _ = (C0+C1+C2)*(z 1)^2 := by ring

/-- The complete cusp cutoff has a quadratic height ceiling on every modular image. -/
theorem globalCuspCutoff_height_square_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℍ,
      ‖globalCuspCutoff q branch z‖ ≤ C*(max 1 (max z.im (1/z.im)))^2 := by
  obtain ⟨C,hC,hb⟩ := cuspResponse_high_norm q branch
  refine ⟨C,hC,?_⟩
  intro z
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  have hinv := globalCuspCutoff_invariant q branch (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at hinv
  rw [← hinv,globalCuspCutoff_eq_on_fd q branch _ hA]
  by_cases hy : (A • z).im ≤ 2
  · rw [cutoffResponse_zero q branch _ hy,norm_zero]
    positivity
  · have hy1 : 1 ≤ (A • z).im := by linarith
    have hk : ‖cutoff (coordinates (A • z))‖ ≤ 1 := by
      rw [cutoff,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have hh : (A • z).im ≤ max 1 (max z.im (1/z.im)) :=
      (modular_orbit_height_le (QuotientGroup.mk A) z).trans (le_max_right _ _)
    calc
      _ ≤ ‖cuspResponse q branch (coordinates (A • z))‖ := by
        rw [cutoffResponse,norm_mul]
        exact (mul_le_mul_of_nonneg_right hk (norm_nonneg _)).trans_eq (one_mul _)
      _ ≤ C*(A • z).im^2 := hb _ hy1
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (A • z).im_pos.le hh 2) hC

/-- All original cutoff contributions are absolutely admitted at every exponent above three. -/
theorem globalCuspCutoff_radial_weight_integrable (q : XiZeroCopy) (branch : Bool)
    (p : ℝ) (hp : 3 < p) :
    Integrable (fun z : ℍ => Real.exp (-p*dist z I)*‖globalCuspCutoff q branch z‖) := by
  obtain ⟨C,hC,hb⟩ := globalCuspCutoff_height_square_bound q branch
  exact radial_admission_of_height_square _
    (ChartSmooth.continuous (globalCuspCutoff_smooth q branch)) C hC hb p hp

/-- The literal full square is continuous in the original upper-half-plane coordinates. -/
theorem fullSquarePotential_upperHalfPlane_continuous (q : XiZeroCopy) :
    Continuous (fun z : ℍ => fullSquarePotential q (coordinates z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply (fullSquarePotential_smooth q _ z.im_pos 0).continuousAt.comp
  have hc : Continuous (coordinates : ℍ → Fin 2 → ℝ) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  exact hc.continuousAt

/-- Absolute admission of the literal full square, retaining every remainder and cross term. -/
theorem fullSquarePotential_radial_weight_integrable (q : XiZeroCopy)
    (p : ℝ) (hp : 3 < p) :
    Integrable (fun z : ℍ => Real.exp (-p*dist z I)*‖fullSquarePotential q (coordinates z)‖) := by
  obtain ⟨C,hC,hb⟩ := fullSquarePotential_global_growth q
  apply radial_admission_of_height_square _ (fullSquarePotential_upperHalfPlane_continuous q) C hC _ p hp
  intro z
  have hh : 1 ≤ max 1 (max z.im (1/z.im)) := le_max_left _ _
  have he := Real.rpow_le_rpow_of_exponent_le hh (sourceGrowthExponent_bounds q).2.le
  rw [Real.rpow_two] at he
  exact (hb z).trans (mul_le_mul_of_nonneg_left he hC)

private theorem radial_complex_integrable_iff (f : ℍ → ℂ) (hf : Continuous f) (p : ℝ) :
    Integrable (fun z : ℍ => Real.exp (-p*dist z I)*‖f z‖) ↔
      Integrable (fun z : ℍ => (Real.exp (-p*dist z I):ℂ)*f z) := by
  have hc : Continuous (fun z : ℍ => (Real.exp (-p*dist z I):ℂ)*f z) := by fun_prop
  have h := integrable_norm_iff (μ := (volume : Measure ℍ)) hc.aestronglyMeasurable
  simpa only [norm_mul,Complex.norm_of_nonneg (Real.exp_pos _).le] using h

/-- Absolute admission of the complete angular field at every exponent above three. -/
theorem fullAngular_radial_weight_integrable (q : XiZeroCopy) (branch : Bool)
    (p : ℝ) (hp : 3 < p) :
    Integrable (fun z : ℍ => Real.exp (-p*dist z I)*‖fullAngular q branch z‖) := by
  have hc := (radial_complex_integrable_iff _
    (ChartSmooth.continuous (globalCuspCutoff_smooth q branch)) p).mp
    (globalCuspCutoff_radial_weight_integrable q branch p hp)
  have hr := (radial_complex_integrable_iff _
    (ChartSmooth.continuous (globalResponse_smooth q branch)) p).mp
    (globalResponse_radial_weight_integrable q branch p (by linarith))
  apply (radial_complex_integrable_iff _
    (ChartSmooth.continuous (fullAngular_smooth q branch)) p).mpr
  simp only [fullAngular,mul_add]
  exact hc.add hr

/-- The full source combination is admitted without dropping either angular component. -/
theorem fullAngular_sub_square_radial_weight_integrable (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (p : ℝ) (hp : 3 < p) :
    Integrable (fun z : ℍ => Real.exp (-p*dist z I)*
      ‖fullAngular q branch z-a*fullSquarePotential q (coordinates z)‖) := by
  have hb := (radial_complex_integrable_iff _
    (ChartSmooth.continuous (fullAngular_smooth q branch)) p).mp
    (fullAngular_radial_weight_integrable q branch p hp)
  have hq := (radial_complex_integrable_iff _ (fullSquarePotential_upperHalfPlane_continuous q) p).mp
    (fullSquarePotential_radial_weight_integrable q p hp)
  apply (radial_complex_integrable_iff _
    ((ChartSmooth.continuous (fullAngular_smooth q branch)).sub
      ((fullSquarePotential_upperHalfPlane_continuous q).const_mul a)) p).mpr
  have he (z : ℍ) : (Real.exp (-p*dist z I):ℂ)*
      (fullAngular q branch z-a*fullSquarePotential q (coordinates z)) =
      (Real.exp (-p*dist z I):ℂ)*fullAngular q branch z-
      a*((Real.exp (-p*dist z I):ℂ)*fullSquarePotential q (coordinates z)) := by ring
  exact (hb.sub (hq.const_mul a)).congr (Eventually.of_forall (fun z => (he z).symm))

/-- Changing the radial center preserves absolute exponential admission. -/
theorem radial_weight_integrable_change_center (f : ℍ → ℂ) (hf : Continuous f)
    (p : ℝ) (hp : 0 ≤ p)
    (hi : Integrable (fun z : ℍ => Real.exp (-p*dist z I)*‖f z‖)) (w : ℍ) :
    Integrable (fun z : ℍ => Real.exp (-p*dist z w)*‖f z‖) := by
  have hc : Continuous (fun z : ℍ => Real.exp (-p*dist z w)*‖f z‖) := by fun_prop
  apply (hi.const_mul (Real.exp (p*dist w I))).mono' hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have he : Real.exp (-p*dist z w) ≤ Real.exp (p*dist w I)*Real.exp (-p*dist z I) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (dist_triangle z w I) hp]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right he (norm_nonneg (f z))

/-- The complete source combination is admitted around every physical target point. -/
theorem fullAngular_sub_square_radial_weight_integrable_at (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (p : ℝ) (hp : 3 < p) (w : ℍ) :
    Integrable (fun z : ℍ => Real.exp (-p*dist z w)*
      ‖fullAngular q branch z-a*fullSquarePotential q (coordinates z)‖) := by
  exact radial_weight_integrable_change_center _
    ((ChartSmooth.continuous (fullAngular_smooth q branch)).sub
      ((fullSquarePotential_upperHalfPlane_continuous q).const_mul a)) p (by linarith)
    (fullAngular_sub_square_radial_weight_integrable q branch a p hp) w

/-- The original fundamental rate lies strictly in the strip required by the horizon kernel. -/
theorem fundamental_physicalRate_re_bounds (q : XiZeroCopy) (branch : Bool) :
    -2 < (physicalRate q branch).re ∧ (physicalRate q branch).re < -1 := by
  have hs := xi_divisor_support_re_mem_open_unit q.1
  cases branch <;> norm_num [physicalRate] <;> constructor <;> linarith [hs.1,hs.2]

/-- The complete source in the two original horizon arms is absolutely admitted
at its unchanged physical decay exponent. -/
theorem physical_cap_source_radial_weight_integrable (q : XiZeroCopy) (branch : Bool) :
    Integrable (fun z : ℍ =>
      Real.exp (-(1-2*(physicalRate q branch).re)*dist z I)*
      ‖fullAngular q branch z-
        (physicalRate q branch*(physicalRate q branch-1)/4)*
          fullSquarePotential q (coordinates z)‖) := by
  apply fullAngular_sub_square_radial_weight_integrable
  linarith [(fundamental_physicalRate_re_bounds q branch).2]

end
end RHTower.D4BMModularCore
