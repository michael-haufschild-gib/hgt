import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleMean
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceOverlap

/-! Global growth of the literal Xi half-square and its native circle mean. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMNativeCircle
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def sourceGrowthExponent (q : XiZeroCopy) : ℝ := 1+2*|(center q).re|

private theorem exponent_nonneg (q : XiZeroCopy) : 0 ≤ sourceGrowthExponent q := by
  unfold sourceGrowthExponent
  positivity

/-- The actual Xi strip supplies a strict growth margin below the source decay rate. -/
theorem sourceGrowthExponent_bounds (q : XiZeroCopy) :
    1 ≤ sourceGrowthExponent q ∧ sourceGrowthExponent q < 2 := by
  have hs := xi_divisor_support_re_mem_open_unit q.1
  have hc : |(center q).re| < 1/2 := by
    apply abs_lt.mpr
    simp only [D4BMGlobalAngularResponse.center,Complex.sub_re]
    norm_num
    constructor <;> linarith [hs.1,hs.2]
  constructor <;> dsimp [sourceGrowthExponent]
  · linarith [abs_nonneg ((center q).re)]
  · linarith

private theorem scalar_high_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 1 ≤ z 1 →
      ‖scalar (center q) z‖ ≤ C*(z 1)^(1/2+|(center q).re|) := by
  obtain ⟨Ct,hCt,ht⟩ := weighted_tail_bounded (center q) 0 1 (by norm_num)
  let a := d4BMCompletedEisensteinCuspConstantCoefficient (center q) false
  let b := d4BMCompletedEisensteinCuspConstantCoefficient (center q) true
  refine ⟨‖a‖+‖b‖+Ct,by positivity,?_⟩
  intro z hz
  have hy : 0 < z 1 := lt_of_lt_of_le (by norm_num) hz
  have hpow (e : Bool) :
      ‖(z 1:ℂ)^(d4BMCompletedEisensteinCuspWeylExponent (center q) e)‖ ≤
        (z 1)^(1/2+|(center q).re|) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    apply Real.rpow_le_rpow_of_exponent_le hz
    cases e <;> simp [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign]
    · linarith [neg_le_abs ((center q).re)]
    · exact le_abs_self _
  have hp := Real.one_le_rpow hz (by positivity : 0 ≤ (1/2:ℝ)+|(center q).re|)
  have ht' : ‖tail (center q) z‖ ≤ Ct := by
    simpa only [Complex.cpow_zero,one_mul] using ht z hz
  have he : scalar (center q) z =
      a*(z 1:ℂ)^(d4BMCompletedEisensteinCuspWeylExponent (center q) false)+
      b*(z 1:ℂ)^(d4BMCompletedEisensteinCuspWeylExponent (center q) true)+tail (center q) z := by
    simp only [scalar,d4BMCompletedEisensteinCuspLeg,d4BMCompletedEisensteinCuspConstantPart,
      d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,
      mul_one,a,b,tail]
  rw [he]
  calc
    _ ≤ ‖a*(z 1:ℂ)^(d4BMCompletedEisensteinCuspWeylExponent (center q) false)‖+
        ‖b*(z 1:ℂ)^(d4BMCompletedEisensteinCuspWeylExponent (center q) true)‖+‖tail (center q) z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖a‖*((z 1)^(1/2+|(center q).re|))+
        ‖b‖*((z 1)^(1/2+|(center q).re|))+Ct*((z 1)^(1/2+|(center q).re|)) := by
      rw [norm_mul,norm_mul]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hpow false) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hpow true) (norm_nonneg _)))
        (ht'.trans (by nlinarith))
    _ = _ := by ring

private theorem square_cell_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, z ∈ fd →
      ‖fullSquarePotential q (coordinates z)‖ ≤ C*(max 1 z.im)^sourceGrowthExponent q := by
  obtain ⟨D,hD,hd⟩ := scalar_high_bound q
  have hc : Continuous (fun z : UpperHalfPlane => fullSquarePotential q (coordinates z)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply (fullSquarePotential_smooth q _ z.im_pos 0).continuousAt.comp
    have hcoord : Continuous (coordinates : UpperHalfPlane → Fin 2 → ℝ) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact UpperHalfPlane.continuous_re
      · exact UpperHalfPlane.continuous_im
    exact hcoord.continuousAt
  obtain ⟨C,hC⟩ := (truncated_cell_compact 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 0 (max C (D^2/2)),le_max_left _ _,?_⟩
  intro z hz
  by_cases hy : z.im ≤ 1
  · rw [max_eq_left hy,Real.one_rpow,mul_one]
    exact (hC z ⟨hz,hy⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hy1 : 1 ≤ z.im := (lt_of_not_ge hy).le
    have hpow : (z.im^(1/2+|(center q).re|))^2=z.im^sourceGrowthExponent q := by
      rw [← Real.rpow_natCast,← Real.rpow_mul z.im_pos.le]
      congr 1
      dsimp [sourceGrowthExponent]
      ring
    rw [max_eq_right hy1]
    have hb := hd (coordinates z) hy1
    change ‖scalar (center q) (coordinates z)‖ ≤ D*z.im^(1/2+|(center q).re|) at hb
    calc
      _ = ‖scalar (center q) (coordinates z)‖^2/2 := by
        simp only [fullSquarePotential,norm_mul,norm_div,norm_one,Complex.norm_ofNat]
        ring
      _ ≤ (D*z.im^(1/2+|(center q).re|))^2/2 := by gcongr
      _ = (D^2/2)*z.im^sourceGrowthExponent q := by rw [mul_pow,hpow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((le_max_right C _).trans (le_max_right 0 _)) (Real.rpow_nonneg z.im_pos.le _)

/-- One global bound for the full original source, including all modular images and cusp powers. -/
theorem fullSquarePotential_global_growth (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane,
      ‖fullSquarePotential q (coordinates z)‖ ≤
        C*(max 1 (max z.im (1/z.im)))^sourceGrowthExponent q := by
  obtain ⟨C,hC,hb⟩ := square_cell_bound q
  refine ⟨C,hC,?_⟩
  intro z
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  have hi : fullSquarePotential q (coordinates (A • z))=fullSquarePotential q (coordinates z) := by
    simp only [fullSquarePotential,xi_scalar_modular]
  have hh : (A • z).im ≤ max z.im (1/z.im) := by
    by_cases hc : A 1 0=0
    · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      rw [hn z,ModularGroup.im_T_zpow_smul]
      exact le_max_left _ _
    · exact (nonparabolic_height_le A hc z).trans (le_max_right _ _)
  rw [← hi]
  exact (hb _ hA).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (max_le_max_left 1 hh) (exponent_nonneg q)) hC)

private theorem denominator_bounds (d theta : ℝ) (hd : 0 ≤ d) :
    Real.exp (-d) ≤ denominator d theta ∧ denominator d theta ≤ Real.exp d := by
  rw [← Real.cosh_sub_sinh,← Real.cosh_add_sinh]
  have hs := Real.sinh_nonneg_iff.mpr hd
  dsimp [denominator]
  constructor <;> nlinarith [Real.cos_le_one theta,Real.neg_one_le_cos theta]

/-- The original circle source has controlled exponential growth, uniformly in horizontal position. -/
theorem source_global_growth (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d theta x k : ℝ, 0 ≤ d →
      ‖source q d theta x k‖ ≤ C*Real.exp (sourceGrowthExponent q*(d+|k|)) := by
  obtain ⟨C,hC,hb⟩ := fullSquarePotential_global_growth q
  refine ⟨C,hC,?_⟩
  intro d theta x k hd
  let Y : ℝ := Real.exp k/denominator d theta
  have hY : 0 < Y := div_pos (Real.exp_pos _) (denominator_pos _ _)
  let z : UpperHalfPlane := ⟨⟨logCircle d theta x k 0,Y⟩,hY⟩
  have he : coordinates z=logCircle d theta x k := by
    ext i
    fin_cases i
    · rfl
    · dsimp [coordinates,z,Y,logCircle,circle,height]
      ring
  have hh := denominator_bounds d theta hd
  have hbY : Y ≤ Real.exp (d+|k|) := by
    calc
      Y ≤ Real.exp k/Real.exp (-d) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hh.1
      _ = Real.exp (k+d) := by rw [← Real.exp_sub]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [le_abs_self k])
  have hbiY : 1/Y ≤ Real.exp (d+|k|) := by
    calc
      1/Y = denominator d theta/Real.exp k := by dsimp [Y]; field_simp
      _ ≤ Real.exp d/Real.exp k := div_le_div_of_nonneg_right hh.2 (Real.exp_pos _).le
      _ = Real.exp (d-k) := (Real.exp_sub d k).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [neg_le_abs k])
  have hm : max 1 (max z.im (1/z.im)) ≤ Real.exp (d+|k|) := by
    apply max_le
    · exact Real.one_le_exp_iff.mpr (by positivity)
    · exact max_le hbY hbiY
  have h := (hb z).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hm (exponent_nonneg q)) hC)
  rw [← Real.exp_mul] at h
  simpa only [he,source,mul_comm (d+|k|)] using h

/-- The full native mean obeys the same growth bound without a spectral projection. -/
theorem mean_global_growth (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d x k : ℝ, 0 ≤ d →
      ‖mean q d x k‖ ≤ C*Real.exp (sourceGrowthExponent q*(d+|k|)) := by
  obtain ⟨C,hC,hb⟩ := source_global_growth q
  refine ⟨C,hC,?_⟩
  intro d x k hd
  have h := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc 0 (2*Real.pi)))
    (Filter.Eventually.of_forall (fun theta => hb d theta x k hd))
  have hm : (volume.restrict (Ioc 0 (2*Real.pi))).real Set.univ=2*Real.pi := by
    simp [Measure.real,Real.volume_Ioc,Real.pi_pos.le]
  rw [hm] at h
  dsimp only [mean,average]
  rw [norm_mul,norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ (1/(2*Real.pi))*(C*Real.exp (sourceGrowthExponent q*(d+|k|))*(2*Real.pi)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

end
end RHTower.D4BMNativeCircle
