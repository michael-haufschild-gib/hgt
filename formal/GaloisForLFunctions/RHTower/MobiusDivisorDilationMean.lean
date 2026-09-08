import GaloisForLFunctions.RHTower.DivisorContinuousHeadMellin
import GaloisForLFunctions.RHTower.DivisorCoreMellinMean
import GaloisForLFunctions.HTGeometry.MellinConjugate

/-!
# Physical signed dilation mean of the processed divisor source

The literal real head has an absolutely convergent inverse-cube paired
average at every positive dilation. Its Mellin transform and logarithmic
L1/L2 domains identify that average with the complete polarized contour.
Consequently its large-dilation limit is the actual signed source residue.
The core is fixed; no uniform renewal estimate or residue sign is assumed.
-/

noncomputable section
open Complex Filter Set Topology MeasureTheory Finset
open GaloisForLFunctions.HTGeometry
namespace RHTower

/-- The actual signed dilation average of the continuous processed divisor head. -/
def mobiusDivisorDilationMean (P : Finset ℕ) (Y : ℝ) : ℝ :=
  ∫ x in Ioi (1:ℝ), mobiusDivisorContinuousHead P (Y*x)*mobiusDivisorContinuousHead P x/x^3

/-- The physical signed average is absolutely convergent for every positive dilation. -/
theorem integrable_mobiusDivisorDilationMean_kernel (P : Finset ℕ) {Y : ℝ} (hY : 0<Y) :
    IntegrableOn (fun x : ℝ =>
      mobiusDivisorContinuousHead P (Y*x)*mobiusDivisorContinuousHead P x/x^3) (Ioi 1) := by
  obtain ⟨C,hC,hb⟩ := exists_bound_mobiusDivisorContinuousHead P
  have hm : Measurable (fun x : ℝ =>
      mobiusDivisorContinuousHead P (Y*x)*mobiusDivisorContinuousHead P x/x^3) :=
    (((measurable_mobiusDivisorContinuousHead P).comp (by fun_prop)).mul
      (measurable_mobiusDivisorContinuousHead P)).div (by fun_prop)
  have hi : IntegrableOn (fun x : ℝ => (C^2*Real.sqrt Y)*x^(-2:ℝ)) (Ioi 1) :=
    ((integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ)<1)).mpr
      (by norm_num : (-2 : ℝ) < -1)).const_mul _
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0<x := lt_trans zero_lt_one hx
  have ha := mul_le_mul (hb (Y*x)) (hb x) (abs_nonneg _) (by positivity)
  rw [Real.sqrt_mul hY.le] at ha
  have hh : |mobiusDivisorContinuousHead P (Y*x)| * |mobiusDivisorContinuousHead P x| ≤
      (C^2*Real.sqrt Y)*x := by
    calc
      _ ≤ (C*(Real.sqrt Y*Real.sqrt x))*(C*Real.sqrt x) := ha
      _ = (C^2*Real.sqrt Y)*(Real.sqrt x)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hx0.le]
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (pow_pos hx0 3),
    Real.rpow_neg hx0.le,Real.rpow_two,← div_eq_mul_inv]
  apply (div_le_div_of_nonneg_right hh (pow_pos hx0 3).le).trans
  have hxne : x ≠ 0 := hx0.ne'
  field_simp
  rfl

private lemma dilation_integral_from_zero (P : Finset ℕ) (Y : ℝ) :
    (∫ x in Ioi (0:ℝ), mobiusDivisorContinuousHead P (Y*x)*mobiusDivisorContinuousHead P x/x^3) =
      mobiusDivisorDilationMean P Y := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  intro x hx
  have hx1 : x ≤ 1 := le_of_not_gt hx.2
  rw [mobiusDivisorContinuousHead_eq_zero P hx1,mul_zero,zero_div]

private lemma paired_physical_mellin (P : Finset ℕ) (Y : ℝ) :
    mellin (fun x : ℝ => (starRingEnd ℂ) (mobiusDivisorContinuousHead P (Y*x):ℂ)*
      (mobiusDivisorContinuousHead P x:ℂ)) (-2) = (mobiusDivisorDilationMean P Y:ℂ) := by
  rw [mellin]
  have he (x : ℝ) :
      (x:ℂ)^((-2:ℂ)-1) • ((starRingEnd ℂ) (mobiusDivisorContinuousHead P (Y*x):ℂ)*
        (mobiusDivisorContinuousHead P x:ℂ)) =
      (mobiusDivisorContinuousHead P (Y*x)*mobiusDivisorContinuousHead P x/x^3:ℝ) := by
    rw [show (-2:ℂ)-1=-(3:ℂ) by norm_num,Complex.cpow_neg]
    norm_num only [Complex.cpow_ofNat,Complex.conj_ofReal,smul_eq_mul]
    push_cast
    ring
  simp_rw [he]
  rw [integral_complex_ofReal,dilation_integral_from_zero]

private lemma exp_dilation_mellin (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀p∈P,p.Prime) (a : ℝ) {s : ℂ} (hs : 1/2<s.re) :
    mellin (fun x : ℝ => (mobiusDivisorContinuousHead P (Real.exp a*x):ℂ)) (-s) =
      Complex.exp ((a:ℂ)*s)*divisorCoreMellin P s := by
  rw [mellin_comp_mul_left (fun x : ℝ => (mobiusDivisorContinuousHead P x : ℂ))
    (-s) (Real.exp_pos a),neg_neg,smul_eq_mul,
    mellin_mobiusDivisorContinuousHead_eq_core P hP hprime hs]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos a).ne'),
    ← Complex.ofReal_log (Real.exp_pos a).le,Real.log_exp]

private lemma physical_pairing_integrand (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀p∈P,p.Prime) (a t : ℝ) :
    (starRingEnd ℂ) (mellin (fun x : ℝ => (mobiusDivisorContinuousHead P (Real.exp a*x):ℂ))
      ((-1:ℂ)+(t:ℂ)*I))*
      mellin (fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ)) ((-1:ℂ)+(t:ℂ)*I) =
    Complex.exp ((a:ℂ)*(1+(t:ℂ)*I))*divisorCoreMellinPair P (1+(t:ℂ)*I) := by
  have hconj := mellin_conj_of_conj_invariant
    (F := fun x : ℝ => (mobiusDivisorContinuousHead P (Real.exp a*x):ℂ))
    (by intro x; simp) ((-1:ℂ)+(t:ℂ)*I)
  rw [← hconj]
  have h₁ : (starRingEnd ℂ) ((-1:ℂ)+(t:ℂ)*I)=-(1+(t:ℂ)*I) := by simp; ring
  have h₂ : (-1:ℂ)+(t:ℂ)*I=-(1-(t:ℂ)*I) := by ring
  rw [h₁,h₂,exp_dilation_mellin P hP hprime a (by simp; norm_num),
    mellin_mobiusDivisorContinuousHead_eq_core P hP hprime (by simp; norm_num),
    divisorCoreMellinPair]
  have he : 2-((1:ℂ)+(t:ℂ)*I)=1-(t:ℂ)*I := by ring
  rw [he]
  ring

/-- Exact identification of the proved Mellin contour with the physical signed
average. The complete polarized pairing and both source domains are discharged. -/
theorem mobiusDivisorDilationMean_eq_contour (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀p∈P,p.Prime) (a : ℝ) :
    (mobiusDivisorDilationMean P (Real.exp a):ℂ)=divisorCoreMellinContourMean P a := by
  have h₁ := integrable_log_mobiusDivisorContinuousHead P (Real.exp_pos a)
  have h₂ := memLp_log_mobiusDivisorContinuousHead P (Real.exp_pos a)
  have h₃ := integrable_log_mobiusDivisorContinuousHead P (by norm_num : (0:ℝ)<1)
  have h₄ := memLp_log_mobiusDivisorContinuousHead P (by norm_num : (0:ℝ)<1)
  simp only [one_mul] at h₃ h₄
  have h := integral_conj_mellin_line_mul_mellin_line h₁ h₂ h₃ h₄
  norm_num only [Complex.ofReal_neg,Complex.ofReal_one,show (2:ℝ)*(-1)=-2 by norm_num,
    Complex.ofReal_ofNat] at h
  simp_rw [physical_pairing_integrand P hP hprime a] at h
  rw [paired_physical_mellin] at h
  rw [divisorCoreMellinContourMean,h]
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- The actual signed head average has the fixed-core residue limit at
unbounded dilation. It is not merely an asymptotic of an auxiliary contour. -/
theorem tendsto_mobiusDivisorDilationMean (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀p∈P,p.Prime) :
    Tendsto (mobiusDivisorDilationMean P) atTop (𝓝 (divisorCoreMellinPairResidue P).re) := by
  have hc := (tendsto_divisorCoreMellinContourMean P hP).comp Real.tendsto_log_atTop
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Y hY
  simp only [Function.comp_apply]
  rw [← mobiusDivisorDilationMean_eq_contour P hP hprime (Real.log Y),
    Real.exp_log hY,Complex.ofReal_re]

end RHTower
