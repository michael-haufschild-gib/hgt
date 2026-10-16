import GaloisForLFunctions.HTGeometry.EvenEntireAxisType
import GaloisForLFunctions.RHTower.StripHorizontalShift
import GaloisForLFunctions.HTGeometry.CompactTestTransform
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Zeta23.Poisson.PaperFT

/-!
# Compact support from the recovered strip estimate

The contour shift gives literal support for the inverse transform. Real-axis
moments will provide smoothness independently of the support argument.
-/

open Complex Filter Topology Set MeasureTheory
open scoped FourierTransform ContDiff
noncomputable section
namespace GaloisForLFunctions.HTGeometry

def angularInverse (Q : ℂ → ℂ) (u : ℝ) : ℂ :=
  ∫ x : ℝ,Q x*Complex.exp (I*(u : ℂ)*(x : ℂ))

theorem angularInverse_even {Q : ℂ → ℂ} (he : Function.Even Q) :
    Function.Even (angularInverse Q) := by
  intro u
  rw [angularInverse,angularInverse,← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Complex.ofReal_neg]
  rw [he (x : ℂ)]
  congr 2
  ring

theorem angularInverse_zero_of_type_lt {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q)
    {C A u : ℝ} (hC : 0≤C)
    (hb : ∀ z,‖Q z‖≤C*Real.exp (A*|z.im|)*(1+z.re^2)⁻¹) (hu : A<u) :
    angularInverse Q u=0 := by
  let F := fun z : ℂ => Q z*Complex.exp (I*(u : ℂ)*z)
  have hF : Differentiable ℂ F := hQ.mul (by fun_prop)
  have hpoint (z : ℂ) (hz : 0≤z.im) :
      ‖F z‖≤C*Real.exp ((A-u)*z.im)*(1+z.re^2)⁻¹ := by
    have he : (I*(u : ℂ)*z).re= -u*z.im := by simp [Complex.mul_re,Complex.mul_im]
    dsimp only [F]
    rw [norm_mul,Complex.norm_exp,he]
    calc
      _ ≤ (C*Real.exp (A*|z.im|)*(1+z.re^2)⁻¹)*Real.exp (-u*z.im) :=
        mul_le_mul_of_nonneg_right (hb z) (Real.exp_nonneg _)
      _ = _ := by
        rw [abs_of_nonneg hz,show (A-u)*z.im=A*z.im+(-u*z.im) by ring,Real.exp_add]
        ring
  have hshift (c : ℝ) (hc : 0≤c) :
      (∫ x : ℝ,F ((x : ℂ)+(c : ℂ)*I))=angularInverse Q u := by
    apply RHTower.integral_horizontal_shift_of_upper_inv_one_add_sq_decay hc
      (fun z _ _ => hF z)
    intro z hz _
    apply (hpoint z hz).trans
    have hex : Real.exp ((A-u)*z.im)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hz)
    calc
      _ ≤ C*1*(1+z.re^2)⁻¹ := by gcongr
      _ = _ := by ring
  let J : ℝ := ∫ x : ℝ,(1+x^2)⁻¹
  have hbound (c : ℝ) (hc : 0≤c) :
      ‖angularInverse Q u‖≤(C*Real.exp ((A-u)*c))*J := by
    rw [← hshift c hc]
    have hint := integrable_inv_one_add_sq.const_mul (C*Real.exp ((A-u)*c))
    have hh := norm_integral_le_of_norm_le hint (Eventually.of_forall fun x : ℝ => by
      have hp := hpoint ((x : ℂ)+(c : ℂ)*I) (by simpa using hc)
      simpa using hp)
    simpa only [integral_const_mul,J] using hh
  have hlim : Tendsto (fun c : ℝ => (C*Real.exp ((A-u)*c))*J) atTop (𝓝 0) := by
    have hl : Tendsto (fun c : ℝ => (u-A)*c) atTop atTop :=
      tendsto_id.const_mul_atTop (sub_pos.mpr hu)
    have hn : Tendsto (fun c : ℝ => (A-u)*c) atTop atBot := by
      convert tendsto_neg_atTop_atBot.comp hl using 1
      funext c
      dsimp only [Function.comp_def]
      ring
    simpa using ((Real.tendsto_exp_atBot.comp hn).const_mul C).mul_const J
  have hzero : ‖angularInverse Q u‖≤0 := ge_of_tendsto hlim
    (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc; exact hbound c hc)
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

theorem angularInverse_hasCompactSupport {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q)
    (he : Function.Even Q) {C A : ℝ} (hC : 0≤C)
    (hb : ∀ z,‖Q z‖≤C*Real.exp (A*|z.im|)*(1+z.re^2)⁻¹) :
    HasCompactSupport (angularInverse Q) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -A) (b := A))
  intro u hu
  by_contra hh
  have hn : angularInverse Q u≠0 := hu
  simp only [mem_Icc,not_and_or,not_le] at hh
  rcases hh with hh | hh
  · have hx := angularInverse_zero_of_type_lt hQ hC hb (show A < -u by linarith)
    exact hn ((angularInverse_even he u).symm.trans hx)
  · exact hn (angularInverse_zero_of_type_lt hQ hC hb hh)

theorem integrable_moments_of_real_decay {Q : ℂ → ℂ} (hQ : Continuous Q)
    (hd : ∀ n : ℕ,∃ M : ℝ,∀ x : ℝ,‖Q x‖*(1+|x|)^n≤M) (n : ℕ) :
    Integrable fun x : ℝ => ‖x‖^n*‖Q x‖ := by
  obtain ⟨M,hM⟩ := hd (n+2)
  have hc : Continuous (fun x : ℝ => ‖x‖^n*‖Q x‖) :=
    (continuous_norm.pow n).mul ((hQ.comp Complex.continuous_ofReal).norm)
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul M) hc.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  have hweight : ‖x‖^n*(1+x^2)≤(1+|x|)^(n+2) := by
    rw [Real.norm_eq_abs,pow_add]
    have hn : |x|^n≤(1+|x|)^n := pow_le_pow_left₀ (abs_nonneg _) (by linarith) n
    have h2 : 1+x^2≤(1+|x|)^2 := by nlinarith [sq_abs x,abs_nonneg x]
    exact mul_le_mul hn h2 (by positivity) (by positivity)
  calc
    _ = ‖Q x‖*(‖x‖^n*(1+x^2)) := by ring
    _ ≤ ‖Q x‖*(1+|x|)^(n+2) := mul_le_mul_of_nonneg_left hweight (norm_nonneg _)
    _ ≤ M := hM x

theorem angularInverse_eq_fourier (Q : ℂ → ℂ) (u : ℝ) :
    angularInverse Q u=𝓕 (fun x : ℝ => Q x) (-u/(2*Real.pi)) := by
  rw [angularInverse,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rw [mul_comm (Q _)]
  congr 2
  push_cast
  field_simp

theorem angularInverse_smooth {Q : ℂ → ℂ} (hQ : Continuous Q)
    (hd : ∀ n : ℕ,∃ M : ℝ,∀ x : ℝ,‖Q x‖*(1+|x|)^n≤M) :
    ContDiff ℝ ∞ (angularInverse Q) := by
  have hh : ContDiff ℝ ∞ (𝓕 (fun x : ℝ => Q x)) :=
    Real.contDiff_fourier (fun n _ => integrable_moments_of_real_decay hQ hd n)
  have he : angularInverse Q=(𝓕 (fun x : ℝ => Q x)) ∘ (fun u => -u/(2*Real.pi)) :=
    funext (angularInverse_eq_fourier Q)
  rw [he]
  exact hh.comp (by fun_prop)

def compactInverse (Q : ℂ → ℂ) (u : ℝ) : ℂ :=
  ((2*Real.pi)⁻¹ : ℝ) • angularInverse Q u

theorem compactInverse_eq_fourierInv (Q : ℂ → ℂ) :
    compactInverse Q=𝓕⁻ (fun x : ℝ => Q ((2*Real.pi*x : ℝ) : ℂ)) := by
  funext u
  have hpi : (2*Real.pi : ℝ)≠0 := by positivity
  have hc := Measure.integral_comp_mul_left
    (fun x : ℝ => Q x*Complex.exp (I*(u : ℂ)*(x : ℂ))) (2*Real.pi)
  rw [abs_of_pos (inv_pos.mpr (by positivity : 0<2*Real.pi))] at hc
  rw [compactInverse,angularInverse,← hc,Real.fourierInv_eq_fourier_neg,
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rw [mul_comm (Q _)]
  congr 2
  push_cast
  ring

/-- The constructed inverse is a smooth compact even source whose entire
Fourier transform is the prescribed factor. -/
theorem exists_smooth_compact_source {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q)
    (he : Function.Even Q) (hs : SubquadraticType Q)
    (hd : ∀ n : ℕ,∃ M : ℝ,∀ x : ℝ,‖Q x‖*(1+|x|)^n≤M)
    {R T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (him : ∀ y : ℝ,0≤y → ‖Q ((y : ℂ)*I)‖≤R*Real.exp (T*y)) :
    ∃ f : ℝ → ℂ,ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ Function.Even f ∧
      ∀ z,Zeta23.paperFT f z=Q z := by
  obtain ⟨M,hM⟩ := hd 2
  obtain ⟨C,A,hC,_,hb⟩ := quadratic_strip_bound_of_axes hQ he hs hR hT hM him
  have has := angularInverse_hasCompactSupport hQ he hC hb
  have hac := angularInverse_smooth hQ.continuous hd
  have hfc : ContDiff ℝ ∞ (compactInverse Q) := hac.const_smul _
  have hfs : HasCompactSupport (compactInverse Q) := has.smul_left (f := fun _ => ((2*Real.pi)⁻¹ : ℝ))
  have hfe : Function.Even (compactInverse Q) := by
    intro u
    simp only [compactInverse,angularInverse_even he u]
  let V := fun x : ℝ => Q ((2*Real.pi*x : ℝ) : ℂ)
  have hQr : Continuous (fun x : ℝ => Q x) := hQ.continuous.comp Complex.continuous_ofReal
  have hQi : Integrable (fun x : ℝ => Q x) := (integrable_norm_iff hQr.aestronglyMeasurable).mp
    (by simpa only [pow_zero,one_mul] using integrable_moments_of_real_decay hQ.continuous hd 0)
  have hVi : Integrable V := hQi.comp_mul_left' (by positivity)
  have hVc : Continuous V := hQ.continuous.comp (by fun_prop)
  have hfi : Integrable (compactInverse Q) := hfc.continuous.integrable_of_hasCompactSupport hfs
  have hFourier : 𝓕 V=(fun x => compactInverse Q (-x)) := by
    funext x
    rw [compactInverse_eq_fourierInv,Real.fourierInv_eq_fourier_neg,neg_neg]
  have hFi : Integrable (𝓕 V) := by rw [hFourier]; exact hfi.comp_neg
  have hfinv : 𝓕 (compactInverse Q)=V := by
    rw [compactInverse_eq_fourierInv]
    exact hVc.fourier_fourierInv_eq hVi hFi
  have hreal (x : ℝ) : Zeta23.paperFT (compactInverse Q) x=Q x := by
    rw [Zeta23.paperFT_ofReal_eq_fourier,hfinv]
    change Q ((2*Real.pi*(-x/(2*Real.pi)) : ℝ) : ℂ)=Q x
    rw [show 2*Real.pi*(-x/(2*Real.pi)) = -x by field_simp,Complex.ofReal_neg,he (x : ℂ)]
  refine ⟨compactInverse Q,hfc,hfs,hfe,fun z => ?_⟩
  apply sub_eq_zero.mp
  have hft : Differentiable ℂ (Zeta23.paperFT (compactInverse Q)) :=
    differentiable_testTransform hfc.continuous hfs
  exact entire_eq_zero_of_vanishing_on_real_interval (hft.sub hQ)
    (t₀ := 0) (r := 1) (by norm_num) (fun x _ => sub_eq_zero.mpr (hreal x)) z

end GaloisForLFunctions.HTGeometry
