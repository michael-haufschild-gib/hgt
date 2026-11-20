import GaloisForLFunctions.ExceptionalLayerTheory.TheGaussianObservationBoundary
import GaloisForLFunctions.SelbergClass.DegreeOne.VerticalStirling

/-!
# The logarithmic correction at the Gaussian observation boundary

A level front can depend on a logarithmic displacement after the leading
rate cancels, as in Yang–Zhang–Ying (arXiv:2611.14200, equations S46–S48).
For the actual Gaussian Mellin kernel take d = Re ρ − σ and v = (t−Im ρ)/2.
At damping exp(−L), its norm is asymptotic to √(2π)/2 times
exp((dL−πv+(d−1)log v)/2). This holds for arbitrary height-dependent
damping. The critical logarithmic displacement is (1−d)log(v)/d.
-/

noncomputable section
open Complex Filter Topology RHTower
open GaloisForLFunctions.SelbergClass.DegreeOne
namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev gammaHeight (ρ : ℂ) (t : ℝ) := (t-ρ.im)/2

/-- Residual log amplitude after cancelling the exponential and power
factors in vertical Stirling approximation. -/
def gaussianLogExcess (ρ : ℂ) (σ L t : ℝ) : ℝ :=
  ((ρ.re-σ)*L-Real.pi*gammaHeight ρ t+(ρ.re-σ-1)*Real.log (gammaHeight ρ t))/2

/-- Norm of one Gaussian mode at a prescribed logarithmic damping L. -/
def gaussianModeNorm (ρ : ℂ) (σ L t : ℝ) : ℝ :=
  ‖gaussianMBKernel (Real.exp (-L)) (ρ-((σ:ℂ)+(t:ℂ)*I))‖

private theorem mode_norm_factor (ρ : ℂ) (σ L t : ℝ) :
    gaussianModeNorm ρ σ L t =
      (1/2:ℝ)*‖Complex.Gamma (((ρ.re-σ)/2:ℝ)+(gammaHeight ρ t:ℂ)*I)‖*
      Real.exp (L*(ρ.re-σ)/2) := by
  have harg : (ρ-((σ:ℂ)+(t:ℂ)*I))/2 =
      (starRingEnd ℂ) ((((ρ.re-σ)/2:ℝ):ℂ)+(gammaHeight ρ t:ℂ)*I) := by
    apply Complex.ext <;>
      simp only [Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.conj_re,Complex.conj_im,
        Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,Complex.mul_re,
        Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,gammaHeight] <;> ring
  unfold gaussianModeNorm gaussianMBKernel
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos _),←Real.exp_mul]
  norm_num only [norm_div,norm_one,Complex.norm_two]
  rw [harg,RHTower.norm_Gamma_conj]
  congr 2
  simp only [Complex.neg_re,Complex.conj_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
  ring

private theorem shape_modulus (a v : ℝ) (hv : 0<v) :
    ‖stirlingShape a v‖=v^(a-1/2)*Real.exp (-(Real.pi*v/2)) := by
  unfold stirlingShape
  rw [norm_mul,mul_comm I,Complex.norm_exp_ofReal_mul_I,one_mul,Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv.le _) (Real.exp_pos _).le)]

/-- Changing the logarithmic damping multiplies the mode magnitude by
a factor determined entirely by its real coordinate. -/
theorem gaussian_mode_damping_factor (ρ : ℂ) (σ L t : ℝ) :
    gaussianModeNorm ρ σ L t = gaussianModeNorm ρ σ 0 t*Real.exp (L*(ρ.re-σ)/2) := by
  rw [mode_norm_factor,mode_norm_factor,zero_mul,zero_div,Real.exp_zero,mul_one]

/-- All damping schedules share exactly the same relative approximation
error. Neither a bounded slope nor a limit for the schedule is required. -/
theorem gaussian_mode_relative_asymptotic (ρ : ℂ) (σ : ℝ) (L : ℝ → ℝ) :
    Tendsto (fun t => gaussianModeNorm ρ σ (L t) t / Real.exp (gaussianLogExcess ρ σ (L t) t))
      atTop (𝓝 (Real.sqrt (2*Real.pi)/2)) := by
  let a : ℝ := (ρ.re-σ)/2
  have hv : Tendsto (gammaHeight ρ) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num : 0<(2:ℝ)) (by
      simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-ρ.im)
        (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
  have h := (((tendsto_Gamma_div_stirlingShape a).norm).comp hv).div_const 2
  rw [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)] at h
  apply h.congr'
  filter_upwards [hv.eventually_gt_atTop 0] with t ht
  let v := gammaHeight ρ t
  change ‖Complex.Gamma ((a:ℂ)+(v:ℂ)*I)/stirlingShape a v‖/2=_
  rw [norm_div,shape_modulus a v ht,mode_norm_factor,Real.rpow_def_of_pos ht]
  have ex : gaussianLogExcess ρ σ (L t) t =
      L t*(ρ.re-σ)/2 + (Real.log v*(a-1/2) - Real.pi*v/2) := by
    unfold gaussianLogExcess
    dsimp only [a,v]
    ring
  rw [ex,Real.exp_add,Real.exp_sub,Real.exp_neg]
  dsimp only [v,a]
  field_simp

/-- An arbitrary finite displacement of the tuned logarithmic damping
has a strictly positive limiting signal with its full prefactor. -/
theorem gaussian_mode_finite_excess (ρ : ℂ) (σ : ℝ) (L : ℝ → ℝ) {b : ℝ}
    (hb : Tendsto (fun t => gaussianLogExcess ρ σ (L t) t) atTop (𝓝 b)) :
    Tendsto (fun t => gaussianModeNorm ρ σ (L t) t) atTop (𝓝 (Real.sqrt (2*Real.pi)/2*Real.exp b)) := by
  exact ((gaussian_mode_relative_asymptotic ρ σ L).mul hb.rexp).congr fun t =>
    div_mul_cancel₀ _ (Real.exp_ne_zero _)

/-- Damping displacement tends to +∞ exactly when the mode norm tends
to +∞. Oscillating damping schedules are included in the equivalence. -/
theorem gaussian_mode_grows_iff_excess (ρ : ℂ) (σ : ℝ) (L : ℝ → ℝ) :
    Tendsto (fun t => gaussianModeNorm ρ σ (L t) t) atTop atTop ↔
      Tendsto (fun t => gaussianLogExcess ρ σ (L t) t) atTop atTop := by
  let f := fun t => gaussianModeNorm ρ σ (L t) t
  let b := fun t => gaussianLogExcess ρ σ (L t) t
  have h := gaussian_mode_relative_asymptotic ρ σ L
  have hc : 0<Real.sqrt (2*Real.pi)/2 := by positivity
  have hp : ∀ᶠ t in atTop, 0<f t := by
    filter_upwards [h.eventually_const_lt hc] with t ht
    exact (div_pos_iff_of_pos_right (Real.exp_pos _)).mp ht
  constructor
  · intro htop
    have hi := h.inv₀ hc.ne'
    have he : Tendsto (fun t => Real.exp (b t)) atTop atTop := by
      apply (htop.atTop_mul_pos (inv_pos.mpr hc) hi).congr'
      filter_upwards [hp] with t ht
      change f t*(f t/Real.exp (b t))⁻¹=Real.exp (b t)
      field_simp [ht.ne']
    simpa only [Function.comp_def,Real.log_exp] using Real.tendsto_log_atTop.comp he
  · intro htop
    apply ((Real.tendsto_exp_atTop.comp htop).atTop_mul_pos hc h).congr
    intro t
    change Real.exp (b t)*(f t/Real.exp (b t))=f t
    rw [mul_comm,div_mul_cancel₀ _ (Real.exp_ne_zero _)]

/-- Solving for the damping at any prescribed level b gives an exact
logarithmic term and the limiting constant √(2π) exp(b)/2. -/
theorem gaussian_mode_at_corrected_boundary {ρ : ℂ} {σ : ℝ} (hd : ρ.re≠σ) (b : ℝ) :
    Tendsto (fun t => gaussianModeNorm ρ σ
      ((Real.pi*gammaHeight ρ t + (1-(ρ.re-σ))*Real.log (gammaHeight ρ t)+2*b)/(ρ.re-σ)) t)
      atTop (𝓝 (Real.sqrt (2*Real.pi)/2*Real.exp b)) := by
  apply gaussian_mode_finite_excess
  apply tendsto_const_nhds.congr
  intro t
  unfold gaussianLogExcess
  field_simp [sub_ne_zero.mpr hd]
  ring

#print axioms gaussian_mode_relative_asymptotic
#print axioms gaussian_mode_finite_excess
#print axioms gaussian_mode_grows_iff_excess
#print axioms gaussian_mode_at_corrected_boundary
end GaloisForLFunctions.ExceptionalLayerTheory
