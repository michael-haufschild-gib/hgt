import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyHighFrequency
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyBoundaryAmplification
import GaloisForLFunctions.HTGeometry.GammaVerticalRatioBound
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! The central Mellin multiplier of the actual Cauchy transform has the sharp
strict envelope `2^((1−Re w)/2)` on the source half-plane. A normalized Gamma
quotient is Schur: vertical Gamma-ratio bounds give polynomial growth, and
its exact imaginary-axis modulus feeds the half-plane maximum principle.
The high-frequency limit proves that the envelope is the exact supremum. -/

open Complex Set Filter Asymptotics
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerCauchyMellinSymbol MayerCauchyHighFrequency
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchySchur

/-- The actual central Cauchy multiplier with its sharp exponential factor removed. -/
def normalizedSymbol (w : ℂ) : ℂ := (2 : ℂ)^((w-1)/2)*symbol w (w/2)

/-- Recovery of the actual central multiplier from its normalization. -/
theorem symbol_half_eq_normalized (w : ℂ) :
    symbol w (w/2)=(2 : ℂ)^((1-w)/2)*normalizedSymbol w := by
  rw [normalizedSymbol,← mul_assoc,← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0),
    show (1-w)/2+(w-1)/2=0 by ring,Complex.cpow_zero,one_mul]

/-- Duplication identifies the normalization with the quarter-shift Gamma quotient. -/
theorem normalized_eq_gamma {w : ℂ} (hw : 0 < w.re) :
    normalizedSymbol w=Gamma ((w+2)/4)^2/
      (Gamma ((w+1)/4)*Gamma ((w+3)/4)) := by
  rw [normalizedSymbol,symbol_duplication hw,← mul_assoc,
    ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0),
    show (w-1)/2+(1-w)/2=0 by ring,Complex.cpow_zero,one_mul]
  rw [show (w/2+1)/2=(w+2)/4 by ring,
    show (w+1-w/2)/2=(w+2)/4 by ring,pow_two]

/-- The normalized multiplier is holomorphic across the imaginary axis. -/
theorem differentiableAt_normalizedSymbol {w : ℂ} (hw : -1 < w.re) :
    DifferentiableAt ℂ normalizedSymbol w := by
  have hp : Differentiable ℂ (fun v : ℂ => (2 : ℂ)^((v-1)/2)) := by
    simp only [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    fun_prop
  exact (hp w).mul (MayerCauchyBoundaryAmplification.differentiableAt_central hw)

/-- Exact strict boundary norm after removing the exponential spectral factor. -/
theorem normalized_boundary_norm_sq (τ : ℝ) :
    ‖normalizedSymbol ((τ : ℂ)*I)‖^2=
      1-1/(2*Real.cosh (Real.pi*τ/4)^2) := by
  have hre : ((((τ : ℂ)*I)-1)/2).re=(-1/2 : ℝ) := by simp
  have hp : ‖(2 : ℂ)^((((τ : ℂ)*I)-1)/2)‖=(2 : ℝ)^(-1/2 : ℝ) := by
    simpa only [ofReal_ofNat,hre] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ)<2) ((((τ : ℂ)*I)-1)/2)
  have hpsq : ((2 : ℝ)^(-1/2 : ℝ))^2=(1/2 : ℝ) := by
    rw [← Real.rpow_natCast ((2 : ℝ)^(-1/2 : ℝ)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hm := MayerCauchyBoundaryAmplification.symbol_boundary_norm_sq 0 τ
  simp only [ofReal_zero,zero_add,mul_zero,zero_div,Real.cos_zero,one_pow] at hm
  have hu : ((τ : ℂ)*I)/2=(τ : ℂ)/2*I := by ring
  have hC : Real.cosh (Real.pi*τ/2)=2*Real.cosh (Real.pi*τ/4)^2-1 := by
    have h := Real.cosh_add (Real.pi*τ/4) (Real.pi*τ/4)
    rw [show Real.pi*τ/4+Real.pi*τ/4=Real.pi*τ/2 by ring] at h
    nlinarith only [h,Real.cosh_sq (Real.pi*τ/4)]
  have hS : 1+Real.sinh (Real.pi*τ/4)^2=Real.cosh (Real.pi*τ/4)^2 := by
    linarith only [Real.cosh_sq (Real.pi*τ/4)]
  rw [normalizedSymbol,norm_mul,mul_pow,hp,hpsq,hu,hm,hS,hC]
  field_simp [(Real.cosh_pos (Real.pi*τ/4)).ne']

/-- The normalized multiplier has modulus strictly below one at every boundary point. -/
theorem normalized_boundary_norm_lt_one (τ : ℝ) : ‖normalizedSymbol ((τ : ℂ)*I)‖ < 1 := by
  have h := normalized_boundary_norm_sq τ
  have hp : 0 < 1/(2*Real.cosh (Real.pi*τ/4)^2) := by positivity
  nlinarith only [h,hp,norm_nonneg (normalizedSymbol ((τ : ℂ)*I))]

#print axioms symbol_half_eq_normalized
#print axioms normalized_eq_gamma
#print axioms differentiableAt_normalizedSymbol
#print axioms normalized_boundary_norm_sq
#print axioms normalized_boundary_norm_lt_one
private def gammaNorm (x y : ℝ) : ℝ := ‖Gamma ((x : ℂ)+(y : ℂ)*I)‖

private theorem gammaNorm_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < gammaNorm x y := by
  exact norm_pos_iff.mpr (GaloisForLFunctions.gammaLine_ne_zero hx y)

private theorem gammaNorm_recurrence {x : ℝ} (hx : 0 < x) (y : ℝ) :
    gammaNorm (x+1) y=‖(x : ℂ)+(y : ℂ)*I‖*gammaNorm x y := by
  have hz : (x : ℂ)+(y : ℂ)*I ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [add_re,ofReal_re,mul_I_re,ofReal_im,zero_re] at he
    linarith only [hx,he]
  unfold gammaNorm
  rw [show ((x+1 : ℝ) : ℂ)+(y : ℂ)*I=((x : ℂ)+(y : ℂ)*I)+1 by push_cast; ring,
    Complex.Gamma_add_one _ hz,norm_mul]

private theorem real_midpoint_bound {x : ℝ} (hx : 1/2 ≤ x) :
    Real.Gamma x^2 ≤ Real.Gamma (x-1/4)*Real.Gamma (x+1/4) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hm : 0 < x-1/4 := by linarith only [hx]
  have hp : 0 < x+1/4 := by linarith only [hx]
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hm hp
    (a := 1/2) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
  rw [show (1/2 : ℝ)*(x-1/4)+(1/2)*(x+1/4)=x by ring,
    ← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at h
  have hs := (sq_le_sq₀ (Real.Gamma_pos_of_pos hx0).le
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr h
  simpa only [mul_pow,Real.sq_sqrt (Real.Gamma_pos_of_pos hm).le,
    Real.sq_sqrt (Real.Gamma_pos_of_pos hp).le] using hs

private theorem gamma_midpoint_bound {x : ℝ} (hx : 1/2 ≤ x) (y : ℝ) :
    gammaNorm x y^2/(gammaNorm (x-1/4) y*gammaNorm (x+1/4) y) ≤
      ‖((x-1/4 : ℝ) : ℂ)+(y : ℂ)*I‖/(x-1/4) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hm : 0 < x-1/4 := by linarith only [hx]
  have hp : 0 < x+1/4 := by linarith only [hx]
  have h3 : 0 < x+3/4 := by linarith only [hx]
  have h1 := _root_.HTGeometry.norm_Gamma_div_le hx0
    (b := x+1/4) (by linarith) y
  have h2 := _root_.HTGeometry.norm_Gamma_div_le hx0
    (b := x+3/4) (by linarith) y
  change gammaNorm x y/gammaNorm (x+1/4) y ≤ Real.Gamma x/Real.Gamma (x+1/4) at h1
  change gammaNorm x y/gammaNorm (x+3/4) y ≤ Real.Gamma x/Real.Gamma (x+3/4) at h2
  have hrec : gammaNorm (x+3/4) y=
      ‖((x-1/4 : ℝ) : ℂ)+(y : ℂ)*I‖*gammaNorm (x-1/4) y := by
    simpa only [show x-1/4+1=x+3/4 by ring] using gammaNorm_recurrence hm y
  have hrrec : Real.Gamma (x+3/4)=(x-1/4)*Real.Gamma (x-1/4) := by
    rw [show x+3/4=(x-1/4)+1 by ring,Real.Gamma_add_one hm.ne']
  have hzm : 0 < ‖((x-1/4 : ℝ) : ℂ)+(y : ℂ)*I‖ := by
    apply norm_pos_iff.mpr
    intro h
    have he := congrArg Complex.re h
    simp only [add_re,ofReal_re,mul_I_re,ofReal_im,zero_re] at he
    linarith only [hm,he]
  have hprod := mul_le_mul h1 h2
    (div_nonneg (gammaNorm_pos hx0 y).le (gammaNorm_pos h3 y).le)
    (div_nonneg (Real.Gamma_pos_of_pos hx0).le (Real.Gamma_pos_of_pos hp).le)
  have hreal : Real.Gamma x^2/(Real.Gamma (x-1/4)*Real.Gamma (x+1/4)) ≤ 1 :=
    (div_le_one (mul_pos (Real.Gamma_pos_of_pos hm) (Real.Gamma_pos_of_pos hp))).mpr
      (real_midpoint_bound hx)
  calc
    _ = ‖((x-1/4 : ℝ) : ℂ)+(y : ℂ)*I‖*
        ((gammaNorm x y/gammaNorm (x+1/4) y)*(gammaNorm x y/gammaNorm (x+3/4) y)) := by
      rw [hrec]
      have halg (A B C D : ℝ) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
          A^2/(C*B)=D*((A/B)*(A/(D*C))) := by field_simp
      exact halg _ _ _ _ (gammaNorm_pos hp y).ne' (gammaNorm_pos hm y).ne' hzm.ne'
    _ ≤ ‖((x-1/4 : ℝ) : ℂ)+(y : ℂ)*I‖*
        ((Real.Gamma x/Real.Gamma (x+1/4))*(Real.Gamma x/Real.Gamma (x+3/4))) :=
      mul_le_mul_of_nonneg_left hprod hzm.le
    _ = (‖((x-1/4 : ℝ) : ℂ)+(y : ℂ)*I‖/(x-1/4))*
        (Real.Gamma x^2/(Real.Gamma (x-1/4)*Real.Gamma (x+1/4))) := by
      rw [hrrec]
      field_simp
    _ ≤ _ := mul_le_of_le_one_right (div_nonneg hzm.le hm.le) hreal

/-- Two vertical Gamma-ratio comparisons and real log-convexity give a polynomial envelope. -/
theorem normalized_norm_le_linear_ratio {w : ℂ} (hw : 0 < w.re) :
    ‖normalizedSymbol w‖ ≤ ‖w+1‖/(w.re+1) := by
  have hx : (1/2 : ℝ) ≤ (w.re+2)/4 := by linarith only [hw]
  have h := gamma_midpoint_bound hx (w.im/4)
  have ha : (w+2)/4=(((w.re+2)/4 : ℝ) : ℂ)+((w.im/4 : ℝ) : ℂ)*I := by
    apply Complex.ext <;> simp
  have hm : (w+1)/4=((((w.re+2)/4-1/4 : ℝ)) : ℂ)+((w.im/4 : ℝ) : ℂ)*I := by
    apply Complex.ext <;> simp; ring
  have hp : (w+3)/4=((((w.re+2)/4+1/4 : ℝ)) : ℂ)+((w.im/4 : ℝ) : ℂ)*I := by
    apply Complex.ext <;> simp; ring
  have he : ‖normalizedSymbol w‖=
      gammaNorm ((w.re+2)/4) (w.im/4)^2/
        (gammaNorm ((w.re+2)/4-1/4) (w.im/4)*gammaNorm ((w.re+2)/4+1/4) (w.im/4)) := by
    rw [normalized_eq_gamma hw,norm_div,norm_pow,norm_mul,ha,hm,hp]
    rfl
  rw [he]
  refine h.trans_eq ?_
  rw [← hm,norm_div,show ‖(4 : ℂ)‖=(4 : ℝ) by norm_num,
    show (w.re+2)/4-1/4=(w.re+1)/4 by ring]
  field_simp

/-- The actual normalized multiplier grows at most linearly on the right half-plane. -/
theorem normalized_norm_le_linear {w : ℂ} (hw : 0 < w.re) :
    ‖normalizedSymbol w‖ ≤ ‖w‖+1 := by
  calc
    _ ≤ ‖w+1‖/(w.re+1) := normalized_norm_le_linear_ratio hw
    _ ≤ ‖w+1‖ := by
      apply (div_le_iff₀ (by linarith only [hw] : 0 < w.re+1)).mpr
      nlinarith only [mul_nonneg (norm_nonneg (w+1)) hw.le]
    _ ≤ _ := by simpa only [norm_one] using norm_add_le w (1 : ℂ)

/-- Real Gamma log-convexity bounds the normalization on the positive real axis. -/
theorem normalized_norm_real_le_one {r : ℝ} (hr : 0 < r) :
    ‖normalizedSymbol (r : ℂ)‖ ≤ 1 := by
  have h := normalized_norm_le_linear_ratio (w := (r : ℂ)) hr
  have hc : ‖(r : ℂ)+1‖=r+1 := by
    rw [← ofReal_one,← ofReal_add,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by linarith only [hr])]
  simpa only [hc,ofReal_re,div_self (by linarith only [hr] : r+1 ≠ 0)] using h

#print axioms normalized_norm_le_linear_ratio
#print axioms normalized_norm_le_linear
#print axioms normalized_norm_real_le_one

/-- The imaginary-axis estimate propagates through the closed half-plane using proved growth. -/
theorem normalized_norm_le_one {w : ℂ} (hw : 0 ≤ w.re) : ‖normalizedSymbol w‖ ≤ 1 := by
  have hd : DiffContOnCl ℂ normalizedSymbol {z : ℂ | 0 < z.re} := by
    constructor
    · intro z hz
      have hz0 : 0 < z.re := hz
      exact (differentiableAt_normalizedSymbol (by linarith only [hz0])).differentiableWithinAt
    · intro z hz
      have hcl : closure {v : ℂ | 0 < v.re} ⊆ {v : ℂ | 0 ≤ v.re} :=
        closure_minimal (fun v hv => show 0 ≤ v.re from le_of_lt hv) (isClosed_le continuous_const Complex.continuous_re)
      have hz0 : 0 ≤ z.re := hcl hz
      exact (differentiableAt_normalizedSymbol (by linarith only [hz0])).continuousAt.continuousWithinAt
  have hO : normalizedSymbol =O[Bornology.cobounded ℂ ⊓ principal {z : ℂ | 0 < z.re}]
      (fun z : ℂ => Real.exp ‖z‖) := by
    apply IsBigO.of_bound 1
    filter_upwards [mem_inf_of_right (mem_principal_self {z : ℂ | 0 < z.re})] with z hz
    rw [one_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (normalized_norm_le_linear hz).trans (Real.add_one_le_exp ‖z‖)
  have hexp : ∃ c < (2 : ℝ), ∃ B,
      normalizedSymbol =O[Bornology.cobounded ℂ ⊓ principal {z : ℂ | 0 < z.re}]
        (fun z : ℂ => Real.exp (B*‖z‖^c)) := by
    exact ⟨1,by norm_num,1,by simpa only [Real.rpow_one,one_mul] using hO⟩
  have hreal : IsBoundedUnder (· ≤ ·) atTop (fun r : ℝ => ‖normalizedSymbol (r : ℂ)‖) := by
    have hR : (fun r : ℝ => normalizedSymbol (r : ℂ)) =O[atTop] (fun _ : ℝ => (1 : ℂ)) := by
      apply IsBigO.of_bound 1
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      simpa only [norm_one,mul_one] using normalized_norm_real_le_one hr
    exact hR.isBoundedUnder_le
  exact PhragmenLindelof.right_half_plane_of_bounded_on_real hd hexp hreal
    (fun τ => (normalized_boundary_norm_lt_one τ).le) hw

/-- The exponential spectral factor has a completely explicit modulus. -/
theorem norm_symbol_half (w : ℂ) :
    ‖symbol w (w/2)‖=(2 : ℝ)^((1-w.re)/2)*‖normalizedSymbol w‖ := by
  have hr : ((1-w)/2).re=(1-w.re)/2 := by simp
  have hn : ‖(2 : ℂ)^((1-w)/2)‖=(2 : ℝ)^((1-w.re)/2) := by
    simpa only [ofReal_ofNat,hr] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ)<2) ((1-w)/2)
  rw [symbol_half_eq_normalized,norm_mul,hn]

private theorem central_hasMellin {w : ℂ} (hw : 0 < w.re) :
    HasMellin (cauchyKernel w) (w/2) (symbol w (w/2)) := by
  have hu : (w/2).re=w.re/2 := by simp
  exact cauchyKernel_hasMellin hw (by rw [hu]; linarith only [hw])
    (by rw [hu]; linarith only [hw])

#print axioms normalized_norm_le_one
#print axioms norm_symbol_half

/-- No interior point attains unit modulus: the strong maximum principle would contradict
continuity at the strict imaginary-axis boundary value. -/
theorem normalized_norm_lt_one {w : ℂ} (hw : 0 < w.re) : ‖normalizedSymbol w‖ < 1 := by
  by_contra hnot
  have heq : ‖normalizedSymbol w‖=1 :=
    le_antisymm (normalized_norm_le_one hw.le) (not_lt.mp hnot)
  have hc : Convex ℝ {z : ℂ | 0 < z.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq,Complex.add_re,Complex.smul_re,smul_eq_mul]
    by_cases ha0 : a=0
    · subst a
      have hb1 : b=1 := by simpa only [zero_add] using hab
      rw [hb1,zero_mul,zero_add,one_mul]
      exact hy
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hap hx) (mul_nonneg hb hy.le)
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ normalizedSymbol {z : ℂ | 0 < z.re} := by
    intro z hz
    have hz0 : 0 < z.re := hz
    exact (differentiableAt_normalizedSymbol (by linarith only [hz0])).differentiableWithinAt
  have hm : IsMaxOn (norm ∘ normalizedSymbol) {z : ℂ | 0 < z.re} w := by
    intro z hz
    change ‖normalizedSymbol z‖ ≤ ‖normalizedSymbol w‖
    rw [heq]
    exact normalized_norm_le_one (le_of_lt hz)
  have hconst := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hc.isPreconnected ho hd
    (show w ∈ {z : ℂ | 0 < z.re} from hw) hm
  have hf := (differentiableAt_normalizedSymbol (w := (0 : ℂ)) (by norm_num)).continuousAt
  have hg : ContinuousAt (fun r : ℝ => (r : ℂ)) 0 := Complex.continuous_ofReal.continuousAt
  have hcont : ContinuousAt (fun r : ℝ => ‖normalizedSymbol (r : ℂ)‖) 0 :=
    (hf.comp (f := fun r : ℝ => (r : ℂ)) hg).norm
  have h0 : ‖normalizedSymbol (0 : ℂ)‖ ∈ Iio (1 : ℝ) := by
    simpa only [ofReal_zero,zero_mul,mem_Iio] using normalized_boundary_norm_lt_one 0
  have hev : ∀ᶠ r : ℝ in 𝓝 0, ‖normalizedSymbol (r : ℂ)‖ < 1 :=
    hcont.eventually (isOpen_Iio.mem_nhds h0)
  obtain ⟨δ,hδ,hδf⟩ := Metric.eventually_nhds_iff.mp hev
  have hr : 0 < δ/2 := by linarith only [hδ]
  have hsmall := hδf (y := δ/2) (by
    rw [Real.dist_eq,sub_zero,abs_of_pos hr]
    linarith only [hδ])
  have hz : ((δ/2 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    simpa only [Set.mem_setOf_eq,ofReal_re] using hr
  have hval := hconst hz
  simp only [Function.comp_apply,Function.const_apply,heq] at hval
  exact (ne_of_lt hsmall) hval

/-- Sharp strict global envelope for the actual, absolutely convergent central Mellin integral. -/
theorem norm_mellin_half_lt {w : ℂ} (hw : 0 < w.re) :
    ‖mellin (cauchyKernel w) (w/2)‖ < (2 : ℝ)^((1-w.re)/2) := by
  rw [(central_hasMellin hw).2,norm_symbol_half]
  have hp : 0 < (2 : ℝ)^((1-w.re)/2) := Real.rpow_pos_of_pos (by norm_num) _
  simpa only [mul_one] using mul_lt_mul_of_pos_left (normalized_norm_lt_one hw) hp

/-- At and above abscissa one, every finite spectral height is strictly contractive. -/
theorem central_contractive {w : ℂ} (hw : 1 ≤ w.re) :
    ‖mellin (cauchyKernel w) (w/2)‖ < 1 := by
  have hw0 : 0 < w.re := lt_of_lt_of_le zero_lt_one hw
  have hp : (2 : ℝ)^((1-w.re)/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hw])
  exact lt_of_lt_of_le (norm_mellin_half_lt hw0) hp

/-- The global envelope is the exact supremum over heights on every positive abscissa. -/
theorem central_norm_isLUB {σ : ℝ} (hσ : 0 < σ) :
    IsLUB (Set.range (fun τ : ℝ => ‖mellin (cauchyKernel ((σ : ℂ)+(τ : ℂ)*I))
      (((σ : ℂ)+(τ : ℂ)*I)/2)‖)) ((2 : ℝ)^((1-σ)/2)) := by
  have hl : Tendsto (fun τ : ℝ => ‖mellin (cauchyKernel ((σ : ℂ)+(τ : ℂ)*I))
      (((σ : ℂ)+(τ : ℂ)*I)/2)‖) atTop (𝓝 ((2 : ℝ)^((1-σ)/2))) := by
    have h := tendsto_norm_mellin (σ := σ) (α := σ/2) hσ
      (by linarith only [hσ]) (by linarith only [hσ])
    refine h.congr (fun τ => ?_)
    rw [show ((σ/2 : ℝ) : ℂ)+(τ : ℂ)/2*I=((σ : ℂ)+(τ : ℂ)*I)/2 by push_cast; ring]
  constructor
  · rintro y ⟨τ,rfl⟩
    have h := norm_mellin_half_lt (w := (σ : ℂ)+(τ : ℂ)*I) (by simpa using hσ)
    simpa using h.le
  · intro b hb
    exact le_of_tendsto hl (Eventually.of_forall (fun τ => hb (Set.mem_range_self τ)))

#print axioms normalized_norm_lt_one
#print axioms norm_mellin_half_lt
#print axioms central_contractive
#print axioms central_norm_isLUB

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchySchur
