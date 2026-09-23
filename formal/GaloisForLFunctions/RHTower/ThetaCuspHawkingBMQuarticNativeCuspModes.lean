import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspNativeMeanSquare
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMWeightedSquareCuspBound
import GaloisForLFunctions.RHTower.SelbergMaassParseval
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Forced coercivity of the original native cusp modes

The two constructed angular responses retain their exact full forcing in every
literal period-one Fourier mode. Their mass second derivative is the sum of
vertical energy, the original spectral/metric potential and signed source work.
Completing one square gives a forced lower bound. The nonzero integer frequency
gap makes it coercive above an explicit cusp height, with no change of physical
clock. The forcing has arbitrary weighted bounds uniformly in the Fourier index.
Parseval and the original modular energy give each mode's weighted integrability.

These are source-derived inputs for an infinite-cusp comparison argument.
Decay of complete response products, their actual tested boundary finite part,
physical left-QNM action identification and fixed-clock extinction are not
asserted here. No boundary value, radiation condition or covariance premise is added.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.SelbergMaassMean
open GaloisForLFunctions.RHTower.SelbergMaassFourier
open scoped ContDiff
namespace RHTower.D4BMQuarticNativeCuspModes
open D4BMModularCore D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- The literal period-one coefficient of the constructed native angular response. -/
def responseMode (q : XiZeroCopy) (b : Bool) (n : ℤ) : ℝ → ℂ :=
  coefficient 1 n (D4BMCuspResponse.responsePlanar q b)

/-- The same coefficient of the complete original cusp-subtracted forcing. -/
def forcingMode (q : XiZeroCopy) (b : Bool) (n : ℤ) : ℝ → ℂ :=
  coefficient 1 n (globalForcing q b ∘ ofComplex)

private theorem mode_hasDerivAt (q : XiZeroCopy) (b : Bool) (n : ℤ)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (responseMode q b n) (deriv (responseMode q b n) y) y :=
  (coefficient_hasDerivAt 1 (by norm_num) n
    ((D4BMCuspResponse.responsePlanar_smooth q b).of_le (WithTop.coe_le_coe.mpr le_top)) hy).differentiableAt.hasDerivAt

private theorem mode_second_hasDerivAt (q : XiZeroCopy) (b : Bool) (n : ℤ)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (responseMode q b n)) (deriv (deriv (responseMode q b n)) y) y :=
  (coefficient_second_hasDerivAt 1 (by norm_num) n
    ((D4BMCuspResponse.responsePlanar_smooth q b).of_le (WithTop.coe_le_coe.mpr le_top)) hy).differentiableAt.hasDerivAt

private theorem weighted_integrable (n : ℤ) {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun x => deningerFourierKernel 1 n x*F (point x y)) (Ioc (0:ℝ) 1) := by
  have hk : Continuous (deningerFourierKernel 1 n) :=
    continuous_iff_continuousAt.mpr (fun x => (deningerFourierKernel_hasDerivAt 1 n x).continuousAt)
  exact (hk.mul (slice_continuous hf.continuousOn hy)).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- Both real height derivatives of every original response mode retain its complete forcing. -/
theorem responseMode_equation (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : Ioi (0:ℝ)) :
    deriv (deriv (responseMode q b n)) y =
      (((signedFrequency 1 n)^(2 : ℕ):ℝ):ℂ)*responseMode q b n y +
        (parameter q b*responseMode q b n y+forcingMode q b n y)/(y.val:ℂ)^(2 : ℕ) := by
  let F := D4BMCuspResponse.responsePlanar q b
  let G := globalForcing q b ∘ ofComplex
  have hf := D4BMCuspResponse.responsePlanar_smooth q b
  have hg := (globalForcing_smooth q b).planar_contDiffOn
  have hd1 := planar_derivative_contDiffOn hf (1:ℂ)
  have hdI := planar_derivative_contDiffOn hf Complex.I
  have hxx := weighted_integrable n (planar_derivative_contDiffOn hd1 (1:ℂ)) y.2
  have hyy := weighted_integrable n (planar_derivative_contDiffOn hdI Complex.I) y.2
  have hF := weighted_integrable n hf y.2
  have hG := weighted_integrable n hg y.2
  have he (x : ℝ) :
      directional 1 (directional 1 F) (point x y)+
        directional Complex.I (directional Complex.I F) (point x y) =
      (parameter q b*F (point x y)+G (point x y))/(y.val:ℂ)^(2 : ℕ) := by
    have hp : 0 < (point x y).im := by simpa only [point,Complex.add_im,
      Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using (show 0 < y.val from y.2)
    have h := globalResponse_classical_planar q b (point x y) hp
    change (fderiv ℝ (fun w => fderiv ℝ (globalResponse q b ∘ ofComplex) w 1) (point x y) 1+
      fderiv ℝ (fun w => fderiv ℝ (globalResponse q b ∘ ofComplex) w Complex.I)
        (point x y) Complex.I) = _
    simpa only [F,G,D4BMCuspResponse.responsePlanar,directional,Function.comp_apply,
      planarLaplacian,Fin.sum_univ_two,direction,Matrix.cons_val_zero,
      Matrix.cons_val_one,point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,
      Complex.ofReal_re,zero_add] using h
  have hew (x : ℝ) :
      deningerFourierKernel 1 n x*directional 1 (directional 1 F) (point x y)+
        deningerFourierKernel 1 n x*directional Complex.I (directional Complex.I F) (point x y) =
      (parameter q b*(deningerFourierKernel 1 n x*F (point x y))+
        deningerFourierKernel 1 n x*G (point x y))/(y.val:ℂ)^(2 : ℕ) := by
    linear_combination deningerFourierKernel 1 n x*he x
  have hi := integral_congr_ae (μ := volume.restrict (Ioc (0:ℝ) 1))
    (Filter.Eventually.of_forall hew)
  change IntegrableOn (fun x => deningerFourierKernel 1 n x*
    directional 1 (directional 1 F) (point x y)) (Ioc (0:ℝ) 1) at hxx
  change IntegrableOn (fun x => deningerFourierKernel 1 n x*
    directional Complex.I (directional Complex.I F) (point x y)) (Ioc (0:ℝ) 1) at hyy
  change IntegrableOn (fun x => deningerFourierKernel 1 n x*F (point x y)) (Ioc (0:ℝ) 1) at hF
  change IntegrableOn (fun x => deningerFourierKernel 1 n x*G (point x y)) (Ioc (0:ℝ) 1) at hG
  rw [integral_add hxx hyy,integral_div,integral_add (hF.const_mul _) hG,
    integral_const_mul] at hi
  have hc : coefficient 1 n (directional 1 (directional 1 F)) y+
      coefficient 1 n (directional Complex.I (directional Complex.I F)) y =
      (parameter q b*coefficient 1 n F y+coefficient 1 n G y)/(y.val:ℂ)^(2 : ℕ) := by
    simpa only [coefficient,deningerFourierCoeff,Complex.ofReal_one,div_one,one_mul,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using hi
  rw [coefficient_horizontal_second 1 (by norm_num) n (hf.of_le (WithTop.coe_le_coe.mpr le_top)) y.2
    (D4BMCuspResponse.responsePlanar_periodic q b y.2),
    ← (coefficient_second_hasDerivAt 1 (by norm_num) n (hf.of_le (WithTop.coe_le_coe.mpr le_top)) y.2).deriv] at hc
  change -(signedFrequency 1 n:ℂ)^(2 : ℕ)*responseMode q b n y+
      deriv (deriv (responseMode q b n)) y =
      (parameter q b*responseMode q b n y+forcingMode q b n y)/(y.val:ℂ)^(2 : ℕ) at hc
  push_cast
  linear_combination hc

/-- Squared mass of an actual native mode. -/
def modeMass (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : ℝ) : ℝ :=
  Complex.normSq (responseMode q b n y)

/-- The original modal source work, with the changing hyperbolic metric weight. -/
def modeWork (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : ℝ) : ℝ :=
  (forcingMode q b n y*(starRingEnd ℂ) (responseMode q b n y)).re/y^(2 : ℕ)

private theorem normSq_hasDerivAt {a : ℝ → ℂ} {v : ℂ} {y : ℝ} (ha : HasDerivAt a v y) :
    HasDerivAt (fun t => Complex.normSq (a t))
      (2*(v*(starRingEnd ℂ) (a y)).re) y := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y ha
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y ha
  convert (hr.mul hr).add (hi.mul hi) using 1 <;> try rfl
  simp only [Function.comp_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

/-- Native modal mass differentiates to its actual vertical current. -/
theorem modeMass_hasDerivAt (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : Ioi (0:ℝ)) :
    HasDerivAt (modeMass q b n)
      (2*(deriv (responseMode q b n) y*(starRingEnd ℂ) (responseMode q b n y)).re) y :=
  normSq_hasDerivAt (mode_hasDerivAt q b n y.2)

/-- The exact forced mass identity; the signed source work is not discarded. -/
theorem modeMass_second_hasDerivAt (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : Ioi (0:ℝ)) :
    HasDerivAt (deriv (modeMass q b n))
      (2*Complex.normSq (deriv (responseMode q b n) y)+
        2*((signedFrequency 1 n)^(2 : ℕ)+(parameter q b).re/y.val^(2 : ℕ))*modeMass q b n y+
        2*modeWork q b n y) y := by
  let c := responseMode q b n
  have hc := mode_hasDerivAt q b n y.2
  have hdc := mode_second_hasDerivAt q b n y.2
  have hconj := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt y.val hc
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt y.val (hdc.mul hconj)).const_mul 2
  have hd : deriv (modeMass q b n) =ᶠ[𝓝 y.val]
      (fun t => 2*(deriv c t*(starRingEnd ℂ) (c t)).re) := by
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    exact (modeMass_hasDerivAt q b n ⟨t,ht⟩).deriv
  apply (h.congr_of_eventuallyEq hd).congr_deriv
  change 2*((deriv (deriv (responseMode q b n)) y)*
      (starRingEnd ℂ) (responseMode q b n y)+
      deriv (responseMode q b n) y*(starRingEnd ℂ) (deriv (responseMode q b n) y)).re = _
  rw [responseMode_equation q b n y]
  simp only [modeMass,modeWork,← Complex.ofReal_pow,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.normSq_apply]
  ring

/-- A pointwise forced coercivity estimate for every actual mode, before taking a cusp limit. -/
theorem modeMass_forced_lower (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : Ioi (0:ℝ)) :
    2*Complex.normSq (deriv (responseMode q b n) y)+
      (2*(signedFrequency 1 n)^(2 : ℕ)+2*(parameter q b).re/y.val^(2 : ℕ)-1)*modeMass q b n y-
      Complex.normSq (forcingMode q b n y)/y.val^(4 : ℕ) ≤ deriv (deriv (modeMass q b n)) y := by
  rw [(modeMass_second_hasDerivAt q b n y).deriv]
  have h := Complex.normSq_nonneg (responseMode q b n y+forcingMode q b n y/(y.val:ℂ)^(2 : ℕ))
  have hs : 0 ≤ modeMass q b n y+2*modeWork q b n y+
      Complex.normSq (forcingMode q b n y)/y.val^(4 : ℕ) := by
    convert h using 1
    rw [Complex.normSq_add,Complex.normSq_div,map_pow,Complex.normSq_ofReal]
    simp only [modeMass,modeWork,Complex.mul_re,Complex.conj_re,Complex.conj_im,
      ← Complex.ofReal_pow,Complex.div_ofReal_re,Complex.div_ofReal_im]
    ring
  ring_nf at hs ⊢
  linarith

/-- A cusp-height cutoff only; the common physical Hawking clock is unchanged. -/
def coercivityHeight (q : XiZeroCopy) (b : Bool) : ℝ := 1+2*|(parameter q b).re|

/-- Nonzero native modes have uniform forced coercivity above the explicit cusp cutoff. -/
theorem modeMass_cusp_coercivity (q : XiZeroCopy) (b : Bool) (n : {n : ℤ // n ≠ 0})
    (y : Ici (coercivityHeight q b)) :
    2*Complex.normSq (deriv (responseMode q b n.val) y)+
      (signedFrequency 1 n.val)^(2 : ℕ)*modeMass q b n.val y-
      Complex.normSq (forcingMode q b n.val y)/y.val^(4 : ℕ) ≤
        deriv (deriv (modeMass q b n.val)) y := by
  have hy1 : 1 ≤ y.val := by
    have hh : 1+2*|(parameter q b).re| ≤ y.val := y.2
    linarith [abs_nonneg (parameter q b).re]
  have hy : 0 < y.val := lt_of_lt_of_le (by norm_num) hy1
  have hy2 : 2*|(parameter q b).re| ≤ y.val^(2 : ℕ) := by
    have hh : 1+2*|(parameter q b).re| ≤ y.val := y.2
    nlinarith [sq_nonneg (y.val-1)]
  have ha : -(1/2:ℝ) ≤ (parameter q b).re/y.val^(2 : ℕ) := by
    rw [le_div_iff₀ (sq_pos_of_pos hy)]
    linarith [neg_abs_le (parameter q b).re]
  have hnZ : (1:ℤ) ≤ n.val^(2 : ℕ) := Int.add_one_le_iff.mpr (sq_pos_of_ne_zero n.2)
  have hnR : (1:ℝ) ≤ (n.val:ℝ)^(2 : ℕ) := by exact_mod_cast hnZ
  have hk : 2 ≤ (signedFrequency 1 n.val)^(2 : ℕ) := by
    have hm := mul_le_mul_of_nonneg_left hnR (sq_nonneg (2*Real.pi))
    have hp := Real.pi_gt_three
    dsimp only [signedFrequency]
    rw [div_one,mul_pow]
    nlinarith [sq_nonneg (Real.pi-3)]
  have hcoeff : (signedFrequency 1 n.val)^(2 : ℕ) ≤
      2*(signedFrequency 1 n.val)^(2 : ℕ)+2*(parameter q b).re/y.val^(2 : ℕ)-1 := by
    rw [mul_div_assoc]
    linarith
  have hm := mul_le_mul_of_nonneg_right hcoeff (Complex.normSq_nonneg (responseMode q b n.val y))
  have h := modeMass_forced_lower q b n.val ⟨y.val,hy⟩
  change (signedFrequency 1 n.val)^(2 : ℕ)*modeMass q b n.val y ≤
      (2*(signedFrequency 1 n.val)^(2 : ℕ)+2*(parameter q b).re/y.val^(2 : ℕ)-1)*modeMass q b n.val y at hm
  dsimp only [Subtype.coe_mk] at h
  linarith

private theorem forcing_strip_weighted (q : XiZeroCopy) (b : Bool) (w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, 0 ≤ z.re → z.re ≤ 1 → 3 < z.im →
      ‖(z.im:ℂ)^w*globalForcing q b z‖ ≤ C := by
  obtain ⟨A,hA,hbound⟩ := weighted_squareRemainder_bounded (center q) w 3 (by norm_num)
  let C := ‖parameter q b/2‖*A
  have hfd (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) (hy : 3 < z.im) :
      ‖(z.im:ℂ)^w*globalForcing q b z‖ ≤ C := by
    rw [globalForcing_eq_on_fd q b z hz,forcing_high q b _ hy]
    have he : (z.im:ℂ)^w*((parameter q b/2)*squareRemainder (center q) (coordinates z)) =
        (parameter q b/2)*((z.im:ℂ)^w*squareRemainder (center q) (coordinates z)) := by ring
    rw [he,norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound (coordinates z) hy.le) (norm_nonneg _)
  refine ⟨C,mul_nonneg (norm_nonneg _) hA,?_⟩
  intro z hx0 hx1 hy
  by_cases hx : z.re ≤ 1/2
  · apply hfd z _ hy
    constructor
    · change 1 ≤ z.re*z.re+z.im*z.im
      nlinarith [sq_nonneg z.re]
    · exact abs_le.mpr ⟨by linarith,hx⟩
  · let z' := ModularGroup.T^(-1:ℤ) • z
    have hi : z'.im = z.im := by
      change (ModularGroup.T^(-1:ℤ) • z).im = z.im
      rw [ModularGroup.im_T_zpow_smul]
    have hr : z'.re = z.re-1 := by
      change (ModularGroup.T^(-1:ℤ) • z).re = z.re-1
      rw [ModularGroup.re_T_zpow_smul]
      norm_num
      ring
    have hz' : z' ∈ ModularGroup.fd := by
      constructor
      · change 1 ≤ z'.re*z'.re+z'.im*z'.im
        rw [hi]
        nlinarith [sq_nonneg z'.re]
      · rw [hr]
        exact abs_le.mpr ⟨by linarith,by linarith⟩
    have he := globalForcing_invariant q b (QuotientGroup.mk (ModularGroup.T^(-1:ℤ))) z
    change globalForcing q b z' = globalForcing q b z at he
    rw [← he,← hi]
    exact hfd z' hz' (by rw [hi]; exact hy)

/-- Every complex height weight of the complete modal forcing is bounded uniformly in n. -/
theorem forcingMode_weighted_bound (q : XiZeroCopy) (b : Bool) (w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, ∀ y : Ioi (3:ℝ),
      ‖(y.val:ℂ)^w*forcingMode q b n y‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := forcing_strip_weighted q b w
  refine ⟨C,hC,?_⟩
  intro n y
  have he : (y.val:ℂ)^w*forcingMode q b n y =
      deningerFourierCoeff 1 (fun x => (y.val:ℂ)^w*globalForcing q b (ofComplex (point x y))) n := by
    simp only [forcingMode,coefficient,deningerFourierCoeff,Complex.ofReal_one,
      div_one,one_mul,Function.comp_apply,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [he]
  apply deningerFourierCoeff_norm_le (by norm_num : (0:ℝ) < 1)
  intro x hx
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
  have hp : 0 < (point x y).im := by
    simp only [point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]
    exact lt_trans (by norm_num : (0:ℝ)<3) y.2
  rw [ofComplex_apply_of_im_pos hp]
  have hr : (⟨point x y,hp⟩:UpperHalfPlane).re = x := by simp [UpperHalfPlane.re,point]
  have hi : (⟨point x y,hp⟩:UpperHalfPlane).im = y.val := by simp [UpperHalfPlane.im,point]
  have h := hb ⟨point x y,hp⟩ (by rw [hr]; exact hx.1.le)
    (by rw [hr]; exact hx.2) (by rw [hi]; exact y.2)
  rwa [hi] at h

/-- Parseval recovers the complete native cusp mass from all original modes. -/
theorem modeMass_hasSum (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    HasSum (fun n : ℤ => modeMass q b n y) (D4BMCuspResponse.responseMeanSquare q b y) := by
  have hs := GaloisForLFunctions.RHTower.SelbergMaassParseval.coefficient_mass_hasSum 1
    (by norm_num) (D4BMCuspResponse.responsePlanar_smooth q b).continuousOn y.2
  have hp : Function.Periodic
      (fun x => ‖D4BMCuspResponse.responsePlanar q b (point x y)‖^(2 : ℕ)) 1 := by
    intro x
    change ‖D4BMCuspResponse.responsePlanar q b (D4BMCuspResponse.point (x+1) y)‖^(2 : ℕ) =
      ‖D4BMCuspResponse.responsePlanar q b (D4BMCuspResponse.point x y)‖^(2 : ℕ)
    rw [D4BMCuspResponse.responsePlanar_periodic q b y.2 x]
  have hi := hp.intervalIntegral_add_eq 0 (-1/2)
  norm_num only [zero_add,show (-1/2:ℝ)+1=1/2 by ring] at hi
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)] at hi
  simp only [inv_one,one_mul,Complex.normSq_eq_norm_sq] at hs
  rw [hi] at hs
  simpa only [modeMass,responseMode,Complex.normSq_eq_norm_sq,
    D4BMCuspResponse.responseMeanSquare,D4BMCuspResponse.point,point,neg_div] using hs

/-- Native L2 admission bounds each original coefficient by the actual full slice mass. -/
theorem modeMass_le_native_square (q : XiZeroCopy) (b : Bool) (n : ℤ) (y : Ioi (0:ℝ)) :
    modeMass q b n y ≤ D4BMCuspResponse.responseMeanSquare q b y := by
  have hs := modeMass_hasSum q b y
  rw [← hs.tsum_eq]
  exact hs.summable.le_tsum n (fun _ _ => Complex.normSq_nonneg _)

/-- The full original modular energy gives integrability of every modal cusp mass.
No modal decay, radiation condition, or zero boundary value is supplied. -/
theorem modeMass_density_integrable (q : XiZeroCopy) (b : Bool) (n : ℤ) :
    IntegrableOn (fun y : ℝ => modeMass q b n y/y^(2 : ℕ)) (Ioi (2:ℝ)) := by
  have hc : ContinuousOn (fun y : ℝ => modeMass q b n y/y^(2 : ℕ)) (Ioi (2:ℝ)) := by
    intro y hy
    have hp : 0 < y := lt_trans (by norm_num : (0:ℝ)<2) hy
    exact ((modeMass_hasDerivAt q b n ⟨y,hp⟩).continuousAt.div
      (continuousAt_id.pow 2) (pow_ne_zero 2 hp.ne')).continuousWithinAt
  apply (D4BMCuspResponse.responseMeanSquare_density_integrable q b).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hp : 0 < y := lt_trans (by norm_num : (0:ℝ)<2) hy
  have hm : 0 ≤ modeMass q b n y := Complex.normSq_nonneg _
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hm (sq_nonneg y))]
  exact div_le_div_of_nonneg_right (modeMass_le_native_square q b n ⟨y,hp⟩) (sq_nonneg y)

end
end RHTower.D4BMQuarticNativeCuspModes
