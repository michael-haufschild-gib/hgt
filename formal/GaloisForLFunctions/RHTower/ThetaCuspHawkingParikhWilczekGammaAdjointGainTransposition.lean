import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaAdjointPairedResponse
import Mathlib.MeasureTheory.Group.Prod

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

theorem pwGammaRaySource_coordinate_hasDerivAt {x : ℝ} (hx : 0<x) :
    HasDerivAt pwGammaRaySource (((1/(2*x):ℝ):ℂ)*pwGammaRaySource x-pwGammaRaySource x) x := by
  have he : pwGammaMobiusGlobalAtom (0:ℂ) 1 = pwGammaRaySource := by
    funext y
    simp [pwGammaMobiusGlobalAtom]
  have ht := pwGammaMobiusGlobalAtom_coordinate_hasDerivAt 0 1 hx
  rw [he] at ht
  simpa [pwGammaMobiusGlobalAtom] using ht

theorem pwGammaMobiusGroundQuotient_hasDerivAt (z : ℂ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y => pwGammaMobiusTilt z y/pwGammaRaySource y)
      (pwGammaMobiusTilt z x/pwGammaRaySource x-pwGammaMobiusTilt (z-1) x/pwGammaRaySource x) x := by
  have hh := (pwGammaMobiusTilt_coordinate_hasDerivAt z hx).div
    (pwGammaRaySource_coordinate_hasDerivAt hx) (pwGammaRaySource_ne_zero x)
  apply hh.congr_deriv
  field_simp [pwGammaRaySource_ne_zero]
  ring

theorem pwGammaMobiusGroundQuotient_measurable (z : ℂ) :
    Measurable (fun x => pwGammaMobiusTilt z x/pwGammaRaySource x) := by
  apply (pwGammaMobiusTilt_measurable z).div
  unfold pwGammaRaySource GaloisForLFunctions.expShift
  fun_prop

theorem pwGammaMobiusGroundQuotient_polynomial_bound (z : ℂ) :
    ∃p:ℕ, ∃C:ℝ, 0≤C ∧ ∀x:ℝ, 0<x →
      ‖pwGammaMobiusTilt z x/pwGammaRaySource x‖≤C*(1+1/x)^p := by
  obtain ⟨p,C,hC,hb⟩ := pwGammaMobiusReciprocalTail_polynomial_bound z
  refine ⟨p,1+C,by positivity,fun x hx => ?_⟩
  have ht := hb (1/x) (by positivity)
  have he : pwGammaMobiusTilt z x/pwGammaRaySource x = pwGammaMobiusReciprocalTail z (1/x)+1 := by
    simp only [pwGammaMobiusReciprocalTail, one_div, inv_inv, sub_add_cancel]
  have h1 : (1:ℝ)≤(1+1/x)^p := one_le_pow₀ (by linarith [show (0:ℝ)≤1/x by positivity])
  have hp : (1/x)^p≤(1+1/x)^p := pow_le_pow_left₀ (by positivity) (by linarith) p
  rw [he]
  calc
    _ ≤ ‖pwGammaMobiusReciprocalTail z (1/x)‖+‖(1:ℂ)‖ := norm_add_le _ _
    _ ≤ C*(1/x)^p+1 := add_le_add ht (by simp)
    _ ≤ C*(1+1/x)^p+(1+1/x)^p := add_le_add (mul_le_mul_of_nonneg_left hp hC) h1
    _ = _ := by ring

theorem pwGammaMobiusGroundQuotient_derivative_bound (z : ℂ) :
    ∃r:ℕ, ∃C:ℝ, 0≤C ∧ ∀x y:ℝ, 0<x → x≤y →
      ‖pwGammaMobiusTilt z y/pwGammaRaySource y-pwGammaMobiusTilt (z-1) y/pwGammaRaySource y‖ ≤
        C*(1+1/x)^r := by
  obtain ⟨p,A,hA,ha⟩ := pwGammaMobiusGroundQuotient_polynomial_bound z
  obtain ⟨q,B,hB,hb⟩ := pwGammaMobiusGroundQuotient_polynomial_bound (z-1)
  refine ⟨p+q,A+B,by positivity,fun x y hx hxy => ?_⟩
  have hy := hx.trans_le hxy
  have hxy' : 1+1/y≤1+1/x := by
    linarith [one_div_le_one_div_of_le hx hxy]
  have h1 : (1:ℝ)≤1+1/x := by linarith [show (0:ℝ)≤1/x by positivity]
  have hp : (1+1/y)^p≤(1+1/x)^(p+q) :=
    (pow_le_pow_left₀ (by positivity) hxy' p).trans (pow_le_pow_right₀ h1 (by omega))
  have hq : (1+1/y)^q≤(1+1/x)^(p+q) :=
    (pow_le_pow_left₀ (by positivity) hxy' q).trans (pow_le_pow_right₀ h1 (by omega))
  calc
    _ ≤ ‖pwGammaMobiusTilt z y/pwGammaRaySource y‖+‖pwGammaMobiusTilt (z-1) y/pwGammaRaySource y‖ := norm_sub_le _ _
    _ ≤ A*(1+1/y)^p+B*(1+1/y)^q := add_le_add (ha y hy) (hb y hy)
    _ ≤ A*(1+1/x)^(p+q)+B*(1+1/x)^(p+q) :=
      add_le_add (mul_le_mul_of_nonneg_left hp hA) (mul_le_mul_of_nonneg_left hq hB)
    _ = _ := by ring

theorem pwGammaMobiusGroundQuotient_increment_bound (z : ℂ) :
    ∃r:ℕ, ∃C:ℝ, 0≤C ∧ ∀x h:ℝ, 0<x → 0≤h →
      ‖pwGammaMobiusTilt z (x+h)/pwGammaRaySource (x+h)-pwGammaMobiusTilt z x/pwGammaRaySource x‖ ≤
        C*(1+1/x)^r*h := by
  obtain ⟨r,C,hC,hb⟩ := pwGammaMobiusGroundQuotient_derivative_bound z
  refine ⟨r,C,hC,fun x h hx hh => ?_⟩
  have ht := norm_image_sub_le_of_norm_deriv_le_segment'
    (a:=x) (b:=x+h)
    (f:=fun y => pwGammaMobiusTilt z y/pwGammaRaySource y)
    (f':=fun y => pwGammaMobiusTilt z y/pwGammaRaySource y-pwGammaMobiusTilt (z-1) y/pwGammaRaySource y)
    (C:=C*(1+1/x)^r)
    (fun y hy => (pwGammaMobiusGroundQuotient_hasDerivAt z (hx.trans_le hy.1)).hasDerivWithinAt)
    (fun y hy => hb x y hx hy.1) (x+h) ⟨by linarith,le_refl _⟩
  simpa only [add_sub_cancel_left] using ht

/-- Original normalized forward jump difference, with the complete arithmetic source. -/
def pwGammaMobiusForwardResponse (z : ℂ) (x h : ℝ) : ℂ :=
  (Real.exp (-h):ℂ)*(pwGammaMobiusTilt z (x+h)/pwGammaRaySource (x+h)-
    pwGammaMobiusTilt z x/pwGammaRaySource x)/(h:ℂ)

theorem pwGammaMobiusForwardResponse_measurable (z : ℂ) :
    Measurable (fun p : ℝ×ℝ => pwGammaMobiusForwardResponse z p.1 p.2) := by
  have hg := pwGammaMobiusGroundQuotient_measurable z
  unfold pwGammaMobiusForwardResponse
  exact ((by fun_prop : Measurable (fun p : ℝ×ℝ => (Real.exp (-p.2):ℂ))).mul
    ((hg.comp (by fun_prop : Measurable (fun p : ℝ×ℝ => p.1+p.2))).sub
      (hg.comp measurable_fst))).div (by fun_prop)

theorem pwGammaMobiusForwardResponse_bound (z : ℂ) :
    ∃r:ℕ, ∃C:ℝ, 0≤C ∧ ∀x h:ℝ, 0<x → 0<h →
      ‖pwGammaMobiusForwardResponse z x h‖≤C*(1+1/x)^r*Real.exp (-h) := by
  obtain ⟨r,C,hC,hb⟩ := pwGammaMobiusGroundQuotient_increment_bound z
  refine ⟨r,C,hC,fun x h hx hh => ?_⟩
  unfold pwGammaMobiusForwardResponse
  rw [norm_div,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg hh.le]
  calc
    _ ≤ Real.exp (-h)*(C*(1+1/x)^r*h)/h :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hb x h hx hh.le) (Real.exp_pos _).le) hh.le
    _ = _ := by field_simp


theorem pwGammaMobiusForwardResponse_source_eq (z : ℂ) {x h : ℝ} (hx : 0<x) (hh : 0≤h) :
    pwGammaMobiusForwardResponse z x h = pwGammaMobiusFrullaniResponse z x h/pwGammaRaySource x := by
  have hq := pwGammaWeightedTranslation_ray_atom (n:=1) (by positivity) hh hx
  simp only [Nat.cast_one,one_mul] at hq
  have ht : pwGammaWeightedTranslation h (pwGammaMobiusTilt z) x =
      (Real.exp (-h):ℂ)*pwGammaRaySource x*
        (pwGammaMobiusTilt z (x+h)/pwGammaRaySource (x+h)) := by
    rw [← hq]
    unfold pwGammaWeightedTranslation
    field_simp [pwGammaRaySource_ne_zero]
  unfold pwGammaMobiusForwardResponse pwGammaMobiusFrullaniResponse
  rw [ht]
  field_simp [pwGammaRaySource_ne_zero]

theorem pwGammaMobiusForwardResponse_integrable (z : ℂ) {x : ℝ} (hx : 0<x) :
    IntegrableOn (pwGammaMobiusForwardResponse z x) (Ioi 0) := by
  have hi : IntegrableOn (fun h => pwGammaMobiusFrullaniResponse z x h/pwGammaRaySource x)
      (Ioi (0:ℝ)) := (pwGammaMobiusFrullaniResponse_integrable z hx).div_const (pwGammaRaySource x)
  apply hi.congr_fun _ measurableSet_Ioi
  intro h hh
  exact (pwGammaMobiusForwardResponse_source_eq z hx hh.le).symm

theorem pwGammaMobiusForwardResponse_integral (z : ℂ) {x : ℝ} (hx : 0<x) :
    (∫h in Ioi (0:ℝ), pwGammaMobiusForwardResponse z x h) =
      pwGammaMobiusTiltCurrent z x/pwGammaRaySource x := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun h hh => pwGammaMobiusForwardResponse_source_eq z hx hh.le), integral_div,
    pwGammaMobiusFrullaniResponse_integral z hx]

private theorem pwGammaForward_density_inverse_bound (k : ℕ) {x : ℝ} (hx : 0<x) :
    pwGammaReversibleDensity x/x^k ≤ ((k+2).factorial:ℝ)*x*Real.exp (-x) := by
  have hp := Real.pow_div_factorial_le_exp x⁻¹ (inv_pos.mpr hx).le (k+2)
  have hf : (0:ℝ)<(k+2).factorial := by positivity
  have hb : (x⁻¹)^(k+2)*Real.exp (-x⁻¹) ≤ ((k+2).factorial:ℝ) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr
      (by simpa only [mul_comm] using (div_le_iff₀ hf).mp hp)
  calc
    _ = (x*Real.exp (-x))*((x⁻¹)^(k+2)*Real.exp (-x⁻¹)) := by
      unfold pwGammaReversibleDensity
      rw [sub_eq_add_neg, Real.exp_add, pow_add, inv_pow]
      field_simp
    _ ≤ (x*Real.exp (-x))*((k+2).factorial:ℝ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem pwGammaReversibleDensity_shiftedPower_bound (k : ℕ) {x : ℝ} (hx : 0<x) :
    pwGammaReversibleDensity x*(1+1/x)^k ≤
      ((2:ℝ)^(k-1)*(((2:ℕ).factorial:ℝ)+((k+2).factorial:ℝ)))*x*Real.exp (-x) := by
  have ha := add_pow_le (show (0:ℝ)≤1 by positivity) (show (0:ℝ)≤1/x by positivity) k
  have hw := (pwGammaReversibleDensity_pos hx).le
  calc
    _ ≤ pwGammaReversibleDensity x*((2:ℝ)^(k-1)*(1^k+(1/x)^k)) :=
      mul_le_mul_of_nonneg_left ha hw
    _ = (2:ℝ)^(k-1)*(pwGammaReversibleDensity x/x^0+pwGammaReversibleDensity x/x^k) := by
      rw [div_pow, one_pow, pow_zero]
      ring
    _ ≤ (2:ℝ)^(k-1)*(((2:ℕ).factorial:ℝ)*x*Real.exp (-x)+
        ((k+2).factorial:ℝ)*x*Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left (add_le_add (pwGammaForward_density_inverse_bound 0 hx)
        (pwGammaForward_density_inverse_bound k hx)) (by positivity)
    _ = _ := by ring

def pwGammaMobiusForwardPairKernel (z v : ℂ) (p : ℝ×ℝ) : ℂ :=
  (pwGammaReversibleDensity p.1:ℂ)*(starRingEnd ℂ) (pwGammaMobiusTilt z p.1/pwGammaRaySource p.1)*
    pwGammaMobiusForwardResponse v p.1 p.2

theorem pwGammaMobiusForwardPairKernel_measurable (z v : ℂ) :
    Measurable (pwGammaMobiusForwardPairKernel z v) := by
  unfold pwGammaMobiusForwardPairKernel
  have hw : Measurable (fun p : ℝ×ℝ => (pwGammaReversibleDensity p.1:ℂ)) := by
    unfold pwGammaReversibleDensity
    fun_prop
  exact (hw.mul (Complex.continuous_conj.measurable.comp
    ((pwGammaMobiusGroundQuotient_measurable z).comp measurable_fst))).mul
    (pwGammaMobiusForwardResponse_measurable v)

theorem pwGammaMobiusForwardPairKernel_bound (z v : ℂ) :
    ∃C:ℝ, 0≤C ∧ ∀x h:ℝ, 0<x → 0<h →
      ‖pwGammaMobiusForwardPairKernel z v (x,h)‖≤C*x*Real.exp (-x)*Real.exp (-h) := by
  obtain ⟨p,A,hA,ha⟩ := pwGammaMobiusGroundQuotient_polynomial_bound z
  obtain ⟨r,B,hB,hb⟩ := pwGammaMobiusForwardResponse_bound v
  let D : ℝ := (2:ℝ)^(p+r-1)*(((2:ℕ).factorial:ℝ)+((p+r+2).factorial:ℝ))
  have hD : 0≤D := by positivity
  refine ⟨A*B*D,by positivity,fun x h hx hh => ?_⟩
  have hw := (pwGammaReversibleDensity_pos hx).le
  unfold pwGammaMobiusForwardPairKernel
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hw,Complex.norm_conj]
  calc
    _ ≤ pwGammaReversibleDensity x*(A*(1+1/x)^p)*(B*(1+1/x)^r*Real.exp (-h)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (ha x hx) hw) (hb x h hx hh)
        (norm_nonneg _) (by positivity)
    _ = (A*B*Real.exp (-h))*(pwGammaReversibleDensity x*(1+1/x)^(p+r)) := by rw [pow_add]; ring
    _ ≤ (A*B*Real.exp (-h))*(D*x*Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left (pwGammaReversibleDensity_shiftedPower_bound (p+r) hx) (by positivity)
    _ = _ := by ring

theorem pwGammaMobiusForwardPairKernel_integrable (z v : ℂ) :
    Integrable (pwGammaMobiusForwardPairKernel z v)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusForwardPairKernel_bound z v
  have hx : IntegrableOn (fun x : ℝ => C*x*Real.exp (-x)) (Ioi 0) := by
    change Integrable (fun x : ℝ => C*x*Real.exp (-x)) (volume.restrict (Ioi (0:ℝ)))
    have hp := Real.GammaIntegral_convergent (s := (1:ℕ)+1) (by positivity)
    simpa only [add_sub_cancel_right,Real.rpow_natCast,pow_one,mul_assoc,mul_comm,mul_left_comm] using hp.const_mul C
  apply (hx.mul_prod (integrableOn_exp_neg_Ioi 0)).mono'
    (pwGammaMobiusForwardPairKernel_measurable z v).aestronglyMeasurable
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  exact hb p.1 p.2 hp.1 hp.2

theorem pwGammaMobiusForwardPairKernel_section_integral (z v : ℂ) {x : ℝ} (hx : 0<x) :
    (∫h in Ioi (0:ℝ), pwGammaMobiusForwardPairKernel z v (x,h)) =
      (pwGammaReversibleDensity x:ℂ)*(starRingEnd ℂ) (pwGammaMobiusTilt z x/pwGammaRaySource x)*
        (pwGammaMobiusTiltCurrent v x/pwGammaRaySource x) := by
  unfold pwGammaMobiusForwardPairKernel
  dsimp only
  rw [integral_const_mul,pwGammaMobiusForwardResponse_integral v hx]

theorem pwGammaMobiusForwardPair_original_integrable (z v : ℂ) :
    IntegrableOn (fun x => (pwGammaReversibleDensity x:ℂ)*
      (starRingEnd ℂ) (pwGammaMobiusTilt z x/pwGammaRaySource x)*
      (pwGammaMobiusTiltCurrent v x/pwGammaRaySource x)) (Ioi 0) := by
  have hi : IntegrableOn (fun x => ∫h in Ioi (0:ℝ), pwGammaMobiusForwardPairKernel z v (x,h))
      (Ioi (0:ℝ)) := (pwGammaMobiusForwardPairKernel_integrable z v).integral_prod_left
  apply hi.congr_fun _ measurableSet_Ioi
  intro x hx
  exact pwGammaMobiusForwardPairKernel_section_integral z v hx


/-- The actual recipient interval maps onto the transported cutoff ray. -/
theorem pwGammaAdjointGain_reciprocal_image {y d : ℝ} (hy : 0<y) (hdy : d<y) :
    (fun x : ℝ => x⁻¹-y⁻¹) '' Ioo 0 (y-d) = Ioi (pwGammaAdjointCutoffLower y d) := by
  have hpos := sub_pos.mpr hdy
  rw [← pwGammaAdjointCutoffLower_displacement hy.ne' hpos.ne']
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact sub_lt_sub_right ((inv_lt_inv₀ hpos hx.1).mpr hx.2) _
  · intro hr
    have hr' : (y-d)⁻¹<r+y⁻¹ := by change (y-d)⁻¹-y⁻¹<r at hr; linarith
    have hr0 : 0<r+y⁻¹ := (inv_pos.mpr hpos).trans hr'
    refine ⟨(r+y⁻¹)⁻¹,⟨inv_pos.mpr hr0,?_⟩,?_⟩
    · simpa only [inv_inv] using (inv_lt_inv₀ hr0 (inv_pos.mpr hpos)).mpr hr'
    · simp only [inv_inv,add_sub_cancel_right]

def pwGammaMobiusForwardGainDensity (z v : ℂ) (x y : ℝ) : ℂ :=
  (pwGammaReversibleDensity x:ℂ)*(starRingEnd ℂ) (pwGammaMobiusTilt z x/pwGammaRaySource x)*
    (pwGammaMobiusTilt v y/pwGammaRaySource y)*(pwGammaForwardJumpRate x y:ℂ)

/-- Exact full-source gain substitution with its original Jacobian. -/
theorem pwGammaMobiusForwardGainDensity_reciprocal_integral (z v : ℂ) {y d : ℝ}
    (hy : 0<y) (hd : 0<d) (hdy : d<y) :
    (∫x in Ioo 0 (y-d), pwGammaMobiusForwardGainDensity z v x y) =
      (pwGammaReversibleDensity y:ℂ)*(pwGammaMobiusTilt v y/pwGammaRaySource y)*
        (∫h in Ioi (pwGammaAdjointCutoffLower y d), (Real.exp (-h)/h:ℝ)*
          (starRingEnd ℂ) (pwGammaMobiusTilt z (1/(1/y+h))/pwGammaRaySource (1/(1/y+h)))) := by
  let G : ℝ → ℂ := fun h => (Real.exp (-h)/h:ℝ)*
    (starRingEnd ℂ) (pwGammaMobiusTilt z (1/(1/y+h))/pwGammaRaySource (1/(1/y+h)))
  have hinj : InjOn (fun x : ℝ => x⁻¹-y⁻¹) (Ioo 0 (y-d)) := by
    intro x hx t ht he
    apply inv_injective
    dsimp only at he
    linear_combination he
  have hi := integral_image_eq_integral_abs_deriv_smul
    (f:=fun x : ℝ => x⁻¹-y⁻¹) (f':=fun x : ℝ => -(x^2)⁻¹)
    measurableSet_Ioo
    (fun x hx => (pwGammaBackwardJump_displacement_hasDerivAt (ne_of_gt hx.1) y).hasDerivWithinAt)
    hinj G
  rw [pwGammaAdjointGain_reciprocal_image hy hdy] at hi
  change _ = (pwGammaReversibleDensity y:ℂ)*(pwGammaMobiusTilt v y/pwGammaRaySource y)*
    ∫h in Ioi (pwGammaAdjointCutoffLower y d), G h
  rw [hi, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hx0 : 0<x := hx.1
  have hxy : x<y := by linarith [hx.2]
  have hxarg : 1/(1/y+(x⁻¹-y⁻¹))=x := by
    rw [one_div,one_div,show y⁻¹+(x⁻¹-y⁻¹)=x⁻¹ by ring,inv_inv]
  have hw := pwGammaReversibleDensity_detailedBalance (x:=x) (y:=y) hy.ne'
  rw [← pwGammaBackwardJumpRate_changeOfVariables hx0 hxy] at hw
  unfold pwGammaMobiusForwardGainDensity
  dsimp only [G]
  rw [hxarg,abs_neg,abs_of_pos (by positivity : 0<(x^2)⁻¹),Complex.real_smul]
  have hwc := congrArg (fun t : ℝ => (t:ℂ)) hw
  push_cast at hwc ⊢
  linear_combination (starRingEnd ℂ) (pwGammaMobiusTilt z x/pwGammaRaySource x)*
    (pwGammaMobiusTilt v y/pwGammaRaySource y)*hwc


theorem pwGammaMobiusForwardGainDensity_bound (z v : ℂ) :
    ∃C:ℝ, 0≤C ∧ ∀x h:ℝ, 0<x → 0<h →
      ‖pwGammaMobiusForwardGainDensity z v x (x+h)‖≤C*x*Real.exp (-x)*(Real.exp (-h)/h) := by
  obtain ⟨p,A,hA,ha⟩ := pwGammaMobiusGroundQuotient_polynomial_bound z
  obtain ⟨q,B,hB,hb⟩ := pwGammaMobiusGroundQuotient_polynomial_bound v
  let D : ℝ := (2:ℝ)^(p+q-1)*(((2:ℕ).factorial:ℝ)+((p+q+2).factorial:ℝ))
  have hD : 0≤D := by positivity
  refine ⟨A*B*D,by positivity,fun x h hx hh => ?_⟩
  have hw := (pwGammaReversibleDensity_pos hx).le
  have hv : ‖pwGammaMobiusTilt v (x+h)/pwGammaRaySource (x+h)‖≤B*(1+1/x)^q := by
    apply (hb (x+h) (add_pos hx hh)).trans
    apply mul_le_mul_of_nonneg_left _ hB
    apply pow_le_pow_left₀ (by positivity)
    linarith [one_div_le_one_div_of_le hx (show x≤x+h by linarith)]
  unfold pwGammaMobiusForwardGainDensity pwGammaForwardJumpRate
  rw [add_sub_cancel_left,norm_mul,norm_mul,norm_mul,Complex.norm_real,
    Complex.norm_real,Real.norm_of_nonneg hw,Real.norm_of_nonneg (by positivity : 0≤Real.exp (-h)/h),
    Complex.norm_conj]
  calc
    _ ≤ pwGammaReversibleDensity x*(A*(1+1/x)^p)*(B*(1+1/x)^q)*(Real.exp (-h)/h) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ha x hx) hw) hv (norm_nonneg _) (by positivity)
    _ = (A*B*(Real.exp (-h)/h))*(pwGammaReversibleDensity x*(1+1/x)^(p+q)) := by rw [pow_add]; ring
    _ ≤ (A*B*(Real.exp (-h)/h))*(D*x*Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left (pwGammaReversibleDensity_shiftedPower_bound (p+q) hx) (by positivity)
    _ = _ := by ring

theorem pwGammaMobiusForwardGainDensity_measurable (z v : ℂ) :
    Measurable (fun p : ℝ×ℝ => pwGammaMobiusForwardGainDensity z v p.1 p.2) := by
  have hg := pwGammaMobiusGroundQuotient_measurable
  have hw : Measurable (fun p : ℝ×ℝ => (pwGammaReversibleDensity p.1:ℂ)) := by
    unfold pwGammaReversibleDensity
    fun_prop
  have hk : Measurable (fun p : ℝ×ℝ => (pwGammaForwardJumpRate p.1 p.2:ℂ)) := by
    unfold pwGammaForwardJumpRate
    fun_prop
  exact ((hw.mul (Complex.continuous_conj.measurable.comp ((hg z).comp measurable_fst))).mul
    ((hg v).comp measurable_snd)).mul hk

theorem pwGammaMobiusForwardGainDensity_cutoff_integrable (z v : ℂ) {d : ℝ} (hd : 0<d) :
    Integrable (fun p : ℝ×ℝ => pwGammaMobiusForwardGainDensity z v p.1 (p.1+p.2))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi d))) := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusForwardGainDensity_bound z v
  have hx : IntegrableOn (fun x : ℝ => C*x*Real.exp (-x)) (Ioi 0) := by
    change Integrable (fun x : ℝ => C*x*Real.exp (-x)) (volume.restrict (Ioi (0:ℝ)))
    have hp := Real.GammaIntegral_convergent (s := (1:ℕ)+1) (by positivity)
    simpa only [add_sub_cancel_right,Real.rpow_natCast,pow_one,mul_assoc,mul_comm,mul_left_comm] using hp.const_mul C
  apply (hx.mul_prod ((integrableOn_exp_neg_Ioi d).div_const d)).mono'
    ((pwGammaMobiusForwardGainDensity_measurable z v).comp
      (by fun_prop : Measurable (fun p : ℝ×ℝ => (p.1,p.1+p.2)))).aestronglyMeasurable
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  have hx0 : 0<p.1 := hp.1
  apply (hb p.1 p.2 hx0 (hd.trans hp.2)).trans
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Real.exp_pos _).le hd hp.2.le) (by positivity)

def pwGammaMobiusForwardCutoffGain (z v : ℂ) (d : ℝ) : ℝ×ℝ → ℂ :=
  (Ioi (0:ℝ) ×ˢ Ioi d).indicator (fun p => pwGammaMobiusForwardGainDensity z v p.1 (p.1+p.2))

theorem pwGammaMobiusForwardCutoffGain_integrable (z v : ℂ) {d : ℝ} (hd : 0<d) :
    Integrable (pwGammaMobiusForwardCutoffGain z v d) (volume.prod volume) := by
  have hi : IntegrableOn (fun p : ℝ×ℝ => pwGammaMobiusForwardGainDensity z v p.1 (p.1+p.2))
      (Ioi (0:ℝ) ×ˢ Ioi d) (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact pwGammaMobiusForwardGainDensity_cutoff_integrable z v hd
  exact hi.integrable_indicator (measurableSet_Ioi.prod measurableSet_Ioi)

private theorem pwGammaForwardGain_shear_integrable (z v : ℂ) {d : ℝ} (hd : 0<d) :
    Integrable (fun p : ℝ×ℝ => pwGammaMobiusForwardCutoffGain z v d (p.1,p.2-p.1))
      (volume.prod volume) :=
  (measurePreserving_prod_sub (volume:Measure ℝ) volume).integrable_comp_of_integrable
    (pwGammaMobiusForwardCutoffGain_integrable z v hd)

private theorem pwGammaForwardGain_shear_eq (z v : ℂ) (d x y : ℝ) :
    pwGammaMobiusForwardCutoffGain z v d (x,y-x) =
      (Ioo 0 (y-d)).indicator (fun x => pwGammaMobiusForwardGainDensity z v x y) x := by
  unfold pwGammaMobiusForwardCutoffGain
  have he : (x,y-x)∈Ioi (0:ℝ)×ˢIoi d ↔ x∈Ioo 0 (y-d) := by
    simp only [mem_prod,mem_Ioi,mem_Ioo]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  by_cases hx : x∈Ioo 0 (y-d)
  · rw [indicator_of_mem (he.mpr hx),indicator_of_mem hx]
    congr 1
    ring
  · rw [indicator_of_notMem (not_iff_not.mpr he |>.mpr hx),indicator_of_notMem hx]

theorem pwGammaMobiusForwardGainDensity_triangle_integrable (z v : ℂ) {d : ℝ} (hd : 0<d) :
    Integrable (fun y => ∫x in Ioo 0 (y-d), pwGammaMobiusForwardGainDensity z v x y) volume := by
  have hi := (pwGammaForwardGain_shear_integrable z v hd).integral_prod_right
  apply hi.congr
  filter_upwards with y
  simp_rw [pwGammaForwardGain_shear_eq,integral_indicator measurableSet_Ioo]

/-- Exact full-source triangular Fubini identity, before reciprocal substitution. -/
theorem pwGammaMobiusForwardGainDensity_triangle_integral (z v : ℂ) {d : ℝ} (hd : 0<d) :
    (∫x in Ioi (0:ℝ), ∫h in Ioi d, pwGammaMobiusForwardGainDensity z v x (x+h)) =
      ∫y in Ioi d, ∫x in Ioo 0 (y-d), pwGammaMobiusForwardGainDensity z v x y := by
  have hI : (∫p, pwGammaMobiusForwardCutoffGain z v d p ∂(volume.prod volume)) =
      ∫x in Ioi (0:ℝ), ∫h in Ioi d, pwGammaMobiusForwardGainDensity z v x (x+h) := by
    unfold pwGammaMobiusForwardCutoffGain
    rw [integral_indicator (measurableSet_Ioi.prod measurableSet_Ioi), ← Measure.prod_restrict,
      integral_prod _ (pwGammaMobiusForwardGainDensity_cutoff_integrable z v hd)]
  have hS := (measurePreserving_prod_sub (volume:Measure ℝ) volume).integral_comp
    (MeasurableEquiv.shearSubRight ℝ).measurableEmbedding (pwGammaMobiusForwardCutoffGain z v d)
  rw [← hI, ← hS,integral_prod_symm _ (pwGammaForwardGain_shear_integrable z v hd)]
  simp_rw [pwGammaForwardGain_shear_eq, integral_indicator measurableSet_Ioo]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : d<y
  · rw [indicator_of_mem (show y∈Ioi d from hy)]
  · rw [indicator_of_notMem (show y∉Ioi d from hy), Ioo_eq_empty_of_le (by linarith : y-d≤0)]
    simp

/-- The original gain is exactly the transported reciprocal gain, with both outer domains retained. -/
theorem pwGammaMobiusForwardGainDensity_full_transposition (z v : ℂ) {d : ℝ} (hd : 0<d) :
    (∫x in Ioi (0:ℝ), ∫h in Ioi d, pwGammaMobiusForwardGainDensity z v x (x+h)) =
      ∫y in Ioi d, (pwGammaReversibleDensity y:ℂ)*(pwGammaMobiusTilt v y/pwGammaRaySource y)*
        (∫h in Ioi (pwGammaAdjointCutoffLower y d), (Real.exp (-h)/h:ℝ)*
          (starRingEnd ℂ) (pwGammaMobiusTilt z (1/(1/y+h))/pwGammaRaySource (1/(1/y+h)))) := by
  rw [pwGammaMobiusForwardGainDensity_triangle_integral z v hd]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  exact pwGammaMobiusForwardGainDensity_reciprocal_integral z v (hd.trans hy) hd hy


private theorem pwGammaGain_exp_tail_integrable {a : ℝ} (ha : 0<a) :
    IntegrableOn (fun h : ℝ => ((Real.exp (-h)/h:ℝ):ℂ)) (Ioi a) := by
  apply ((integrableOn_exp_neg_Ioi a).div_const a).mono'
    (show Measurable (fun h : ℝ => ((Real.exp (-h)/h:ℝ):ℂ)) by fun_prop).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hh0 := ha.trans hh
  rw [Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤Real.exp (-h)/h)]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le ha hh.le

theorem pwGammaMobiusBackwardGain_decomposition (z : ℂ) (y h : ℝ) :
    ((Real.exp (-h)/h:ℝ):ℂ)*(starRingEnd ℂ)
      (pwGammaMobiusTilt z (1/(1/y+h))/pwGammaRaySource (1/(1/y+h))) =
    (starRingEnd ℂ) (pwGammaMobiusReciprocalResponse z (1/y) h)+
      ((Real.exp (-h)/h:ℝ):ℂ)*(starRingEnd ℂ) (pwGammaMobiusTilt z y/pwGammaRaySource y) := by
  have he : ((Real.exp (-h)/h:ℝ):ℂ)*
      (pwGammaMobiusTilt z (1/(1/y+h))/pwGammaRaySource (1/(1/y+h))) =
      pwGammaMobiusReciprocalResponse z (1/y) h+
      ((Real.exp (-h)/h:ℝ):ℂ)*(pwGammaMobiusTilt z y/pwGammaRaySource y) := by
    unfold pwGammaMobiusReciprocalResponse pwGammaMobiusReciprocalTail
    simp only [one_div,inv_inv]
    push_cast
    ring
  simpa only [map_add,map_mul,Complex.conj_ofReal] using congrArg (starRingEnd ℂ) he

theorem pwGammaMobiusBackwardGain_integrable (z : ℂ) {y a : ℝ} (hy : 0<y) (ha : 0<a) :
    IntegrableOn (fun h : ℝ => ((Real.exp (-h)/h:ℝ):ℂ)*(starRingEnd ℂ)
      (pwGammaMobiusTilt z (1/(1/y+h))/pwGammaRaySource (1/(1/y+h)))) (Ioi a) := by
  have hr : IntegrableOn (fun h => (starRingEnd ℂ) (pwGammaMobiusReciprocalResponse z (1/y) h))
      (Ioi a) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
        ((pwGammaMobiusReciprocalResponse_integrable z (show 0<1/y by positivity)).mono_set (Ioi_subset_Ioi ha.le))
  apply (hr.add ((pwGammaGain_exp_tail_integrable ha).mul_const
    ((starRingEnd ℂ) (pwGammaMobiusTilt z y/pwGammaRaySource y)))).congr_fun _ measurableSet_Ioi
  intro h _
  exact (pwGammaMobiusBackwardGain_decomposition z y h).symm

theorem pwGammaMobiusForwardGainDensity_section_integrable (z v : ℂ) {d x : ℝ} (hd : 0<d) (hx : 0<x) :
    IntegrableOn (fun h => pwGammaMobiusForwardGainDensity z v x (x+h)) (Ioi d) := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusForwardGainDensity_bound z v
  apply (((integrableOn_exp_neg_Ioi d).div_const d).const_mul (C*x*Real.exp (-x))).mono'
    ((pwGammaMobiusForwardGainDensity_measurable z v).comp
      (by fun_prop : Measurable (fun h : ℝ => (x,x+h)))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  apply (hb x h hx (hd.trans hh)).trans
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Real.exp_pos _).le hd hh.le) (by positivity)

theorem pwGammaMobiusForwardGainDensity_recipient_integrable (z v : ℂ) {y d : ℝ}
    (hd : 0<d) :
    IntegrableOn (fun x => pwGammaMobiusForwardGainDensity z v x y) (Ioo 0 (y-d)) := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusForwardGainDensity_bound z v
  have hi : IntegrableOn (fun x : ℝ => (C/d)*x*Real.exp (-x)) (Ioi 0) := by
    change Integrable (fun x : ℝ => (C/d)*x*Real.exp (-x)) (volume.restrict (Ioi (0:ℝ)))
    have hp := Real.GammaIntegral_convergent (s := (1:ℕ)+1) (by positivity)
    simpa only [add_sub_cancel_right,Real.rpow_natCast,pow_one,mul_assoc,mul_comm,mul_left_comm] using hp.const_mul (C/d)
  apply (hi.mono_set Ioo_subset_Ioi_self).mono'
    ((pwGammaMobiusForwardGainDensity_measurable z v).comp
      (by fun_prop : Measurable (fun x : ℝ => (x,y)))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hgap : d<y-x := by linarith [hx.2]
  have hgap0 := hd.trans hgap
  have ht := hb x (y-x) hx.1 hgap0
  rw [show x+(y-x)=y by ring] at ht
  have hx0 : 0<x := hx.1
  have he : Real.exp (-(y-x))/(y-x)≤1/d := by
    apply (div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith)) hgap0.le).trans
    exact one_div_le_one_div_of_le hd hgap.le
  calc
    _ ≤ C*x*Real.exp (-x)*(Real.exp (-(y-x))/(y-x)) := ht
    _ ≤ C*x*Real.exp (-x)*(1/d) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

theorem pwGammaMobiusForwardGainDensity_outer_admission (z v : ℂ) {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun x => ∫h in Ioi d, pwGammaMobiusForwardGainDensity z v x (x+h)) (Ioi 0) ∧
    IntegrableOn (fun y => (pwGammaReversibleDensity y:ℂ)*(pwGammaMobiusTilt v y/pwGammaRaySource y)*
        (∫h in Ioi (pwGammaAdjointCutoffLower y d), (Real.exp (-h)/h:ℝ)*
          (starRingEnd ℂ) (pwGammaMobiusTilt z (1/(1/y+h))/pwGammaRaySource (1/(1/y+h))))) (Ioi d) := by
  constructor
  · exact (pwGammaMobiusForwardGainDensity_cutoff_integrable z v hd).integral_prod_left
  · have hi : IntegrableOn (fun y => ∫x in Ioo 0 (y-d), pwGammaMobiusForwardGainDensity z v x y)
        (Ioi d) := (pwGammaMobiusForwardGainDensity_triangle_integrable z v hd).integrableOn
    apply hi.congr_fun _ measurableSet_Ioi
    intro y hy
    exact pwGammaMobiusForwardGainDensity_reciprocal_integral z v (hd.trans hy) hd hy


private def pwGammaForwardPairMask (z v : ℂ) (d : ℝ) (p : ℝ×ℝ) : ℂ :=
  if d<p.2 then pwGammaMobiusForwardPairKernel z v p else 0

private theorem pwGammaForwardPairMask_measurable (z v : ℂ) (d : ℝ) :
    Measurable (pwGammaForwardPairMask z v d) := by
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    (pwGammaMobiusForwardPairKernel_measurable z v) measurable_const

private theorem pwGammaForwardPairMask_bound (z v : ℂ) (d : ℝ) (p : ℝ×ℝ) :
    ‖pwGammaForwardPairMask z v d p‖≤‖pwGammaMobiusForwardPairKernel z v p‖ := by
  unfold pwGammaForwardPairMask
  split_ifs
  · exact le_refl _
  · simpa only [norm_zero] using norm_nonneg (pwGammaMobiusForwardPairKernel z v p)

private theorem pwGammaForwardPairMask_integrable (z v : ℂ) (d : ℝ) :
    Integrable (pwGammaForwardPairMask z v d)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
  (pwGammaMobiusForwardPairKernel_integrable z v).mono
    (pwGammaForwardPairMask_measurable z v d).aestronglyMeasurable
    (Eventually.of_forall (pwGammaForwardPairMask_bound z v d))

private theorem pwGammaForwardPairMask_section (z v : ℂ) {d : ℝ} (hd : 0≤d) (x : ℝ) :
    (∫h in Ioi (0:ℝ), pwGammaForwardPairMask z v d (x,h)) =
      ∫h in Ioi d, pwGammaMobiusForwardPairKernel z v (x,h) := by
  change (∫h in Ioi (0:ℝ), (Ioi d).indicator (fun h => pwGammaMobiusForwardPairKernel z v (x,h)) h) = _
  rw [setIntegral_indicator measurableSet_Ioi,inter_eq_right.mpr (Ioi_subset_Ioi hd)]

theorem pwGammaMobiusForwardPairKernel_cutoff_outer_integrable (z v : ℂ) {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun x => ∫h in Ioi d, pwGammaMobiusForwardPairKernel z v (x,h)) (Ioi 0) := by
  have hi : IntegrableOn (fun x => ∫h in Ioi (0:ℝ), pwGammaForwardPairMask z v d (x,h))
      (Ioi (0:ℝ)) := (pwGammaForwardPairMask_integrable z v d).integral_prod_left
  apply hi.congr_fun _ measurableSet_Ioi
  intro x _
  exact pwGammaForwardPairMask_section z v hd.le x

/-- The original forward cutoff converges to the admitted complete arithmetic current pairing. -/
theorem pwGammaMobiusForwardPairKernel_cutoff_tendsto (z v : ℂ) :
    Tendsto (fun d => ∫x in Ioi (0:ℝ), ∫h in Ioi d, pwGammaMobiusForwardPairKernel z v (x,h))
      (𝓝[>] (0:ℝ)) (𝓝 (∫x in Ioi (0:ℝ), (pwGammaReversibleDensity x:ℂ)*
      (starRingEnd ℂ) (pwGammaMobiusTilt z x/pwGammaRaySource x)*
      (pwGammaMobiusTiltCurrent v x/pwGammaRaySource x))) := by
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun p => ‖pwGammaMobiusForwardPairKernel z v p‖)
    (Eventually.of_forall fun d => (pwGammaForwardPairMask_measurable z v d).aestronglyMeasurable)
    (Eventually.of_forall fun d => Eventually.of_forall (pwGammaForwardPairMask_bound z v d))
    (pwGammaMobiusForwardPairKernel_integrable z v).norm
    (show ∀ᵐ p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))),
      Tendsto (fun d => pwGammaForwardPairMask z v d p) (𝓝[>] (0:ℝ))
        (𝓝 (pwGammaMobiusForwardPairKernel z v p)) from by
      rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
      have hd : Tendsto (fun d : ℝ => d) (𝓝[>] (0:ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      apply tendsto_const_nhds.congr'
      filter_upwards [hd.eventually (gt_mem_nhds (show 0<p.2 from hp.2))] with d hd
      exact (if_pos hd).symm)
  rw [integral_prod _ (pwGammaMobiusForwardPairKernel_integrable z v)] at ht
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => pwGammaMobiusForwardPairKernel_section_integral z v hx)] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  rw [integral_prod _ (pwGammaForwardPairMask_integrable z v d)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => pwGammaForwardPairMask_section z v (le_of_lt hd) x)

end
end RHTower
