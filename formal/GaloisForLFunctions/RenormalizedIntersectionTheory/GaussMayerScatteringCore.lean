import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEisensteinLift
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyMellinSymbol

/-!
# Finite-energy scattering subtraction for the Mayer Cauchy transform

The actual Epstein field becomes square-integrable with central Mellin weight after
subtracting its two zeta axes and its reciprocal scattering powers. The Eisenstein
Fourier expansion controls infinity; height reciprocity controls zero. The actual
Cauchy transform retains an explicit boundary correction with coefficient
`2 * riemannZeta (w - 1) / (w - 1)`.
-/

open Complex Set MeasureTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerCauchyMellinSymbol MayerEpsteinQuadrants
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringCore

/-- The actual outgoing Eisenstein coefficient after archimedean normalization. -/
def scatteringCoefficient (w : ℂ) : ℂ :=
  _root_.RHTower.reflectedCompletedLambda (w-1)/Gammaℝ w

/-- The reciprocal pair of scattering powers. -/
def scatteringPowers (w : ℂ) (a : ℝ) : ℂ := (a : ℂ)^(-1 : ℂ)+(a : ℂ)^(1-w)

/-- Remove both zeta axes and both reciprocal scattering tails from the actual field. -/
def fieldCore (w : ℂ) (a : ℝ) : ℂ := epsteinField w a-
  riemannZeta w*(1+(a : ℂ)^(-w))-scatteringCoefficient w*scatteringPowers w a

private theorem power_quotient {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (u : ℂ) :
    ((a/t : ℝ) : ℂ)^(-u)=(a : ℂ)^(-u)*(t : ℂ)^u := by
  rw [div_eq_mul_inv,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (inv_pos.mpr ht).le,Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm),
    ← Complex.cpow_neg,neg_neg]

private theorem power_integrand {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (w u : ℂ) :
    cauchyKernel w t*((a/t : ℝ) : ℂ)^(-u)/(t : ℂ)=
      (a : ℂ)^(-u)*((t : ℂ)^(u-1)*cauchyKernel w t) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hp : (t : ℂ)^(u-1)=(t : ℂ)^u/(t : ℂ) := by
    rw [Complex.cpow_sub _ _ htC,Complex.cpow_one]
  rw [power_quotient ha ht,hp]
  ring

/-- Every admissible power mode has an absolutely convergent Cauchy transform. -/
theorem power_integrable {w u : ℂ} (hw : 0 < w.re) (hu : -1 < u.re)
    (hwu : u.re < w.re+1) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => cauchyKernel w t*((a/t : ℝ) : ℂ)^(-u)/(t : ℂ)) (Ioi 0) := by
  have hm := (cauchyKernel_hasMellin hw hu hwu).1
  change IntegrableOn (fun t : ℝ => (t : ℂ)^(u-1) • cauchyKernel w t) (Ioi 0) at hm
  simp only [smul_eq_mul] at hm
  exact MeasureTheory.IntegrableOn.congr_fun (hm.const_mul ((a : ℂ)^(-u)))
    (fun t ht => (power_integrand ha ht w u).symm) measurableSet_Ioi

/-- The certified Gamma symbol is the exact eigenvalue of every admissible power mode. -/
theorem power_convolution {w u : ℂ} (hw : 0 < w.re) (hu : -1 < u.re)
    (hwu : u.re < w.re+1) {a : ℝ} (ha : 0 < a) :
    _root_.RHTower.positiveMellinConvolution (cauchyKernel w) (fun x : ℝ => (x : ℂ)^(-u)) a=
      (a : ℂ)^(-u)*symbol w u := by
  rw [_root_.RHTower.positiveMellinConvolution,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => power_integrand ha ht w u),
    integral_const_mul]
  have h := (cauchyKernel_hasMellin hw hu hwu).2
  simpa only [mellin,smul_eq_mul] using congrArg (fun v : ℂ => (a : ℂ)^(-u)*v) h

#print axioms power_integrable
#print axioms power_convolution

/-- The two reciprocal scattering powers have the same actual Cauchy multiplier. -/
theorem symbol_scattering_pair (w : ℂ) : symbol w (w-1)=symbol w 1 := symbol_reflection w 1

/-- The outgoing coefficient maps to the boundary charge divided by `w−1`. -/
theorem scatteringCoefficient_mul_symbol_one {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im) :
    scatteringCoefficient w*symbol w 1=2*riemannZeta (w-1)/(w-1) := by
  have hminus : (w-1)/2 ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    linarith only [hi,him]
  have hW : w-1 ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact him.ne' hi
  have hG : Gamma (w/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith only [hw])
  have hM : Gamma ((w-1)/2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n he
    have hi := congrArg Complex.im he
    simp at hi
    linarith only [hi,him]
  have hP : (Real.pi : ℂ)^(1/2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hA : (Real.pi : ℂ)^(-w/2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hpi : (Real.pi : ℂ)^(-(w-1)/2)=(Real.pi : ℂ)^(-w/2)*(Real.pi : ℂ)^(1/2 : ℂ) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    congr 1
    ring
  have hrec : Gamma ((w+1)/2)=((w-1)/2)*Gamma ((w-1)/2) := by
    rw [show (w+1)/2=(w-1)/2+1 by ring,Complex.Gamma_add_one _ hminus]
  have hs : symbol w 1=Gamma (w/2)/((Real.pi : ℂ)^(1/2 : ℂ)*Gamma ((w+1)/2)) := by
    rw [symbol,show ((1 : ℂ)+1)/2=1 by norm_num,
      show (w+1-1)/2=w/2 by ring,Complex.Gamma_one,one_mul]
  rw [scatteringCoefficient,_root_.RHTower.reflectedCompletedLambda,Gammaℝ_def,Gammaℝ_def,hs,hpi,hrec]
  have halg (A P C D X Z : ℂ) (hA : A ≠ 0) (hP : P ≠ 0) (hC : C ≠ 0)
      (hD : D ≠ 0) (hX : X ≠ 0) :
      (A*P*D*Z/(A*C))*(C/(P*(X/2*D)))=2*Z/X := by field_simp
  exact halg _ _ _ _ _ _ hA hP hG hM hW

#print axioms symbol_scattering_pair
#print axioms scatteringCoefficient_mul_symbol_one


private def transformedPower (w u : ℂ) (a t : ℝ) : ℂ :=
  cauchyKernel w t*((a/t : ℝ) : ℂ)^(-u)/(t : ℂ)

private theorem transformedPower_integral {w u : ℂ} (hw : 0 < w.re) (hu : -1 < u.re)
    (hwu : u.re < w.re+1) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), transformedPower w u a t)=(a : ℂ)^(-u)*symbol w u := by
  simpa only [transformedPower,_root_.RHTower.positiveMellinConvolution] using
    power_convolution hw hu hwu ha

private theorem core_integrand (w : ℂ) (a t : ℝ) :
    cauchyKernel w t*fieldCore w (a/t)/(t : ℂ)=
      cauchyKernel w t*epsteinField w (a/t)/(t : ℂ)-
        riemannZeta w*(transformedPower w 0 a t+transformedPower w w a t)-
        scatteringCoefficient w*(transformedPower w 1 a t+transformedPower w (w-1) a t) := by
  simp only [fieldCore,scatteringPowers,transformedPower,neg_zero,Complex.cpow_zero,
    show -(w-1)=1-w by ring]
  ring

private theorem parameter_ne_two {w : ℂ} (him : 0 < w.im) : w ≠ 2 := by
  intro he
  have hi := congrArg Complex.im he
  simp at hi
  exact him.ne' hi

/-- Subtracting the actual axes and scattering powers preserves absolute Cauchy convergence. -/
theorem cauchyKernel_core_integrable {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => cauchyKernel w t*fieldCore w (a/t)/(t : ℂ)) (Ioi 0) := by
  have hE := MayerEpsteinContinuation.cauchyKernel_epstein_integrable hw (parameter_ne_two him) ha
  have h0 : IntegrableOn (transformedPower w 0 a) (Ioi 0) :=
    power_integrable hw (by norm_num) (by simp; linarith only [hw]) ha
  have hW : IntegrableOn (transformedPower w w a) (Ioi 0) :=
    power_integrable hw (by linarith only [hw]) (by linarith) ha
  have h1 : IntegrableOn (transformedPower w 1 a) (Ioi 0) :=
    power_integrable hw (by norm_num) (by simp; linarith only [hw]) ha
  have hM : IntegrableOn (transformedPower w (w-1) a) (Ioi 0) :=
    power_integrable hw (by simp; linarith only [hw]) (by simp; linarith) ha
  have h := (hE.sub ((h0.add hW).const_mul (riemannZeta w))).sub
    ((h1.add hM).const_mul (scatteringCoefficient w))
  exact MeasureTheory.IntegrableOn.congr_fun h (fun t _ => (core_integrand w a t).symm)
    measurableSet_Ioi

/-- The actual finite-energy core maps to the Mayer period with its exact boundary correction. -/
theorem cauchyKernel_core_period {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : a ∈ MayerScatteringPeriod.periodSegment) :
    _root_.RHTower.positiveMellinConvolution (cauchyKernel w) (fieldCore w) a=
      MayerScatteringPeriod.periodValue w a-riemannZeta w*(1+(a : ℂ)^(-w))-
        (2*riemannZeta (w-1)/(w-1))*scatteringPowers w a := by
  have ha0 : 0 < a := by linarith only [ha.1]
  have hE := MayerEpsteinContinuation.cauchyKernel_epstein_integrable hw (parameter_ne_two him) ha0
  have h0 : IntegrableOn (transformedPower w 0 a) (Ioi 0) :=
    power_integrable hw (by norm_num) (by simp; linarith only [hw]) ha0
  have hW : IntegrableOn (transformedPower w w a) (Ioi 0) :=
    power_integrable hw (by linarith only [hw]) (by linarith) ha0
  have h1 : IntegrableOn (transformedPower w 1 a) (Ioi 0) :=
    power_integrable hw (by norm_num) (by simp; linarith only [hw]) ha0
  have hM : IntegrableOn (transformedPower w (w-1) a) (Ioi 0) :=
    power_integrable hw (by simp; linarith only [hw]) (by simp; linarith) ha0
  have haxis : IntegrableOn (fun t => riemannZeta w*
      (transformedPower w 0 a t+transformedPower w w a t)) (Ioi 0) := (h0.add hW).const_mul _
  have hscatter : IntegrableOn (fun t => scatteringCoefficient w*
      (transformedPower w 1 a t+transformedPower w (w-1) a t)) (Ioi 0) := (h1.add hM).const_mul _
  have hperiod := MayerEpsteinContinuation.cauchyKernel_epstein_period hw (parameter_ne_two him) ha
  rw [_root_.RHTower.positiveMellinConvolution] at hperiod ⊢
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => core_integrand w a t),
    integral_sub (f := fun t => cauchyKernel w t*epsteinField w (a/t)/(t : ℂ)-
      riemannZeta w*(transformedPower w 0 a t+transformedPower w w a t))
      (hE.sub haxis) hscatter,integral_sub hE haxis,
    integral_const_mul,integral_const_mul,integral_add h0 hW,integral_add h1 hM,hperiod]
  have hs0 : symbol w 0=1 :=
    (cauchyKernel_hasMellin hw (u := 0) (by norm_num) (by simp; linarith only [hw])).2.symm.trans
      (cauchyKernel_mellin_zero hw).2
  have hsW : symbol w w=1 :=
    (cauchyKernel_hasMellin hw (u := w) (by linarith only [hw]) (by linarith)).2.symm.trans
      (cauchyKernel_mellin_spectral hw).2
  rw [transformedPower_integral hw (u := 0) (by norm_num) (by simp; linarith only [hw]) ha0,
    transformedPower_integral hw (u := w) (by linarith only [hw]) (by linarith) ha0,
    transformedPower_integral hw (u := 1) (by norm_num) (by simp; linarith only [hw]) ha0,
    transformedPower_integral hw (u := w-1) (by simp; linarith only [hw]) (by simp; linarith) ha0,
    hs0,hsW,symbol_scattering_pair,neg_zero,Complex.cpow_zero,one_mul,mul_one]
  have hpair : scatteringCoefficient w*
      ((a : ℂ)^(-1 : ℂ)*symbol w 1+(a : ℂ)^(-(w-1))*symbol w 1)=
      (scatteringCoefficient w*symbol w 1)*scatteringPowers w a := by
    rw [scatteringPowers,show -(w-1)=1-w by ring]
    ring
  rw [hpair,scatteringCoefficient_mul_symbol_one hw him]

#print axioms cauchyKernel_core_integrable
#print axioms cauchyKernel_core_period


private theorem inverse_power {a : ℝ} (ha : 0 < a) (u : ℂ) :
    ((1/a : ℝ) : ℂ)^u=(a : ℂ)^(-u) := by
  rw [one_div,Complex.ofReal_inv,Complex.inv_cpow _ _
    (by rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_ne_zero.symm),← Complex.cpow_neg]

private theorem paired_power_reciprocity {a : ℝ} (ha : 0 < a) (w u : ℂ) :
    (a : ℂ)^(-w)*(((1/a : ℝ) : ℂ)^(-u)+((1/a : ℝ) : ℂ)^(u-w))=
      (a : ℂ)^(-u)+(a : ℂ)^(u-w) := by
  have hA : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [mul_add,inverse_power ha,inverse_power ha,
    ← Complex.cpow_add _ _ hA,← Complex.cpow_add _ _ hA,
    show -w+ -(-u)=u-w by ring,show -w+ -(u-w)= -u by ring,add_comm]

/-- Subtracting reciprocal pairs preserves the exact height symmetry of the field. -/
theorem fieldCore_reciprocity {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 0 < a) : fieldCore w a=(a : ℂ)^(-w)*fieldCore w (1/a) := by
  have hE := MayerEpsteinReciprocity.reciprocity hw (parameter_ne_two him) ha
  have haxis : (a : ℂ)^(-w)*(1+((1/a : ℝ) : ℂ)^(-w))=1+(a : ℂ)^(-w) := by
    simpa only [neg_zero,Complex.cpow_zero,zero_sub] using paired_power_reciprocity ha w 0
  have hscatter : (a : ℂ)^(-w)*scatteringPowers w (1/a)=scatteringPowers w a :=
    paired_power_reciprocity ha w 1
  symm
  calc
    _ = (a : ℂ)^(-w)*epsteinField w (1/a)-
        riemannZeta w*((a : ℂ)^(-w)*(1+((1/a : ℝ) : ℂ)^(-w)))-
        scatteringCoefficient w*((a : ℂ)^(-w)*scatteringPowers w (1/a)) := by
      unfold fieldCore
      ring
    _ = _ := by rw [← hE,haxis,hscatter]; rfl

/-- The actual Fourier tail on the height axis with the same normalization as the Epstein field. -/
def normalizedTail (w : ℂ) (a : ℝ) : ℂ :=
  (a : ℂ)^(-w/2)/Gammaℝ w*
    _root_.RHTower.d4BMCompletedEisensteinCuspTailPart .scalar ((w-1)/2) 0 a

/-- The two actual Eisenstein constant terms are retained before renormalization. -/
theorem field_eq_constant_scattering_tail {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 0 < a) :
    epsteinField w a=riemannZeta w+scatteringCoefficient w*(a : ℂ)^(1-w)+normalizedTail w a := by
  have hA : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hG : Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hw
  have hpoint : _root_.RHTower.eisensteinLineModel ((w-1)/2) (MayerEisensteinLift.axisPoint a ha)=
      _root_.RHTower.d4BMCompletedEisensteinCuspConstantPart .scalar ((w-1)/2) a+
      _root_.RHTower.d4BMCompletedEisensteinCuspTailPart .scalar ((w-1)/2) 0 a := by
    simp [_root_.RHTower.eisensteinLineModel,MayerEisensteinLift.axisPoint,
      _root_.RHTower.d4BMCompletedEisensteinCuspLeg]
  have hpow1 : (a : ℂ)^(-w/2)*(a : ℂ)^(1-w/2)=(a : ℂ)^(1-w) := by
    rw [← Complex.cpow_add _ _ hA]
    congr 1
    ring
  have hpow2 : (a : ℂ)^(-w/2)*(a : ℂ)^(w/2)=1 := by
    rw [← Complex.cpow_add _ _ hA,show -w/2+w/2=0 by ring,Complex.cpow_zero]
  rw [← congrFun (MayerEisensteinLift.eisensteinField_eq_epsteinField hw him) a,
    MayerEisensteinLift.eisensteinField,dif_pos ha,hpoint,
    _root_.RHTower.cuspConstantPart_eq_msAB,_root_.RHTower.msA,_root_.RHTower.msB,
    show 1+2*((w-1)/2)=w by ring,show 2*((w-1)/2)=w-1 by ring,
    show 1/2-(w-1)/2=1-w/2 by ring,show 1/2+(w-1)/2=w/2 by ring]
  calc
    _ = (_root_.RHTower.reflectedCompletedLambda (w-1)/Gammaℝ w)*
          ((a : ℂ)^(-w/2)*(a : ℂ)^(1-w/2))+
        riemannZeta w*((a : ℂ)^(-w/2)*(a : ℂ)^(w/2))+normalizedTail w a := by
      simp only [_root_.RHTower.reflectedCompletedLambda,normalizedTail]
      field_simp
    _ = _ := by rw [hpow1,hpow2,mul_one,scatteringCoefficient]; ring

/-- At large heights only the opposite-endpoint power tails remain in the core. -/
theorem fieldCore_eq_tail {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 0 < a) :
    fieldCore w a=normalizedTail w a-riemannZeta w*(a : ℂ)^(-w)-
      scatteringCoefficient w*(a : ℂ)^(-1 : ℂ) := by
  rw [fieldCore,field_eq_constant_scattering_tail hw him ha,scatteringPowers]
  ring

/-- A nonnegative height-independent coefficient for the normalized Fourier tail. -/
def tailCoefficient (w : ℂ) : ℝ :=
  _root_.RHTower.tailConst ((w-1)/2)/(2*Real.pi*‖Gammaℝ w‖)

private theorem tailCoefficient_nonneg (w : ℂ) : 0 ≤ tailCoefficient w :=
  div_nonneg (_root_.RHTower.tailConst_nonneg _) (by positivity)

private theorem exp_decay_le_reciprocal {a : ℝ} (ha : 0 < a) :
    Real.exp (-(2*Real.pi*a)) ≤ 1/(2*Real.pi*a) := by
  have hp : 0 < 2*Real.pi*a := by positivity
  have h : 2*Real.pi*a ≤ Real.exp (2*Real.pi*a) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  rw [Real.exp_neg,inv_eq_one_div]
  exact (div_le_div_iff₀ (Real.exp_pos _) hp).mpr (by simpa only [one_mul] using h)

/-- The actual exponentially decaying tail satisfies a square-integrable power bound. -/
theorem normalizedTail_norm_le {w : ℂ} {a : ℝ} (ha : 1 ≤ a) :
    ‖normalizedTail w a‖ ≤ tailCoefficient w*a^(-w.re/2-1) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hT := _root_.RHTower.norm_cuspTailPart_le_exp ((w-1)/2) 0 (Y := a) (by linarith only [ha])
  have hdecay := exp_decay_le_reciprocal ha0
  rw [normalizedTail,norm_mul,norm_div,Complex.norm_cpow_eq_rpow_re_of_pos ha0,
    show (-w/2).re= -w.re/2 by simp]
  calc
    _ ≤ (a^(-w.re/2)/‖Gammaℝ w‖)*
        (_root_.RHTower.tailConst ((w-1)/2)*Real.exp (-(2*Real.pi*a))) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (a^(-w.re/2)/‖Gammaℝ w‖)*
        (_root_.RHTower.tailConst ((w-1)/2)*(1/(2*Real.pi*a))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdecay (_root_.RHTower.tailConst_nonneg _)) (by positivity)
    _ = _ := by
      rw [tailCoefficient,Real.rpow_sub ha0,Real.rpow_one]
      ring

/-- The large-height bound separates both power tails from the normalized Fourier tail. -/
theorem core_large_bound {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im) {a : ℝ} (ha : 1 ≤ a) :
    ‖fieldCore w a‖ ≤ ‖riemannZeta w‖*a^(-w.re)+‖scatteringCoefficient w‖*a^(-1 : ℝ)+
      tailCoefficient w*a^(-w.re/2-1) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  rw [fieldCore_eq_tail hw him ha0]
  have h := (norm_sub_le (normalizedTail w a-riemannZeta w*(a : ℂ)^(-w))
    (scatteringCoefficient w*(a : ℂ)^(-1 : ℂ))).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ha0,
    Complex.norm_cpow_eq_rpow_re_of_pos ha0,Complex.neg_re] at h
  norm_num only [neg_re,one_re] at h
  linarith only [h,normalizedTail_norm_le (w := w) ha]

#print axioms fieldCore_reciprocity
#print axioms field_eq_constant_scattering_tail
#print axioms fieldCore_eq_tail
#print axioms normalizedTail_norm_le
#print axioms core_large_bound


private theorem inverse_rpow {a : ℝ} (ha : 0 < a) (r : ℝ) : (1/a)^r=a^(-r) := by
  rw [Real.rpow_def_of_pos (one_div_pos.mpr ha),Real.rpow_def_of_pos ha,
    Real.log_div one_ne_zero ha.ne',Real.log_one]
  congr 1
  ring

/-- Reciprocity converts the decaying large-height tails into integrable small-height powers. -/
theorem core_small_bound {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ‖fieldCore w a‖ ≤ ‖riemannZeta w‖+‖scatteringCoefficient w‖*a^(1-w.re)+
      tailCoefficient w*a^(1-w.re/2) := by
  have hi : 1 ≤ 1/a := (le_div_iff₀ ha).mpr (by simpa only [one_mul] using ha1)
  have hlarge := core_large_bound hw him hi
  have h0 : a^(-w.re)*a^w.re=1 := by
    rw [← Real.rpow_add ha,neg_add_cancel,Real.rpow_zero]
  have h1 : a^(-w.re)*a^(1 : ℝ)=a^(1-w.re) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  have h2 : a^(-w.re)*a^(w.re/2+1)=a^(1-w.re/2) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  rw [fieldCore_reciprocity hw him ha,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ha,Complex.neg_re]
  calc
    _ ≤ a^(-w.re)*(‖riemannZeta w‖*(1/a)^(-w.re)+
        ‖scatteringCoefficient w‖*(1/a)^(-1 : ℝ)+tailCoefficient w*(1/a)^(-w.re/2-1)) :=
      mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg ha.le _)
    _ = ‖riemannZeta w‖*(a^(-w.re)*a^w.re)+
        ‖scatteringCoefficient w‖*(a^(-w.re)*a^(1 : ℝ))+tailCoefficient w*(a^(-w.re)*a^(w.re/2+1)) := by
      rw [inverse_rpow ha,inverse_rpow ha,inverse_rpow ha,neg_neg,neg_neg,
        show -(-w.re/2-1)=w.re/2+1 by ring]
      ring
    _ = _ := by rw [h0,h1,h2,mul_one]

private theorem weighted_square {a : ℝ} (ha : 0 < a) (σ p : ℝ) :
    a^(σ-1)*(a^p)^2=a^(σ-1+2*p) := by
  rw [← Real.rpow_natCast (a^p) 2,← Real.rpow_mul ha.le,← Real.rpow_add ha]
  congr 1
  ring

private theorem weighted_square_bound {a : ℝ} (ha : 0 < a) (σ p q r A B C v : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hv : 0 ≤ v)
    (hb : v ≤ A*a^p+B*a^q+C*a^r) :
    a^(σ-1)*v^2 ≤ 3*(A^2*a^(σ-1+2*p)+B^2*a^(σ-1+2*q)+C^2*a^(σ-1+2*r)) := by
  have hsq : v^2 ≤ (A*a^p+B*a^q+C*a^r)^2 :=
    (sq_le_sq₀ hv (by positivity)).mpr hb
  have htri : (A*a^p+B*a^q+C*a^r)^2 ≤ 3*((A*a^p)^2+(B*a^q)^2+(C*a^r)^2) := by
    nlinarith only [sq_nonneg (A*a^p-B*a^q),sq_nonneg (B*a^q-C*a^r),sq_nonneg (C*a^r-A*a^p)]
  calc
    _ ≤ a^(σ-1)*(3*((A*a^p)^2+(B*a^q)^2+(C*a^r)^2)) :=
      mul_le_mul_of_nonneg_left (hsq.trans htri) (Real.rpow_nonneg ha.le _)
    _ = 3*(A^2*(a^(σ-1)*(a^p)^2)+B^2*(a^(σ-1)*(a^q)^2)+C^2*(a^(σ-1)*(a^r)^2)) := by ring
    _ = _ := by rw [weighted_square ha,weighted_square ha,weighted_square ha]

private theorem energy_large_bound {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 1 ≤ a) :
    a^(w.re-1)*‖fieldCore w a‖^2 ≤ 3*(‖riemannZeta w‖^2*a^(-w.re-1)+
      ‖scatteringCoefficient w‖^2*a^(w.re-3)+tailCoefficient w^2*a^(-3 : ℝ)) := by
  have h := weighted_square_bound (lt_of_lt_of_le zero_lt_one ha) w.re (-w.re) (-1)
    (-w.re/2-1) ‖riemannZeta w‖ ‖scatteringCoefficient w‖ (tailCoefficient w) ‖fieldCore w a‖
    (norm_nonneg _) (norm_nonneg _) (tailCoefficient_nonneg w) (norm_nonneg _)
    (core_large_bound hw him ha)
  simpa only [show w.re-1+2*(-w.re)= -w.re-1 by ring,
    show w.re-1+2*(-1)=w.re-3 by ring,show w.re-1+2*(-w.re/2-1)= -3 by ring] using h

private theorem energy_small_bound {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a^(w.re-1)*‖fieldCore w a‖^2 ≤ 3*(‖riemannZeta w‖^2*a^(w.re-1)+
      ‖scatteringCoefficient w‖^2*a^(1-w.re)+tailCoefficient w^2*a) := by
  have hinput : ‖fieldCore w a‖ ≤ ‖riemannZeta w‖*a^(0 : ℝ)+
      ‖scatteringCoefficient w‖*a^(1-w.re)+tailCoefficient w*a^(1-w.re/2) := by
    simpa only [Real.rpow_zero,mul_one] using core_small_bound hw him ha ha1
  have h := weighted_square_bound ha w.re 0 (1-w.re) (1-w.re/2)
    ‖riemannZeta w‖ ‖scatteringCoefficient w‖ (tailCoefficient w) ‖fieldCore w a‖
    (norm_nonneg _) (norm_nonneg _) (tailCoefficient_nonneg w) (norm_nonneg _) hinput
  simpa only [mul_zero,add_zero,show w.re-1+2*(1-w.re)=1-w.re by ring,
    show w.re-1+2*(1-w.re/2)=1 by ring,Real.rpow_one] using h

/-- The actual scattering-subtracted field has finite central-weight square energy
throughout the strip `0<Re w<2`. -/
theorem weighted_energy_integrable {w : ℂ} (hw : 0 < w.re) (hw2 : w.re < 2)
    (him : 0 < w.im) :
    IntegrableOn (fun a : ℝ => a^(w.re-1)*‖fieldCore w a‖^2) (Ioi 0) := by
  have hw0 : w ≠ 0 := by intro he; simp [he] at hw
  have hE := MayerEpsteinHeightMeasurability.measurable_epsteinField hw0 (parameter_ne_two him)
  have hF : Measurable (fieldCore w) := by
    unfold fieldCore scatteringPowers
    fun_prop
  have hm : Measurable (fun a : ℝ => a^(w.re-1)*‖fieldCore w a‖^2) := by fun_prop
  have hs0 : IntegrableOn (fun a : ℝ => a^(w.re-1)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith only [hw]))
  have hs1 : IntegrableOn (fun a : ℝ => a^(1-w.re)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith only [hw2]))
  have hs2 : IntegrableOn (fun a : ℝ => a) (Ioc 0 1) := by
    have h : IntegrableOn (fun a : ℝ => a^(1 : ℝ)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by norm_num))
    simpa only [Real.rpow_one] using h
  have hsmajor : IntegrableOn (fun a : ℝ => 3*(‖riemannZeta w‖^2*a^(w.re-1)+
      ‖scatteringCoefficient w‖^2*a^(1-w.re)+tailCoefficient w^2*a)) (Ioc 0 1) :=
    (((hs0.const_mul _).add (hs1.const_mul _)).add (hs2.const_mul _)).const_mul 3
  have hsmall : IntegrableOn (fun a : ℝ => a^(w.re-1)*‖fieldCore w a‖^2) (Ioc 0 1) := by
    apply hsmajor.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ha.1.le _) (sq_nonneg _))]
    exact energy_small_bound hw him ha.1 ha.2
  have hl0 : IntegrableOn (fun a : ℝ => a^(-w.re-1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith only [hw])
  have hl1 : IntegrableOn (fun a : ℝ => a^(w.re-3)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith only [hw2])
  have hl2 : IntegrableOn (fun a : ℝ => a^(-3 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by norm_num)
  have hlmajor : IntegrableOn (fun a : ℝ => 3*(‖riemannZeta w‖^2*a^(-w.re-1)+
      ‖scatteringCoefficient w‖^2*a^(w.re-3)+tailCoefficient w^2*a^(-3 : ℝ))) (Ioi 1) :=
    (((hl0.const_mul _).add (hl1.const_mul _)).add (hl2.const_mul _)).const_mul 3
  have hlarge : IntegrableOn (fun a : ℝ => a^(w.re-1)*‖fieldCore w a‖^2) (Ioi 1) := by
    apply hlmajor.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have ha0 : 0 < a := zero_lt_one.trans ha
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ha0.le _) (sq_nonneg _))]
    exact energy_large_bound hw him ha.le
  have hu : Ioc (0 : ℝ) 1 ∪ Ioi 1=Ioi 0 := by
    ext a
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h|h)
      · exact h.1
      · exact zero_lt_one.trans h
    · intro ha
      by_cases h : a ≤ 1
      · exact Or.inl ⟨ha,h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hu]
  exact hsmall.union hlarge

#print axioms core_small_bound
#print axioms weighted_energy_integrable

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringCore
