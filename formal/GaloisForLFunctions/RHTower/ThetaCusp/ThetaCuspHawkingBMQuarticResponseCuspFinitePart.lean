import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticCuspFluxDecay

/-!
# Original-source restoration of physical response cusp periods

The complete weighted theta source is split into its original three principal
powers and an absolutely admitted signed source-tail density. Each particular
response coefficient and the native homogeneous coefficient are retained.
Their explicit power antiderivatives agree with the forced endpoint subtraction.
The full physical cusp period then has an exact finite-cutoff restoration and
a source-determined limit, including its actual lower-boundary jet.

No zero value is assigned to that limit. No complete-action cancellation,
clock covariance, extinction or RH is assumed or asserted. All physical
frequencies remain unchanged.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMQuarticResponseCuspFinitePart
open D4BMModularCore D4BMGlobalAngularResponse D4BMJointSource D4BMCuspResponse
open D4BMQuarticResponseMellinTransport D4BMQuarticCuspFluxDecay D4BMCuspProjection
open D4BMAngularSeries D4BMQuadraticMixedSource
noncomputable section
set_option autoImplicit false

/-- Original particular-response coefficient for each of the three source principal powers. -/
def particularCoefficient (q : XiZeroCopy) (b : Bool) (j : Fin 3) : ℂ :=
  parameter q b*principalAmplitude q j/
    (principalExponent q j*(principalExponent q j-1)-parameter q b)

private theorem particular_sum (q : XiZeroCopy) (b : Bool) (y : ℝ) :
    cuspResponse q b ![0,y]=
      ∑ j : Fin 3,particularCoefficient q b j*(y:ℂ)^(principalExponent q j) := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  simp only [cuspResponse,cuspPowerResponse,powerResponse,particularCoefficient,
    principalAmplitude,principalExponent,weylCoefficient,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Matrix.cons_val_succ]
  ring

/-- The physical moment exponents come from the original test and source; all are nonzero. -/
def sourceMomentExponent (q : XiZeroCopy) (i j : Fin 3) : ℂ :=
  physicalWeight q i+principalExponent q j-1

theorem sourceMomentExponent_ne_zero (q : XiZeroCopy) (i j : Fin 3) :
    sourceMomentExponent q i j ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have hn := xi_divisor_support_im_ne_zero q.1
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceMomentExponent,physicalWeight,principalExponent,Complex.add_im,
      Complex.sub_im,Complex.mul_im,Complex.div_im] at hi <;>
    apply hn <;> linarith

private theorem weighted_fluxSource_integrable (q : XiZeroCopy) (b a : Bool)
    (w : ℂ) (Y : Ioi (3:ℝ)) :
    IntegrableOn (fun y : ℝ => (y:ℂ)^w*fluxSource q b a y) (Ioi (Y:ℝ)) := by
  obtain ⟨C,_,hbound⟩ := weighted_fluxSource_norm_bound q b a w
  have hp : 0 < (Y:ℝ) := by have := Y.2; change 3 < (Y:ℝ) at this; linarith
  have hi : IntegrableOn (fun y : ℝ => y^(-2:ℝ)) (Ioi (Y:ℝ)) :=
    (integrableOn_Ioi_rpow_iff hp).mpr (by norm_num)
  have hc : ContinuousOn (fun y : ℝ => (y:ℂ)^w*fluxSource q b a y) (Ioi (Y:ℝ)) := by
    intro y hy
    have hy0 := hp.trans hy
    exact ((GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := w) hy0).continuousAt.mul
      (fluxSource_continuousAt q b a hy0)).continuousWithinAt
  apply (hi.const_mul C).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 := hp.trans hy
  have h := hbound y (Y.2.trans hy)
  simpa only [Real.rpow_neg hy0.le,Real.rpow_two,div_eq_mul_inv] using h

private theorem full_source_mean (q : XiZeroCopy) (y : Ioi (3:ℝ)) :
    sourceMean q y=principalSquare q ![0,y]+
      (1/2:ℂ)*mean (fun x => squareRemainder (center q) ![x,y]) := by
  have hp : 0 < (y:ℝ) := by have := y.2; change 3 < (y:ℝ) at this; linarith
  have hs : Continuous (fun x : ℝ => scalar (center q) ![x,y]) := by
    apply (cuspLeg_contDiffOn .scalar (center q)).continuousOn.comp_continuous
      (by fun_prop) (fun _ => hp)
  have hpconst (x : ℝ) : D4BMGlobalAngularResponse.principal (center q) ![x,y]=
      D4BMGlobalAngularResponse.principal (center q) ![0,y] := rfl
  have hr : Continuous (fun x : ℝ => squareRemainder (center q) ![x,y]) := by
    have hc := (hs.pow 2).sub (continuous_const (y :=
      D4BMGlobalAngularResponse.principal (center q) ![0,y] ^2))
    change Continuous (fun x : ℝ => scalar (center q) ![x,y] ^2-
      D4BMGlobalAngularResponse.principal (center q) ![0,y] ^2) at hc
    simpa only [squareRemainder,hpconst] using hc
  have he (x : ℝ) : fullSquarePotential q ![x,y]=principalSquare q ![0,y]+
      (1/2:ℂ)*squareRemainder (center q) ![x,y] := by
    dsimp only [fullSquarePotential,principalSquare,squareRemainder]
    simp only [hpconst]
    ring
  rw [sourceMean_eq_horizontal]
  simp_rw [he]
  unfold D4BMCuspProjection.mean
  have hc : IntegrableOn (fun _x : ℝ => principalSquare q ![0,y])
      (Ioc (-1/2:ℝ) (1/2)) volume := continuous_const.integrableOn_Ioc
  dsimp only
  rw [integral_add hc (hr.integrableOn_Ioc.const_mul _),integral_const_mul]
  norm_num [Measure.real,Real.volume_Ioc]

/-- The full weighted source splits into its literal principal powers and an admitted flux source. -/
theorem full_source_weighted_split (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    (y : Ioi (3:ℝ)) :
    parameter q b*((y:ℂ)^(physicalWeight q i-2)*sourceMean q y)=
      parameter q b*((y:ℂ)^(physicalWeight q i-2)*principalSquare q ![0,y])+
        (y:ℂ)^(physicalWeight q i-root q b false)*fluxSource q b false y := by
  have hp : 0 < (y:ℝ) := by have := y.2; change 3 < (y:ℝ) at this; linarith
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hf : fluxSource q b false y=(y:ℂ)^(root q b false-2)*
      (parameter q b/2)*mean (fun x => squareRemainder (center q) ![x,y]) := by
    rw [fluxSource,globalForcing_average q b (by have := y.2; change 3 < (y:ℝ) at this; linarith),
      mean_forcing_high q b y.2,mean_squareRemainder (center q) hp]
    ring
  rw [full_source_mean,hf]
  have he : (y:ℂ)^(physicalWeight q i-root q b false)*(y:ℂ)^(root q b false-2)=
      (y:ℂ)^(physicalWeight q i-2) := by
    rw [← Complex.cpow_add _ _ hn]
    congr 1
    ring
  linear_combination -(parameter q b/2)*mean (fun x => squareRemainder (center q) ![x,y])*he


/-- Antiderivative of the complete original principal source at a physical testing weight. -/
def sourceCounterterm (q : XiZeroCopy) (b : Bool) (i : Fin 3) (y : ℝ) : ℂ :=
  ∑ j : Fin 3, (parameter q b*principalAmplitude q j/sourceMomentExponent q i j)*
    (y:ℂ)^(sourceMomentExponent q i j)

private theorem power_primitive (c d : ℂ) (hd : d ≠ 0) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => (c/d)*(t:ℂ)^d) (c*(y:ℂ)^(d-1)) y := by
  simpa only [← mul_assoc,div_mul_cancel₀ _ hd] using
    (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := d) hy).const_mul (c/d)

/-- The subtraction polynomial is forced by the actual three principal source powers. -/
theorem sourceCounterterm_hasDerivAt (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (sourceCounterterm q b i)
      (parameter q b*((y:ℂ)^(physicalWeight q i-2)*principalSquare q ![0,y])) y := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    power_primitive (parameter q b*principalAmplitude q j) (sourceMomentExponent q i j)
      (sourceMomentExponent_ne_zero q i j) hy)
  have he : (∑ j : Fin 3,parameter q b*principalAmplitude q j*
      (y:ℂ)^(sourceMomentExponent q i j-1))=
      parameter q b*((y:ℂ)^(physicalWeight q i-2)*principalSquare q ![0,y]) := by
    rw [principalSquare_expansion q ![0,y] hy,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hp : (y:ℂ)^(sourceMomentExponent q i j-1)=
        (y:ℂ)^(physicalWeight q i-2)*(y:ℂ)^(principalExponent q j) := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
      congr 1
      dsimp only [sourceMomentExponent]
      ring
    rw [hp]
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
    ring
  rw [he] at h
  exact h

private theorem source_principal_interval (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    (a c : Ioi (3:ℝ)) :
    IntervalIntegrable (fun y : ℝ => parameter q b*((y:ℂ)^(physicalWeight q i-2)*
      principalSquare q ![0,y])) volume (a:ℝ) c := by
  have hp (y : ℝ) (hy : y ∈ uIcc (a:ℝ) c) : 0 < y := by
    have ha := a.2; have hc := c.2
    change 3 < (a:ℝ) at ha
    change 3 < (c:ℝ) at hc
    have ha0 : 0 < (a:ℝ) := by linarith
    have hc0 : 0 < (c:ℝ) := by linarith
    exact (lt_min ha0 hc0).trans_le hy.1
  have hq : ContinuousOn (fun y : ℝ => principalSquare q ![0,y]) (uIcc (a:ℝ) c) :=
    (principalSquare_smooth q).continuousOn.comp (by fun_prop) (fun y hy => hp y hy)
  have hw : ContinuousOn (fun y : ℝ => (y:ℂ)^(physicalWeight q i-2)) (uIcc (a:ℝ) c) :=
    fun y hy => (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal
      (w := physicalWeight q i-2) (hp y hy)).continuousAt.continuousWithinAt
  exact ((hw.mul hq).const_mul _).intervalIntegrable

private theorem source_principal_segment (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    (a c : Ioi (3:ℝ)) :
    (∫ y in (a:ℝ)..c, parameter q b*((y:ℂ)^(physicalWeight q i-2)*principalSquare q ![0,y]))=
      sourceCounterterm q b i c-sourceCounterterm q b i a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (source_principal_interval q b i a c)
  intro y hy
  have ha : 0 < (a:ℝ) := by have := a.2; change 3 < (a:ℝ) at this; linarith
  have hc : 0 < (c:ℝ) := by have := c.2; change 3 < (c:ℝ) at this; linarith
  exact sourceCounterterm_hasDerivAt q b i ((lt_min ha hc).trans_le hy.1)

/-- The complete admitted source-tail density at the unchanged physical testing weight. -/
def sourceTailDensity (q : XiZeroCopy) (b : Bool) (i : Fin 3) (y : ℝ) : ℂ :=
  (y:ℂ)^(physicalWeight q i-root q b false)*fluxSource q b false y

/-- The whole source-tail moment is absolutely integrable, independently of RH. -/
theorem sourceTailDensity_integrable (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    (a : Ioi (3:ℝ)) : IntegrableOn (sourceTailDensity q b i) (Ioi (a:ℝ)) :=
  weighted_fluxSource_integrable q b false (physicalWeight q i-root q b false) a

private theorem sourceTailDensity_interval (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    (a c : Ioi (3:ℝ)) : IntervalIntegrable (sourceTailDensity q b i) volume (a:ℝ) c := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have ha : 0 < (a:ℝ) := by have := a.2; change 3 < (a:ℝ) at this; linarith
  have hc : 0 < (c:ℝ) := by have := c.2; change 3 < (c:ℝ) at this; linarith
  have hp := (lt_min ha hc).trans_le hy.1
  exact ((GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal
    (w := physicalWeight q i-root q b false) hp).continuousAt.mul
      (fluxSource_continuousAt q b false hp)).continuousWithinAt

private theorem full_source_segment (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    (a c : Ioi (3:ℝ)) :
    parameter q b*(∫ y in (a:ℝ)..c, (y:ℂ)^(physicalWeight q i-2)*sourceMean q y)=
      sourceCounterterm q b i c-sourceCounterterm q b i a+
        ∫ y in (a:ℝ)..c, sourceTailDensity q b i y := by
  rw [← intervalIntegral.integral_const_mul]
  have he : (∫ y in (a:ℝ)..c, parameter q b*((y:ℂ)^(physicalWeight q i-2)*sourceMean q y))=
      ∫ y in (a:ℝ)..c, (parameter q b*((y:ℂ)^(physicalWeight q i-2)*principalSquare q ![0,y])+
        sourceTailDensity q b i y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hp : 3 < y := (lt_min a.2 c.2).trans_le hy.1
    exact full_source_weighted_split q b i ⟨y,hp⟩
  rw [he,intervalIntegral.integral_add (source_principal_interval q b i a c)
    (sourceTailDensity_interval q b i a c),source_principal_segment]

/-- Original-source forced subtraction, retaining the particular and native endpoint data. -/
def responseCounterterm (q : XiZeroCopy) (b : Bool) (i : Fin 3) (y : ℝ) : ℂ :=
  (particularPhysicalFlux q b i y+nativePhysicalFlux q b i y-sourceCounterterm q b i y)/
    physicalGap q b i


private theorem particularCoefficient_equation (q : XiZeroCopy) (b : Bool) (j : Fin 3) :
    (principalExponent q j*(principalExponent q j-1)-parameter q b)*particularCoefficient q b j=
      parameter q b*principalAmplitude q j := by
  have h := xi_cusp_denominators q b
  have hd : principalExponent q j*(principalExponent q j-1)-parameter q b ≠ 0 := by
    fin_cases j
    · exact h.1
    · change (1:ℂ)*(1-1)-parameter q b ≠ 0
      simpa only [sub_self,mul_zero,zero_sub,parameter] using h.2.1
    · change (2-2*(q.1:ℂ))*((2-2*(q.1:ℂ))-1)-parameter q b ≠ 0
      convert h.2.2 using 1
      dsimp only [parameter]
      ring
  dsimp only [particularCoefficient]
  field_simp [hd]

private theorem particular_deriv (q : XiZeroCopy) (b : Bool) {y : ℝ} (hy : 0 < y) :
    deriv (fun t : ℝ => cuspResponse q b ![0,t]) y=
      ∑ j : Fin 3, particularCoefficient q b j*(principalExponent q j*(y:ℂ)^(principalExponent q j-1)) := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal
      (w := principalExponent q j) hy).const_mul (particularCoefficient q b j))
  have he : (fun t : ℝ => cuspResponse q b ![0,t])=
      (fun t : ℝ => ∑ j : Fin 3,particularCoefficient q b j*(t:ℂ)^(principalExponent q j)) :=
    funext (particular_sum q b)
  rw [he]
  exact h.deriv

private theorem particular_flux_sum (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    {y : ℝ} (hy : 0 < y) :
    particularPhysicalFlux q b i y=∑ j : Fin 3,particularCoefficient q b j*
      (principalExponent q j-physicalWeight q i)*(y:ℂ)^(sourceMomentExponent q i j) := by
  rw [particularPhysicalFlux,particular_deriv q b hy,particular_sum]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have h0 : (y:ℂ)^(physicalWeight q i)*(y:ℂ)^(principalExponent q j-1)=
      (y:ℂ)^(sourceMomentExponent q i j) := by
    rw [← Complex.cpow_add _ _ hn]
    congr 1
    dsimp only [sourceMomentExponent]
    ring
  have h1 : (y:ℂ)^(physicalWeight q i-1)*(y:ℂ)^(principalExponent q j)=
      (y:ℂ)^(sourceMomentExponent q i j) := by
    rw [← Complex.cpow_add _ _ hn]
    congr 1
    dsimp only [sourceMomentExponent]
    ring
  linear_combination particularCoefficient q b j*principalExponent q j*h0-
    physicalWeight q i*particularCoefficient q b j*h1

private theorem particular_counterterm_balance (q : XiZeroCopy) (b : Bool) (i j : Fin 3) :
    physicalGap q b i*(particularCoefficient q b j/sourceMomentExponent q i j)=
      particularCoefficient q b j*(principalExponent q j-physicalWeight q i)-
        parameter q b*principalAmplitude q j/sourceMomentExponent q i j := by
  apply (eq_sub_iff_add_eq).mpr
  rw [← mul_div_assoc,← add_div]
  apply (div_eq_iff (sourceMomentExponent_ne_zero q i j)).mpr
  have h := particularCoefficient_equation q b j
  dsimp only [physicalGap,sourceMomentExponent]
  linear_combination -h

private theorem physical_gap_factor (q : XiZeroCopy) (b : Bool) (i : Fin 3) :
    physicalGap q b i=(root q b false-physicalWeight q i)*(physicalWeight q i-root q b true) := by
  cases b <;> simp only [physicalGap,root,D4BMCuspProjection.physicalRate,parameter,
    branchParameter,resolventParameter,Bool.false_eq_true,if_false,if_true] <;> ring

private theorem native_exponent_ne_zero (q : XiZeroCopy) (b : Bool) (i : Fin 3) :
    physicalWeight q i-root q b true ≠ 0 := by
  intro h
  apply physicalGap_ne_zero q b i
  rw [physical_gap_factor,h,mul_zero]

/-- The forced subtraction is exactly the antiderivative of the original particular powers
and native homogeneous power; it has no added constant or altered physical frequency. -/
theorem responseCounterterm_power_expansion (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    {y : ℝ} (hy : 0 < y) :
    responseCounterterm q b i y=
      (∑ j : Fin 3,particularCoefficient q b j/sourceMomentExponent q i j*
        (y:ℂ)^(sourceMomentExponent q i j))+
      limitingCoefficient q b false/(physicalWeight q i-root q b true)*
        (y:ℂ)^(physicalWeight q i-root q b true) := by
  apply (div_eq_iff (physicalGap_ne_zero q b i)).mpr
  have hn : nativePhysicalFlux q b i y=
      physicalGap q b i*(limitingCoefficient q b false/(physicalWeight q i-root q b true)*
        (y:ℂ)^(physicalWeight q i-root q b true)) := by
    rw [physical_gap_factor,nativePhysicalFlux]
    field_simp [native_exponent_ne_zero q b i]
  rw [particular_flux_sum q b i hy,sourceCounterterm,hn]
  have hs : (∑ j : Fin 3,particularCoefficient q b j*(principalExponent q j-physicalWeight q i)*
      (y:ℂ)^(sourceMomentExponent q i j))-
      (∑ j : Fin 3,parameter q b*principalAmplitude q j/sourceMomentExponent q i j*
        (y:ℂ)^(sourceMomentExponent q i j))=
      physicalGap q b i*(∑ j : Fin 3,particularCoefficient q b j/sourceMomentExponent q i j*
        (y:ℂ)^(sourceMomentExponent q i j)) := by
    rw [← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    linear_combination -(y:ℂ)^(sourceMomentExponent q i j)*particular_counterterm_balance q b i j
  linear_combination hs

/-- The value of the restored cusp moment in terms of the actual lower boundary and complete source. -/
def sourceDeterminedPeriod (q : XiZeroCopy) (b : Bool) (i : Fin 3) (a : Ioi (3:ℝ)) : ℂ :=
  (-physicalFlux q b i a+sourceCounterterm q b i a-
    ∫ y in Ioi (a:ℝ), sourceTailDensity q b i y)/physicalGap q b i

/-- Exact finite-cutoff restoration keeps every source and boundary term. -/
theorem response_period_restoration (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    (a c : Ioi (3:ℝ)) :
    (∫ y in (a:ℝ)..c, (y:ℂ)^(physicalWeight q i-2)*fullMean q b y)-responseCounterterm q b i c =
      (physicalFlux q b i c-particularPhysicalFlux q b i c-nativePhysicalFlux q b i c-
        physicalFlux q b i a+sourceCounterterm q b i a-
        ∫ y in (a:ℝ)..c, sourceTailDensity q b i y)/physicalGap q b i := by
  have ha : 0 < (a:ℝ) := by have := a.2; change 3 < (a:ℝ) at this; linarith
  have hc : 0 < (c:ℝ) := by have := c.2; change 3 < (c:ℝ) at this; linarith
  rw [physical_response_segment q b i ⟨a,ha⟩ ⟨c,hc⟩,full_source_segment q b i a c]
  dsimp only [responseCounterterm]
  ring

/-- The actual full-response cusp period has the source-determined finite part at every physical weight. -/
theorem response_period_tendsto (q : XiZeroCopy) (b : Bool) (i : Fin 3) (a : Ioi (3:ℝ)) :
    Tendsto (fun c : ℝ => (∫ y in (a:ℝ)..c, (y:ℂ)^(physicalWeight q i-2)*fullMean q b y)-
      responseCounterterm q b i c) atTop (𝓝 (sourceDeterminedPeriod q b i a)) := by
  have hF := intervalIntegral_tendsto_integral_Ioi (a:ℝ)
    (sourceTailDensity_integrable q b i a) tendsto_id
  have hJ := physicalFlux_remainder_tendsto_zero q b i
  have ht := (((hJ.sub_const (physicalFlux q b i a)).add_const (sourceCounterterm q b i a)).sub hF).div_const (physicalGap q b i)
  simp only [zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (3:ℝ)] with c hc
  exact (response_period_restoration q b i a ⟨c,hc⟩).symm

end
end RHTower.D4BMQuarticResponseCuspFinitePart
