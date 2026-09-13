import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedNativeReaderFlux

/-!
The actual mixed-current cusp face against an independent original left-QNM reader.
The full particular response and squared-source contact give three explicit powers;
the integrated remainder retains every Fourier tail and decays at every fixed
complex height weight. Native-flux decay then identifies the original source flux.

The cross power is branch-independent before radial weighting. Only two explicit
independent-source resonances can contribute a constant height power, and neither
occurs on the diagonal. These are angular cusp statements, not a vanishing theorem
for the complete causal action or a change of the common Hawking clock.
-/

open scoped ContDiff BigOperators
open MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open GaloisForLFunctions.RHTower.SelbergMaassMean
open GaloisForLFunctions.RHTower.SelbergMaassFourier
open GaloisForLFunctions.RHTower.SelbergMaassParseval
namespace RHTower.D4BMMixedParticularCuspFlux
open D4BMModularCore D4BMGlobalAngularResponse D4BMJointSource
open D4BMQuarticTestedNativeCurrent D4BMMixedNativeReaderFlux
open D4BMQuadraticMixedSource
noncomputable section
set_option autoImplicit false

private def cell : Set ℝ := Ioc 0 1
private def cellMean (f : ℝ → ℂ) : ℂ := ∫ x in cell, f x

private theorem coefficient_zero_integral (F : ℂ → ℂ) (y : ℝ) :
    coefficient 1 0 F y=cellMean (fun x => F (point x y)) := by
  simp only [coefficient,deningerFourierCoeff,deningerFourierKernel,Int.cast_zero,
    mul_zero,zero_mul,neg_zero,Complex.exp_zero,Complex.ofReal_one,div_one,one_mul]
  change (∫ x in (0:ℝ)..1, F (point x y))=∫ x in Ioc (0:ℝ) 1, F (point x y)
  exact intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)

private theorem physicalTest_smooth (q : XiZeroCopy) :
    ContDiffOn ℝ ∞ (physicalTest q) {z : ℂ | 0 < z.im} := by
  intro z hz
  have h := (D4BMAngularSeries.cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds
      (show 0 < angularCoordinates z 1 from hz))
  exact (h.comp z angularCoordinates.contDiff.contDiffAt).contDiffWithinAt

private theorem physicalTest_periodic (q : XiZeroCopy) (y x : ℝ) :
    physicalTest q (point (x+1) y)=physicalTest q (point x y) := by
  have hp : Function.Periodic (scalar (physicalAngularParameter q)) ![1,0] := by
    intro z
    simpa [scalar,Pi.add_apply] using d4BM_completedEisensteinCuspLeg_scalar_periodic
      (physicalAngularParameter q) (z 1) (z 0)
  have hc : angularCoordinates (point (x+1) y)=angularCoordinates (point x y)+![1,0] := by
    ext i
    fin_cases i <;> norm_num [angularCoordinates,point,Pi.add_apply]
  exact (congrArg (scalar (physicalAngularParameter q)) hc).trans (hp _)

private theorem coefficient_zero_cusp_mean (F : ℂ → ℂ) (y : ℝ)
    (hp : ∀ x : ℝ, F (point (x+1) y)=F (point x y)) :
    coefficient 1 0 F y=D4BMCuspResponse.average F y := by
  rw [coefficient_zero_integral]
  change (∫ x in Ioc (0:ℝ) 1, F (point x y))=
    ∫ x in Ioc (-1/2:ℝ) (1/2), F (point x y)
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ← intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2)]
  have hper : Function.Periodic (fun x : ℝ => F (point x y)) 1 := hp
  simpa only [zero_add,show (-1/2:ℝ)+1=1/2 by ring] using hper.intervalIntegral_add_eq 0 (-1/2)

private theorem reader_mean (r : XiZeroCopy) (y : Ioi (0:ℝ)) :
    coefficient 1 0 (physicalTest r) y =
      reflectedCompletedLambda ((r.1:ℂ)-1)*(y.val:ℂ)^(1-(r.1:ℂ)/2) := by
  rw [coefficient_zero_cusp_mean _ y (physicalTest_periodic r y)]
  let u := physicalAngularParameter r
  have he (x : ℝ) : physicalTest r (point x y)=principal u ![0,y.val]+tail u ![x,y.val] := by
    simp [physicalTest,scalar,D4BMGlobalAngularResponse.principal,tail,d4BMCompletedEisensteinCuspLeg,
      angularCoordinates,point,u]
  have ht : Continuous (fun x : ℝ => tail u ![x,y.val]) := by
    have hh : (fun x : ℝ => tail u ![x,y.val])=
        fun x => physicalTest r (point x y)-principal u ![0,y.val] := by
      funext x
      rw [he]
      ring
    rw [hh]
    exact (GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous
      (physicalTest_smooth r).continuousOn y.2).sub continuous_const
  change (∫ x in Ioc (-1/2:ℝ) (1/2), physicalTest r (point x y))=_
  simp_rw [he]
  rw [integral_add (integrable_const _) ht.integrableOn_Ioc]
  have hm := D4BMCuspProjection.mean_tail u y.2
  change (∫ x in Ioc (-1/2:ℝ) (1/2), tail u ![x,y.val])=0 at hm
  rw [hm,add_zero]
  norm_num
  exact physicalScalar_principal r ![0,y.val]

private theorem reader_derivative_mean (r : XiZeroCopy) (y : Ioi (0:ℝ)) :
    coefficient 1 0 (directional Complex.I (physicalTest r)) y=
      reflectedCompletedLambda ((r.1:ℂ)-1)*(1-(r.1:ℂ)/2)*(y.val:ℂ)^(-(r.1:ℂ)/2) := by
  have h := coefficient_hasDerivAt 1 (by norm_num) 0
    ((physicalTest_smooth r).of_le (WithTop.coe_le_coe.mpr le_top)) y.2
  have hm : HasDerivAt (fun t : ℝ => reflectedCompletedLambda ((r.1:ℂ)-1)*(t:ℂ)^(1-(r.1:ℂ)/2))
      (coefficient 1 0 (directional Complex.I (physicalTest r)) y) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    exact (reader_mean r ⟨t,ht⟩).symm
  have hp := (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := 1-(r.1:ℂ)/2) y.2).const_mul
    (reflectedCompletedLambda ((r.1:ℂ)-1))
  have he : 1-(r.1:ℂ)/2-1=-(r.1:ℂ)/2 := by ring
  rw [he] at hp
  simpa only [mul_assoc] using hm.unique hp


/-- The two literal squared-source Weyl coefficients, before choosing a response branch. -/
def weylCoefficient (q : XiZeroCopy) (e : Bool) : ℂ :=
  d4BMCompletedEisensteinCuspConstantCoefficient (center q) e

/-- All three powers of the literal principal square, including its cross term. -/
def sourcePower (q : XiZeroCopy) (i : Fin 3) : ℂ :=
  ![2*(q.1:ℂ),1,2-2*(q.1:ℂ)] i

def sourceCoefficient (q : XiZeroCopy) (i : Fin 3) : ℂ :=
  ![weylCoefficient q true^2,2*weylCoefficient q true*weylCoefficient q false,
    weylCoefficient q false^2] i

def readerPower (r : XiZeroCopy) : ℂ := 1-(r.1:ℂ)/2

def readerCoefficient (r : XiZeroCopy) : ℂ := reflectedCompletedLambda ((r.1:ℂ)-1)

def denominator (q : XiZeroCopy) (b : Bool) (i : Fin 3) : ℂ :=
  sourcePower q i*(sourcePower q i-1)-parameter q b

def responseCoefficient (q : XiZeroCopy) (b : Bool) (i : Fin 3) : ℂ :=
  (parameter q b/2)*sourceCoefficient q i/denominator q b i

/-- Original Xi source equations exclude resonance in every particular-response denominator. -/
theorem denominator_ne_zero (q : XiZeroCopy) (b : Bool) (i : Fin 3) :
    denominator q b i ≠ 0 := by
  obtain ⟨h0,h1,h2⟩ := xi_cusp_denominators q b
  fin_cases i
  · simpa [denominator,sourcePower,parameter] using h0
  · simpa [denominator,sourcePower,parameter] using h1
  · simpa [denominator,sourcePower,parameter,
      show 2-2*(q.1:ℂ)-1=1-2*(q.1:ℂ) by ring] using h2

private theorem principal_center (q : XiZeroCopy) (y : ℝ) :
    D4BMGlobalAngularResponse.principal (center q) ![0,y]=
      weylCoefficient q true*(y:ℂ)^(q.1:ℂ)+
        weylCoefficient q false*(y:ℂ)^(1-(q.1:ℂ)) := by
  have hm : d4BMCompletedEisensteinCuspWeylExponent (center q) false=1-(q.1:ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,D4BMGlobalAngularResponse.center]
    ring
  have hp : d4BMCompletedEisensteinCuspWeylExponent (center q) true=(q.1:ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,D4BMGlobalAngularResponse.center]
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,
    mul_one,hm,hp,Matrix.cons_val_one,Matrix.cons_val_zero,weylCoefficient]
  ring

/-- Exact three-power identity for the original principal square. -/
theorem principal_square (q : XiZeroCopy) (y : Ioi (0:ℝ)) :
    D4BMGlobalAngularResponse.principal (center q) ![0,y.val] ^2=
      ∑ i : Fin 3, sourceCoefficient q i*(y.val:ℂ)^(sourcePower q i) := by
  rw [principal_center]
  simpa [Fin.sum_univ_three,sourceCoefficient,sourcePower] using
    (cusp_power_square (q.1:ℂ) (weylCoefficient q true) (weylCoefficient q false) ![0,y.val] y.2).symm

/-- The displayed three powers are the actual original particular response. -/
theorem cuspResponse_eq_sum (q : XiZeroCopy) (b : Bool) (y : ℝ) :
    cuspResponse q b ![0,y]=∑ i : Fin 3, responseCoefficient q b i*(y:ℂ)^(sourcePower q i) := by
  simp [cuspResponse,cuspPowerResponse,powerResponse,Fin.sum_univ_three,
    responseCoefficient,sourceCoefficient,sourcePower,denominator,weylCoefficient,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- The derivative is taken from the actual particular response, with all denominators retained. -/
theorem cuspResponse_derivative_eq_sum (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    deriv (fun t : ℝ => cuspResponse q b ![0,t]) y=
      ∑ i : Fin 3, responseCoefficient q b i*(sourcePower q i*(y.val:ℂ)^(sourcePower q i-1)) := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := sourcePower q i) y.2).const_mul
      (responseCoefficient q b i))
  have he : HasDerivAt (fun t : ℝ => cuspResponse q b ![0,t])
      (∑ i : Fin 3, responseCoefficient q b i*(sourcePower q i*(y.val:ℂ)^(sourcePower q i-1))) y := by
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (cuspResponse_eq_sum q b)
  exact he.deriv

def fluxExponent (q r : XiZeroCopy) (i : Fin 3) : ℂ := sourcePower q i-(r.1:ℂ)/2

/-- Actual coefficient supplied by the particular response and full square-source contact. -/
def fluxCoefficient (q r : XiZeroCopy) (b : Bool) (i : Fin 3) : ℂ :=
  (parameter q b/2)*sourceCoefficient q i*readerCoefficient r*sourcePower q i*
    readerPower r*(readerPower r-sourcePower q i)/denominator q b i

def powerFlux (q r : XiZeroCopy) (b : Bool) (y : ℝ) : ℂ :=
  ∑ i : Fin 3, fluxCoefficient q r b i*(y:ℂ)^(fluxExponent q r i)

private theorem reader_eigenvalue (r : XiZeroCopy) :
    physicalAngularParameter r^2-1/4=readerPower r*(readerPower r-1) := by
  rw [physicalAngularParameter_eq]
  unfold readerPower
  ring

/-- The source-derived coefficient identity keeps the complete resolvent denominator. -/
theorem fluxCoefficient_identity (q r : XiZeroCopy) (b : Bool) (i : Fin 3) :
    (physicalAngularParameter r^2-1/4)*readerCoefficient r*responseCoefficient q b i*sourcePower q i-
      parameter q b*(responseCoefficient q b i+sourceCoefficient q i/2)*readerCoefficient r*readerPower r=
        fluxCoefficient q r b i := by
  rw [reader_eigenvalue]
  dsimp only [responseCoefficient,fluxCoefficient]
  field_simp [denominator_ne_zero q b i]
  unfold denominator
  ring

/-- The literal mixed Weyl power carries the same coefficient on both physical source branches. -/
theorem fluxCoefficient_cross (q r : XiZeroCopy) (b : Bool) :
    fluxCoefficient q r b 1 =
      -weylCoefficient q true*weylCoefficient q false*readerCoefficient r*(physicalAngularParameter r^2-1/4) := by
  have hm : parameter q b ≠ 0 := by
    have h := denominator_ne_zero q b 1
    simpa [denominator,sourcePower] using h
  rw [reader_eigenvalue]
  simp only [fluxCoefficient,sourcePower,sourceCoefficient,denominator,
    Matrix.cons_val_one,Matrix.cons_val_zero,sub_self,mul_zero,zero_sub,mul_one,div_neg]
  field_simp [hm]

private theorem directional_smooth {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) (v : ℂ) :
    ContDiffOn ℝ ∞ (directional v F) {z : ℂ | 0 < z.im} :=
  planar_derivative_contDiffOn hf v

private theorem vertical_periodic {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hp : ∀ y : ℝ, 0 < y → ∀ x : ℝ, F (point (x+1) y)=F (point x y))
    (y : Ioi (0:ℝ)) (x : ℝ) :
    directional Complex.I F (point (x+1) y)=directional Complex.I F (point x y) := by
  have hf1 := hf.of_le (show (1 : WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have h := GaloisForLFunctions.RHTower.SelbergMaassMean.slice_vertical hf1 (x+1) y.2
  have hh : HasDerivAt (fun t => F (point x t)) (directional Complex.I F (point (x+1) y)) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    exact (hp t ht x).symm
  exact hh.unique (GaloisForLFunctions.RHTower.SelbergMaassMean.slice_vertical hf1 x y.2)

private theorem scalar_slice (q : XiZeroCopy) (y : Ioi (0:ℝ)) :
    Continuous (fun x : ℝ => scalar (center q) ![x,y.val]) := by
  have he : (fun x : ℝ => scalar (center q) ![x,y.val])=
      fun x => principal (center q) ![0,y.val]+2*D4BMCuspProjection.series
        (D4BMCuspProjection.amplitude (center q) y) x := by
    funext x
    rw [← D4BMCuspProjection.tail_eq_series (center q) y.2 x]
    rfl
  rw [he]
  exact continuous_const.add (continuous_const.mul (D4BMCuspProjection.series_continuous _
    (D4BMCuspProjection.amplitude_norm_summable (center q) y.2)))

/-- Every nonconstant squared-source term paired with the full original reader derivative. -/
def forcingTail (q r : XiZeroCopy) (y : ℝ) : ℂ :=
  ∫ x in Ioc (-1/2:ℝ) (1/2), squareRemainder (center q) ![x,y]*
    directional Complex.I (physicalTest r) (point x y)

private theorem remainder_slice (q : XiZeroCopy) (y : Ioi (0:ℝ)) :
    Continuous (fun x : ℝ => squareRemainder (center q) ![x,y.val]) := by
  change Continuous (fun x : ℝ => scalar (center q) ![x,y.val] ^2-principal (center q) ![0,y.val] ^2)
  exact ((scalar_slice q y).pow 2).sub continuous_const

private theorem particularGreenFlux_means (q r : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    particularGreenFlux q r b y=
      (physicalAngularParameter r^2-1/4)*(readerCoefficient r*(y.val:ℂ)^(readerPower r))*
        deriv (fun t : ℝ => cuspResponse q b ![0,t]) y-
      parameter q b*(cuspResponse q b ![0,y.val]+principal (center q) ![0,y.val] ^2/2)*
        (readerCoefficient r*readerPower r*(y.val:ℂ)^(readerPower r-1))-
      (parameter q b/2)*forcingTail q r y := by
  have hR : (∫ x in Ioc (-1/2:ℝ) (1/2), physicalTest r (point x y))=
      readerCoefficient r*(y.val:ℂ)^(readerPower r) := by
    change D4BMCuspResponse.average (physicalTest r) y=_
    rw [← coefficient_zero_cusp_mean _ y (physicalTest_periodic r y)]
    exact reader_mean r y
  have hRv : (∫ x in Ioc (-1/2:ℝ) (1/2), directional Complex.I (physicalTest r) (point x y))=
      readerCoefficient r*readerPower r*(y.val:ℂ)^(readerPower r-1) := by
    change D4BMCuspResponse.average (directional Complex.I (physicalTest r)) y=_
    rw [← coefficient_zero_cusp_mean _ y (vertical_periodic (physicalTest_smooth r)
      (fun t _ => physicalTest_periodic r t) y),reader_derivative_mean]
    dsimp only [readerCoefficient,readerPower]
    congr 2
    ring
  have cR := GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous
    (physicalTest_smooth r).continuousOn y.2
  have cRv := GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous
    (directional_smooth (physicalTest_smooth r) Complex.I).continuousOn y.2
  let A : ℝ → ℂ := fun x => (physicalAngularParameter r^2-1/4)*physicalTest r (point x y)*
    deriv (fun t : ℝ => cuspResponse q b ![0,t]) y
  let B : ℝ → ℂ := fun x => parameter q b*
    (cuspResponse q b ![0,y.val]+principal (center q) ![0,y.val] ^2/2)*
    directional Complex.I (physicalTest r) (point x y)
  let T : ℝ → ℂ := fun x => (parameter q b/2)*
    (squareRemainder (center q) ![x,y.val]*directional Complex.I (physicalTest r) (point x y))
  have cA : Continuous A := (cR.const_mul _).mul_const _
  have cB : Continuous B := cRv.const_mul _
  have cT : Continuous T := ((remainder_slice q y).mul cRv).const_mul _
  have he : particularGreenFlux q r b y=∫ x in Ioc (-1/2:ℝ) (1/2), (A x-B x)-T x := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    dsimp only [A,B,T,squareRemainder]
    change (physicalAngularParameter r^2-1/4)*physicalTest r (point x y)*
      deriv (fun t : ℝ => cuspResponse q b ![0,t]) y-
      parameter q b*(cuspResponse q b ![0,y.val]+scalar (center q) ![x,y.val] ^2/2)*
        directional Complex.I (physicalTest r) (point x y)=_
    have hp : principal (center q) ![x,y.val]=principal (center q) ![0,y.val] := rfl
    rw [hp]
    ring
  have hAB := integral_sub (μ := volume.restrict (Ioc (-1/2:ℝ) (1/2)))
    cA.integrableOn_Ioc cB.integrableOn_Ioc
  have hABT := integral_sub (μ := volume.restrict (Ioc (-1/2:ℝ) (1/2)))
    (cA.sub cB).integrableOn_Ioc cT.integrableOn_Ioc
  simp only [Pi.sub_apply] at hABT
  rw [he,hABT,hAB]
  dsimp only [A,B,T]
  rw [integral_mul_const,integral_const_mul,integral_const_mul,integral_const_mul,hR,hRv]
  rfl

private theorem individual_power (q r : XiZeroCopy) (b : Bool) (i : Fin 3) (y : Ioi (0:ℝ)) :
    (physicalAngularParameter r^2-1/4)*(readerCoefficient r*(y.val:ℂ)^(readerPower r))*
      (responseCoefficient q b i*(sourcePower q i*(y.val:ℂ)^(sourcePower q i-1)))-
    parameter q b*(responseCoefficient q b i*(y.val:ℂ)^(sourcePower q i)+
      sourceCoefficient q i*(y.val:ℂ)^(sourcePower q i)/2)*
      (readerCoefficient r*readerPower r*(y.val:ℂ)^(readerPower r-1))=
    fluxCoefficient q r b i*(y.val:ℂ)^(fluxExponent q r i) := by
  have hy : (y.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt y.2)
  have h1 : (y.val:ℂ)^(readerPower r)*(y.val:ℂ)^(sourcePower q i-1)=
      (y.val:ℂ)^(fluxExponent q r i) := by
    rw [← Complex.cpow_add _ _ hy]
    congr 1
    dsimp only [readerPower,fluxExponent]
    ring
  have h2 : (y.val:ℂ)^(sourcePower q i)*(y.val:ℂ)^(readerPower r-1)=
      (y.val:ℂ)^(fluxExponent q r i) := by
    rw [← Complex.cpow_add _ _ hy]
    congr 1
    dsimp only [readerPower,fluxExponent]
    ring
  calc
    _ = ((physicalAngularParameter r^2-1/4)*readerCoefficient r*responseCoefficient q b i*sourcePower q i)*
          ((y.val:ℂ)^(readerPower r)*(y.val:ℂ)^(sourcePower q i-1))-
        (parameter q b*(responseCoefficient q b i+sourceCoefficient q i/2)*readerCoefficient r*readerPower r)*
          ((y.val:ℂ)^(sourcePower q i)*(y.val:ℂ)^(readerPower r-1)) := by ring
    _ = _ := by rw [h1,h2,← sub_mul,fluxCoefficient_identity]

/-- Exact evaluation of the actual forced cusp flux; all Fourier remainders are retained. -/
theorem particularGreenFlux_eq (q r : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    particularGreenFlux q r b y=powerFlux q r b y-(parameter q b/2)*forcingTail q r y := by
  rw [particularGreenFlux_means,cuspResponse_derivative_eq_sum,cuspResponse_eq_sum,principal_square]
  congr 1
  simp only [Finset.mul_sum,Finset.sum_div,← Finset.sum_add_distrib,Finset.sum_mul,
    ← Finset.sum_sub_distrib,powerFlux]
  exact Finset.sum_congr rfl (fun i _ => individual_power q r b i y)

/-- The full integrated Fourier remainder admits every fixed complex height weight. -/
theorem forcingTail_weighted_bound (q r : XiZeroCopy) (w : ℂ) :
    ∃ C : ℝ, 0≤C ∧ ∀ y : Ioi (3:ℝ), ‖(y.val:ℂ)^w*forcingTail q r y‖≤C := by
  obtain ⟨A,hA,ha⟩ := weighted_squareRemainder_bounded (center q) w 3 (by norm_num)
  obtain ⟨B,hB,hb⟩ := physicalTest_firstJet_bound r
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro y
  rw [forcingTail,← integral_const_mul]
  have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (-1/2:ℝ) (1/2)))
    (f := fun x : ℝ => (y.val:ℂ)^w*(squareRemainder (center q) ![x,y.val]*
      directional Complex.I (physicalTest r) (point x y))) (C := A*B) (Filter.Eventually.of_forall (fun x => by
        rw [← mul_assoc,norm_mul]
        exact mul_le_mul (ha ![x,y.val] y.2.le) (hb y x).2.1 (norm_nonneg _) hA))
  norm_num at hi ⊢
  exact hi

/-- Every weighted integrated Fourier remainder tends to zero; no reader tail was discarded. -/
theorem forcingTail_weighted_tendsto_zero (q r : XiZeroCopy) (w : ℂ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*forcingTail q r y) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := forcingTail_weighted_bound q r (w+1)
  have hlimit : Tendsto (fun y : ℝ => C/y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul C
  apply squeeze_zero_norm'
    (show ∀ᶠ y : ℝ in atTop, ‖(y:ℂ)^w*forcingTail q r y‖≤C/y from ?_) hlimit
  filter_upwards [eventually_gt_atTop (3:ℝ)] with y hy
  have hy0 : 0<y := lt_trans (by norm_num : (0:ℝ)<3) hy
  have hyn : (y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy0)
  have he : (y:ℂ)^w*forcingTail q r y=((y:ℂ)^(w+1)*forcingTail q r y)/(y:ℂ) := by
    rw [Complex.cpow_add _ _ hyn,Complex.cpow_one]
    field_simp
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy0]
  exact div_le_div_of_nonneg_right (hbound ⟨y,hy⟩) hy0.le

/-- The three source-derived powers exhaust the actual mixed-current upper cusp flux. -/
theorem sourceGreenFlux_sub_powerFlux_tendsto_zero (q r : XiZeroCopy) (b : Bool) :
    Tendsto (fun y : ℝ => sourceGreenFlux q r b y-powerFlux q r b y) atTop (𝓝 0) := by
  have ht : Tendsto (forcingTail q r) atTop (𝓝 0) := by
    simpa only [Complex.cpow_zero,one_mul] using forcingTail_weighted_tendsto_zero q r 0
  have h := (sourceGreenFlux_sub_particular_tendsto_zero q r b).sub (ht.const_mul (parameter q b/2))
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [particularGreenFlux_eq q r b ⟨y,hy⟩]
  ring

/-- The cross Weyl coefficient cancels between branches before radial weighting. -/
theorem powerFlux_branch_difference (q r : XiZeroCopy) (y : ℝ) :
    powerFlux q r true y-powerFlux q r false y=
      (fluxCoefficient q r true 0-fluxCoefficient q r false 0)*(y:ℂ)^(fluxExponent q r 0)+
      (fluxCoefficient q r true 2-fluxCoefficient q r false 2)*(y:ℂ)^(fluxExponent q r 2) := by
  simp only [powerFlux,Fin.sum_univ_three,fluxCoefficient_cross]
  ring


/-- Unweighted branch subtraction removes the cross power in the actual upper flux. -/
theorem sourceGreenFlux_branch_difference (q r : XiZeroCopy) :
    Tendsto (fun y : ℝ => (sourceGreenFlux q r true y-sourceGreenFlux q r false y)-
      ((fluxCoefficient q r true 0-fluxCoefficient q r false 0)*(y:ℂ)^(fluxExponent q r 0)+
       (fluxCoefficient q r true 2-fluxCoefficient q r false 2)*(y:ℂ)^(fluxExponent q r 2)))
      atTop (𝓝 0) := by
  have h := (sourceGreenFlux_sub_powerFlux_tendsto_zero q r true).sub
    (sourceGreenFlux_sub_powerFlux_tendsto_zero q r false)
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [] with y
  rw [← powerFlux_branch_difference]
  ring

/-- Only the two squared-Weyl resonance loci can supply a constant height power. -/
theorem fluxExponent_zero_iff (q r : XiZeroCopy) (i : Fin 3) :
    fluxExponent q r i=0 ↔
      (i=0 ∧ (r.1:ℂ)=4*(q.1:ℂ)) ∨ (i=2 ∧ (r.1:ℂ)=4-4*(q.1:ℂ)) := by
  have h0 : fluxExponent q r 0=0 ↔ (r.1:ℂ)=4*(q.1:ℂ) := by
    change 2*(q.1:ℂ)-(r.1:ℂ)/2=0 ↔ _
    constructor
    · intro h; linear_combination -2*h
    · intro h; linear_combination -(1/2:ℂ)*h
  have h1 : fluxExponent q r 1≠0 := by
    change 1-(r.1:ℂ)/2≠0
    intro h
    have hi := congrArg Complex.im h
    have hr := xi_divisor_support_im_ne_zero r.1
    norm_num at hi
    apply hr
    linarith
  have h2 : fluxExponent q r 2=0 ↔ (r.1:ℂ)=4-4*(q.1:ℂ) := by
    change (2-2*(q.1:ℂ))-(r.1:ℂ)/2=0 ↔ _
    constructor
    · intro h; linear_combination -2*h
    · intro h; linear_combination -(1/2:ℂ)*h
  fin_cases i <;> norm_num [Fin.ext_iff,h0,h1,h2]
  exact h2

/-- The actual finite cusp expansion has no diagonal constant height power. -/
theorem fluxExponent_diagonal_ne_zero (q : XiZeroCopy) (i : Fin 3) :
    fluxExponent q q i≠0 := by
  intro he
  have h := (fluxExponent_zero_iff q q i).mp he
  have hq := xi_divisor_support_im_ne_zero q.1
  rcases h with ⟨_,h⟩ | ⟨_,h⟩ <;>
    have hi := congrArg Complex.im h <;>
    norm_num [Complex.mul_im,Complex.mul_re] at hi <;> apply hq <;> linarith

/-- Coefficient at height exponent zero of the identified three-power expansion.
This is a finite-expansion coefficient, not an assertion that the raw flux has a limit. -/
def constantFluxCoefficient (q r : XiZeroCopy) (b : Bool) : ℂ :=
  ∑ i : Fin 3, if fluxExponent q r i=0 then fluxCoefficient q r b i else 0

/-- Exact original-source classification of the mixed particular constant coefficient. -/
theorem constantFluxCoefficient_eq (q r : XiZeroCopy) (b : Bool) :
    constantFluxCoefficient q r b=
      (if (r.1:ℂ)=4*(q.1:ℂ) then fluxCoefficient q r b 0 else 0)+
      (if (r.1:ℂ)=4-4*(q.1:ℂ) then fluxCoefficient q r b 2 else 0) := by
  simp [constantFluxCoefficient,Fin.sum_univ_three,fluxExponent_zero_iff]

/-- Diagonal constant-coefficient cancellation is source-derived, without RH. -/
theorem constantFluxCoefficient_diagonal (q : XiZeroCopy) (b : Bool) :
    constantFluxCoefficient q q b=0 := by
  simp only [constantFluxCoefficient,fluxExponent_diagonal_ne_zero,↓reduceIte,Finset.sum_const_zero]


end
end RHTower.D4BMMixedParticularCuspFlux
