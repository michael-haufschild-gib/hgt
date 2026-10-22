import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticResponseWork
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspGrowingCoefficient
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarSourcePairingAdmission
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalData
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticPrincipalExpansion

/-!
# Complete scalar-tested cusp decomposition of the original radial source work

The full squared-source remainder and the Fourier tail of every literal scalar test
pair absolutely with both constructed angular responses. The local `Q²` term has
its own complete admitted remainder, obtained from the actual quartic jet expansion.
The exact horizontal cusp mean of the original incoming SV-SV response work retains
both particular responses, both native homogeneous coefficients, all infinite source
moments, and all three tested remainders at the original height cutoff.

This establishes source-work cusp identities and absolute admission of their tails.
The remaining height periods, angular-current boundary action, other independent
channels and complete fixed-Hawking-clock extinction are not asserted here.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMQuarticResponseCuspPair
open D4BMGlobalAngularResponse D4BMModularCore D4BMJointSource D4BMAngularSeries
open D4BMCuspResponse D4BMQuarticResponseWork
open D4BMSquareCuspJets D4BMQuarticPrincipalExpansion D4BMQuarticCutoffMellin
noncomputable section
set_option autoImplicit false

private theorem weighted_scalar_remainder_bound (u v w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 3 ≤ z 1 →
      ‖(z 1:ℂ)^w*scalar v z*squareRemainder u z‖ ≤ C := by
  let e0 := d4BMCompletedEisensteinCuspWeylExponent v false
  let e1 := d4BMCompletedEisensteinCuspWeylExponent v true
  let a0 := d4BMCompletedEisensteinCuspConstantCoefficient v false
  let a1 := d4BMCompletedEisensteinCuspConstantCoefficient v true
  obtain ⟨C0,hC0,h0⟩ := weighted_squareRemainder_bounded u (w+e0) 3 (by norm_num)
  obtain ⟨C1,hC1,h1⟩ := weighted_squareRemainder_bounded u (w+e1) 3 (by norm_num)
  obtain ⟨T,hT,ht⟩ := weighted_tail_bounded v w 3 (by norm_num)
  obtain ⟨R,hR,hr⟩ := squareRemainder_bounded u 3 (by norm_num)
  refine ⟨‖a0‖*C0+‖a1‖*C1+T*R,by positivity,?_⟩
  intro z hz
  have hn : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have he : (z 1:ℂ)^w*scalar v z*squareRemainder u z=
      a0*((z 1:ℂ)^(w+e0)*squareRemainder u z)+
      a1*((z 1:ℂ)^(w+e1)*squareRemainder u z)+
      ((z 1:ℂ)^w*tail v z)*squareRemainder u z := by
    rw [Complex.cpow_add _ _ hn,Complex.cpow_add _ _ hn]
    change (z 1:ℂ)^w*(D4BMGlobalAngularResponse.principal v z+tail v z)*squareRemainder u z=_
    dsimp [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
      d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,
      a0,a1,e0,e1]
    ring
  rw [he]
  calc
    _ ≤ (‖a0*((z 1:ℂ)^(w+e0)*squareRemainder u z)‖+
        ‖a1*((z 1:ℂ)^(w+e1)*squareRemainder u z)‖)+
        ‖((z 1:ℂ)^w*tail v z)*squareRemainder u z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [norm_mul]
      gcongr
      · simpa only [norm_mul] using h0 z hz
      · simpa only [norm_mul] using h1 z hz
      · simpa only [norm_mul] using ht z hz
      · exact hr z hz

/-- Every complex height weight of the literal scalar/subtracted-square pair is in native L². -/
theorem scalar_power_squareResidual_memLp (q : XiZeroCopy) (u w : ℂ) :
    MemLp (fun z : UpperHalfPlane => (z.im:ℂ)^w*scalar u (coordinates z)*
      squareResidual q (coordinates z)) 2 measure := by
  obtain ⟨C,-,hC⟩ := weighted_scalar_remainder_bound (center q) u w
  have hs : ContinuousOn (scalar u) domain := (cuspLeg_contDiffOn .scalar u).continuousOn
  have hp := (height_cpow_contDiffOn w 0).continuousOn
  apply cuspBound_memLp _ ((hp.mul hs).mul (squareResidual_continuousOn q)) (C/2)
  intro z hz
  simp only [Pi.mul_apply]
  rw [squareResidual_high q z hz,← mul_div_assoc,norm_div]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right (hC z hz.le) (by norm_num)

/-- Actual native response times the source remainder pairs absolutely with every full scalar test. -/
theorem scalar_power_native_remainder_integrable (q : XiZeroCopy) (branch : Bool) (u w : ℂ) :
    Integrable (fun z : UpperHalfPlane => (z.im:ℂ)^w*scalar u (coordinates z)*
      squareResidual q (coordinates z)*globalResponse q branch z) measure := by
  have hR : MemLp (globalResponse q branch) 2 measure :=
    (memLp_congr_ae (globalResponse_native_ae q branch)).mpr (Lp.memLp _)
  exact (scalar_power_squareResidual_memLp q u w).integrable_mul hR

private theorem cutoff_norm (z : Fin 2 → ℝ) : ‖cutoff z‖ ≤ 1 := by
  simpa [cutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg (z 1-2))] using
    Real.smoothTransition.le_one (z 1-2)

private theorem coordinates_cont : Continuous coordinates := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact UpperHalfPlane.continuous_re
  · exact UpperHalfPlane.continuous_im

private theorem cutoff_mul_integrable {f : UpperHalfPlane → ℂ} (hf : Integrable f measure) :
    Integrable (fun z => f z*cutoff (coordinates z)) measure := by
  have hc : Continuous (fun z : UpperHalfPlane => cutoff (coordinates z)) :=
    sourceCutoff_smooth.continuous.comp coordinates_cont
  exact hf.mul_bdd
    hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => cutoff_norm (coordinates z)))

private theorem full_response_integrable (q : XiZeroCopy) (branch : Bool) (f : UpperHalfPlane → ℂ)
    (hf : ∀ w : ℂ, MemLp (fun z => (z.im:ℂ)^w*f z) 2 measure) :
    Integrable (fun z => f z*fullAngular q branch z) measure := by
  have hc (w : ℂ) := cutoff_mul_integrable (MemLp.integrable (by norm_num) (hf w))
  let rho : ℂ := q.1
  let P := parameter q branch
  let A := d4BMCompletedEisensteinCuspConstantCoefficient (center q) true
  let B := d4BMCompletedEisensteinCuspConstantCoefficient (center q) false
  let c0 := (P/2)*(A^(2 : ℕ)/((2*rho)*(2*rho-1)-P))
  let c1 := (P/2)*((2*A*B)/(-P))
  let c2 := (P/2)*(B^(2 : ℕ)/((2-2*rho)*(1-2*rho)-P))
  have h := (((hc (2*rho)).const_mul c0).add ((hc 1).const_mul c1)).add
    ((hc (2-2*rho)).const_mul c2)
  have hK : Integrable (fun z => f z*cutoffResponse q branch (coordinates z)) measure := by
    apply h.congr
    filter_upwards with z
    simp only [Pi.add_apply]
    dsimp [cutoffResponse,cuspResponse,D4BMQuadraticMixedSource.cuspPowerResponse,
      D4BMQuadraticMixedSource.powerResponse,c0,c1,c2,P,A,B,rho,coordinates]
    ring
  have hR : MemLp (globalResponse q branch) 2 measure :=
    (memLp_congr_ae (globalResponse_native_ae q branch)).mpr (Lp.memLp _)
  have hf0 : MemLp f 2 measure := by simpa only [Complex.cpow_zero,one_mul] using hf 0
  apply (hK.add (hf0.integrable_mul hR)).congr
  filter_upwards [ae_mem_interior] with z hz
  simp only [Pi.add_apply,Pi.mul_apply]
  rw [fullAngular,globalCuspCutoff_eq_on_fd q branch z (fdo_subset_fd hz)]
  ring

private theorem field_coordinates (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane) :
    fullAngularField q branch (coordinates z)=fullAngular q branch z := by
  change fullAngular q branch (ofComplex (angularCoordinates.symm (angularCoordinates (z:ℂ))))=_
  rw [ContinuousLinearEquiv.symm_apply_apply,ofComplex_apply]

/-- The source remainder against the complete response, with its original cusp cutoff. -/
def responseTailPair (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ) : ℂ :=
  squareResidual q z*fullAngularField q branch z

/-- The complete source-tail/response pairing is absolutely admitted against every literal scalar test. -/
theorem responseTailPair_scalar_integrable (q : XiZeroCopy) (branch : Bool) (u : ℂ) :
    Integrable (fun z : UpperHalfPlane => scalar u (coordinates z)*responseTailPair q branch (coordinates z))
      measure := by
  have h := full_response_integrable q branch
    (fun z => scalar u (coordinates z)*squareResidual q (coordinates z))
    (fun w => by simpa only [mul_assoc] using scalar_power_squareResidual_memLp q u w)
  simpa only [responseTailPair,field_coordinates,mul_assoc] using h

private theorem tail_continuousOn (u : ℂ) : ContinuousOn (tail u) domain := by
  have he : tail u=(fun z => scalar u z-D4BMGlobalAngularResponse.principal u z) := by
    funext z
    change tail u z=(D4BMGlobalAngularResponse.principal u z+tail u z)-_
    ring
  rw [he]
  exact (cuspLeg_contDiffOn .scalar u).continuousOn.sub
    (cuspConstantPart_contDiffOn .scalar u).continuousOn

private theorem power_tail_memLp (u w : ℂ) :
    MemLp (fun z : UpperHalfPlane => (z.im:ℂ)^w*tail u (coordinates z)) 2 measure := by
  obtain ⟨C,-,hC⟩ := weighted_tail_bounded u w 3 (by norm_num)
  apply cuspBound_memLp _ ((height_cpow_contDiffOn w 0).continuousOn.mul (tail_continuousOn u)) C
  intro z hz
  exact hC z hz.le

/-- Every height-weighted Fourier tail of the full scalar test pairs with the complete response. -/
theorem scalarTail_power_response_integrable (q : XiZeroCopy) (branch : Bool) (u w : ℂ) :
    Integrable (fun z : UpperHalfPlane =>
      (z.im:ℂ)^w*tail u (coordinates z)*fullAngular q branch z) measure := by
  apply full_response_integrable q branch (fun z => (z.im:ℂ)^w*tail u (coordinates z))
  intro v
  have he : (fun z : UpperHalfPlane => (z.im:ℂ)^v*((z.im:ℂ)^w*tail u (coordinates z)))=
      fun z => (z.im:ℂ)^(v+w)*tail u (coordinates z) := by
    funext z
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr z.im_pos.ne')]
    ring
  rw [he]
  exact power_tail_memLp u (v+w)

private theorem scalarTail_principalSquare_response_integrable (q : XiZeroCopy)
    (branch : Bool) (u : ℂ) :
    Integrable (fun z : UpperHalfPlane =>
      tail u (coordinates z)*principalSquare q (coordinates z)*fullAngular q branch z) measure := by
  have h (i : Fin 3) :=
    (scalarTail_power_response_integrable q branch u (principalExponent q i)).const_mul (principalAmplitude q i)
  apply ((h 0).add (h 1) |>.add (h 2)).congr
  filter_upwards with z
  simp only [Pi.add_apply]
  rw [principalSquare_expansion q _ z.im_pos]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change _=tail u (coordinates z)*
    (principalAmplitude q 0*(z.im:ℂ)^(principalExponent q 0)+
      (principalAmplitude q 1*(z.im:ℂ)^(principalExponent q 1)+
        principalAmplitude q 2*(z.im:ℂ)^(principalExponent q 2)))*fullAngular q branch z
  ring

/-- Complete scalar-test/source remainder against the actual response, with the original cutoff. -/
def testedResponseTail (q : XiZeroCopy) (branch : Bool) (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  (scalar u z*fullSquarePotential q z-
    cutoff z*D4BMGlobalAngularResponse.principal u z*principalSquare q z)*fullAngularField q branch z

/-- Both the original squared-source tail and the full scalar test's tail are absolutely admitted. -/
theorem testedResponseTail_integrable (q : XiZeroCopy) (branch : Bool) (u : ℂ) :
    Integrable (fun z : UpperHalfPlane => testedResponseTail q branch u (coordinates z)) measure := by
  have h := (responseTailPair_scalar_integrable q branch u).add
    (cutoff_mul_integrable (scalarTail_principalSquare_response_integrable q branch u))
  apply h.congr
  filter_upwards with z
  simp only [Pi.add_apply,testedResponseTail,responseTailPair,squareResidual,field_coordinates]
  change (D4BMGlobalAngularResponse.principal u (coordinates z)+tail u (coordinates z))*_+_=
    ((D4BMGlobalAngularResponse.principal u (coordinates z)+tail u (coordinates z))*_-_)*_
  ring

private theorem full_slice_continuous (q : XiZeroCopy) (branch : Bool) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => fullAngularField q branch ![x,y]) := by
  have hA : ContinuousOn (fullAngularField q branch) domain :=
    fun z hz => (fullAngularField_smooth q branch z hz).continuousAt.continuousWithinAt
  have hc : Continuous (fun x : ℝ => (![x,y] : Fin 2 → ℝ)) := by fun_prop
  exact hA.comp_continuous hc (fun _ => hy)

private theorem square_slice_continuous (q : XiZeroCopy) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => fullSquarePotential q ![x,y]) := by
  have hQ : ContinuousOn (fullSquarePotential q) domain :=
    fun z hz => (fullSquarePotential_smooth q z hz 0).continuousAt.continuousWithinAt
  have hc : Continuous (fun x : ℝ => (![x,y] : Fin 2 → ℝ)) := by fun_prop
  exact hQ.comp_continuous hc (fun _ => hy)

private theorem full_cusp_value (q : XiZeroCopy) (branch : Bool) {x y : ℝ}
    (hx : x ∈ Ioc (-1/2:ℝ) (1/2)) (hy : 3 < y) :
    fullAngularField q branch ![x,y]=cuspResponse q branch ![0,y]+
      responsePlanar q branch (point x y) := by
  let z : UpperHalfPlane := ⟨point x y,by simp [point]; linarith⟩
  have hcoord : coordinates z=![x,y] := by
    ext j
    fin_cases j <;> simp [coordinates,z,point]
  have hfd : z ∈ fd := by
    constructor
    · change 1 ≤ Complex.normSq (point x y)
      simp only [Complex.normSq_apply,point,Complex.add_re,Complex.add_im,Complex.ofReal_re,
        Complex.ofReal_im,Complex.mul_I_re,Complex.mul_I_im,neg_zero,add_zero,zero_add]
      nlinarith [sq_nonneg x]
    · change |(point x y).re| ≤ 1/2
      simpa [point] using abs_le.mpr ⟨by simpa only [neg_div] using hx.1.le,hx.2⟩
  rw [← hcoord,field_coordinates,fullAngular,globalCuspCutoff_eq_on_fd q branch z hfd,hcoord]
  have hc : cutoff ![x,y]=1 := by
    change ((Real.smoothTransition (y-2):ℝ):ℂ)=1
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    rfl
  rw [cutoffResponse,hc,one_mul]
  have he : cuspResponse q branch ![x,y]=cuspResponse q branch ![0,y] := rfl
  rw [he]
  congr 1
  change globalResponse q branch z=globalResponse q branch (ofComplex (z:ℂ))
  rw [ofComplex_apply]

/-- Actual source and boundary data in the native selected cusp mean of the full response. -/
def fullResponseCuspMean (q : XiZeroCopy) (branch : Bool) (y : ℝ) : ℂ :=
  cuspResponse q branch ![0,y]+(y:ℂ)^(root q branch false)*limitingCoefficient q branch false+
    ((y:ℂ)^(root q branch false)*(∫ t in Ioi y, fluxSource q branch true t)-
      (y:ℂ)^(root q branch true)*(∫ t in Ioi y, fluxSource q branch false t))/rootGap q branch

/-- The full response's actual cusp mean retains its native homogeneous coefficient and source tails. -/
theorem fullAngularField_cusp_mean (q : XiZeroCopy) (branch : Bool) (y : Ioi (3:ℝ)) :
    D4BMCuspProjection.mean (fun x => fullAngularField q branch ![x,y])=
      fullResponseCuspMean q branch y := by
  have hp : 0 < (y:ℝ) := lt_trans (by norm_num) y.2
  have hi : IntegrableOn (fun x => responsePlanar q branch (point x y)) (Ioc (-1/2:ℝ) (1/2)) volume :=
    (slice_continuous (responsePlanar q branch) (responsePlanar_smooth q branch) hp).integrableOn_Ioc
  change (∫ x in Ioc (-1/2:ℝ) (1/2), fullAngularField q branch ![x,y])=_
  calc
    _ = ∫ x in Ioc (-1/2:ℝ) (1/2), cuspResponse q branch ![0,y]+responsePlanar q branch (point x y) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact full_cusp_value q branch hx y.2
    _ = cuspResponse q branch ![0,y]+responseMean q branch y := by
      rw [integral_add (integrable_const _) hi]
      norm_num [responseMean,D4BMCuspResponse.average,D4BMCuspProjection.mean]
    _ = _ := by
      rw [responseMean_native_decomposition q branch y.2]
      dsimp only [fullResponseCuspMean]
      ring

/-- Exact original square/response cusp pairing, separating only an absolutely admitted tail. -/
theorem square_response_cusp_mean (q : XiZeroCopy) (branch : Bool) (y : Ioi (3:ℝ)) :
    D4BMCuspProjection.mean (fun x => fullSquarePotential q ![x,y]*fullAngularField q branch ![x,y])=
      principalSquare q ![0,y]*fullResponseCuspMean q branch y+
      D4BMCuspProjection.mean (fun x => responseTailPair q branch ![x,y]) := by
  have hp : 0 < (y:ℝ) := lt_trans (by norm_num) y.2
  have hA := full_slice_continuous q branch hp
  have hR : Continuous (fun x : ℝ => responseTailPair q branch ![x,y]) :=
    ((squareResidual_continuousOn q).comp_continuous (by fun_prop) (fun _ => hp)).mul hA
  rw [← fullAngularField_cusp_mean]
  change (∫ x in Ioc (-1/2:ℝ) (1/2), fullSquarePotential q ![x,y]*fullAngularField q branch ![x,y])=_
  calc
    _ = ∫ x in Ioc (-1/2:ℝ) (1/2),
        principalSquare q ![0,y]*fullAngularField q branch ![x,y]+responseTailPair q branch ![x,y] := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have hc : cutoff ![x,(y:ℝ)]=1 := by
        change ((Real.smoothTransition ((y:ℝ)-2):ℝ):ℂ)=1
        rw [Real.smoothTransition.one_of_one_le (by have : 3 < (y:ℝ) := y.2; linarith)]
        rfl
      dsimp only [responseTailPair,squareResidual]
      rw [hc,one_mul]
      change _=principalSquare q ![x,y]*_+_
      ring
    _ = _ := by
      rw [integral_add (hA.const_mul _).integrableOn_Ioc hR.integrableOn_Ioc,integral_const_mul]
      rfl

/-- Exact cusp pairing with the full scalar testing leg, retaining every native boundary coefficient. -/
theorem tested_square_response_cusp_mean (q : XiZeroCopy) (branch : Bool) (u : ℂ) (y : Ioi (3:ℝ)) :
    D4BMCuspProjection.mean (fun x =>
      scalar u ![x,y]*fullSquarePotential q ![x,y]*fullAngularField q branch ![x,y])=
      D4BMGlobalAngularResponse.principal u ![0,y]*principalSquare q ![0,y]*fullResponseCuspMean q branch y+
        D4BMCuspProjection.mean (fun x => testedResponseTail q branch u ![x,y]) := by
  have hp : 0 < (y:ℝ) := lt_trans (by norm_num) y.2
  have hA := full_slice_continuous q branch hp
  have hQ := square_slice_continuous q hp
  have hc : Continuous (fun x : ℝ => (![x,(y:ℝ)] : Fin 2 → ℝ)) := by fun_prop
  have hs : Continuous (fun x : ℝ => scalar u ![x,y]) :=
    (cuspLeg_contDiffOn .scalar u).continuousOn.comp_continuous hc (fun _ => hp)
  have hcut (x : ℝ) : cutoff ![x,(y:ℝ)]=1 := by
    change ((Real.smoothTransition ((y:ℝ)-2):ℝ):ℂ)=1
    rw [Real.smoothTransition.one_of_one_le (by have : 3 < (y:ℝ) := y.2; linarith)]
    rfl
  have he (x : ℝ) : testedResponseTail q branch u ![x,y]=
      (scalar u ![x,y]*fullSquarePotential q ![x,y]-
        D4BMGlobalAngularResponse.principal u ![0,y]*principalSquare q ![0,y])*fullAngularField q branch ![x,y] := by
    dsimp only [testedResponseTail]
    rw [hcut,one_mul]
    rfl
  have hR : Continuous (fun x : ℝ => testedResponseTail q branch u ![x,y]) := by
    simp_rw [he]
    exact ((hs.mul hQ).sub continuous_const).mul hA
  rw [← fullAngularField_cusp_mean]
  change (∫ x in Ioc (-1/2:ℝ) (1/2),
    scalar u ![x,y]*fullSquarePotential q ![x,y]*fullAngularField q branch ![x,y])=_
  calc
    _ = ∫ x in Ioc (-1/2:ℝ) (1/2),
        (D4BMGlobalAngularResponse.principal u ![0,y]*principalSquare q ![0,y])*fullAngularField q branch ![x,y]+
          testedResponseTail q branch u ![x,y] := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _hx
      dsimp only
      rw [he]
      ring
    _ = _ := by
      rw [integral_add (hA.const_mul _).integrableOn_Ioc hR.integrableOn_Ioc,integral_const_mul]
      rfl

private theorem quartic_zero_field (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    quarticContactField q 0 z=fullSquarePotential q z^(2 : ℕ) := by
  change fullSquarePotential q z*fullSquarePotential q z=_
  ring

private theorem quartic_zero_principal (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    quarticContactPrincipal q 0 z=principalSquare q z^(2 : ℕ) := by
  let X := D4BMGlobalAngularResponse.principal (center q) z
  change ((1/2:ℂ)*(X*X))*((1/2:ℂ)*(X*X))=(X^(2 : ℕ)/2)^(2 : ℕ)
  ring

/-- The local Q² source term with both its source tail and full scalar test retained. -/
def testedSquareTail (q : XiZeroCopy) (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  scalar u z*fullSquarePotential q z^(2 : ℕ)-
    cutoff z*D4BMGlobalAngularResponse.principal u z*principalSquare q z^(2 : ℕ)

/-- Absolute admission of the complete scalar-tested Q² remainder at the original cutoff. -/
theorem testedSquareTail_integrable (q : XiZeroCopy) (u : ℂ) :
    Integrable (fun z : UpperHalfPlane => testedSquareTail q u (coordinates z)) measure := by
  have ht : Integrable (fun z : UpperHalfPlane =>
      tail u (coordinates z)*quarticContactPrincipal q 0 (coordinates z)) measure := by
    have h (j : Fin 5) := (MemLp.integrable (by norm_num)
      (power_tail_memLp u (quarticPrincipalExponent q j))).const_mul (quarticPrincipalCoefficient q 0 j)
    apply (integrable_finsetSum Finset.univ (fun j _ => h j)).congr
    filter_upwards with z
    rw [quarticContactPrincipal_eq_power_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply ((quarticContactResidual_scalar_integrable q 0 u).add (cutoff_mul_integrable ht)).congr
  filter_upwards with z
  simp only [Pi.add_apply,quarticContactResidual,quartic_zero_field,quartic_zero_principal,testedSquareTail]
  change (D4BMGlobalAngularResponse.principal u (coordinates z)+tail u (coordinates z))*_+_=
    (D4BMGlobalAngularResponse.principal u (coordinates z)+tail u (coordinates z))*_-_
  ring

/-- The full scalar-tested local Q² cusp mean includes its complete integrable remainder. -/
theorem tested_square_cusp_mean (q : XiZeroCopy) (u : ℂ) (y : Ioi (3:ℝ)) :
    D4BMCuspProjection.mean (fun x => scalar u ![x,y]*fullSquarePotential q ![x,y] ^ (2 : ℕ))=
      D4BMGlobalAngularResponse.principal u ![0,y]*principalSquare q ![0,y] ^ (2 : ℕ)+
        D4BMCuspProjection.mean (fun x => testedSquareTail q u ![x,y]) := by
  have hp : 0 < (y:ℝ) := lt_trans (by norm_num) y.2
  have hc : Continuous (fun x : ℝ => (![x,(y:ℝ)] : Fin 2 → ℝ)) := by fun_prop
  have hs : Continuous (fun x : ℝ => scalar u ![x,y]) :=
    (cuspLeg_contDiffOn .scalar u).continuousOn.comp_continuous hc (fun _ => hp)
  have hcut (x : ℝ) : cutoff ![x,(y:ℝ)]=1 := by
    change ((Real.smoothTransition ((y:ℝ)-2):ℝ):ℂ)=1
    rw [Real.smoothTransition.one_of_one_le (by have : 3 < (y:ℝ) := y.2; linarith)]
    rfl
  have he (x : ℝ) : testedSquareTail q u ![x,y]=
      scalar u ![x,y]*fullSquarePotential q ![x,y] ^ (2 : ℕ)-
        D4BMGlobalAngularResponse.principal u ![0,y]*principalSquare q ![0,y] ^ (2 : ℕ) := by
    dsimp only [testedSquareTail]
    rw [hcut,one_mul]
    rfl
  have hR : Continuous (fun x : ℝ => testedSquareTail q u ![x,y]) := by
    simp_rw [he]
    exact (hs.mul ((square_slice_continuous q hp).pow 2)).sub continuous_const
  change (∫ x in Ioc (-1/2:ℝ) (1/2), scalar u ![x,y]*fullSquarePotential q ![x,y] ^ (2 : ℕ))=_
  calc
    _ = ∫ x in Ioc (-1/2:ℝ) (1/2),
        D4BMGlobalAngularResponse.principal u ![0,y]*principalSquare q ![0,y] ^ (2 : ℕ)+
          testedSquareTail q u ![x,y] := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _hx
      dsimp only
      rw [he]
      ring
    _ = _ := by
      rw [integral_add (integrable_const _) hR.integrableOn_Ioc]
      norm_num [D4BMCuspProjection.mean]

/-- Every term of the actual radial source work lands on native cusp data and admitted full-test tails. -/
theorem reducedSourceWork_tested_cusp_mean (q : XiZeroCopy) (u : ℂ) (y : Ioi (3:ℝ)) :
    D4BMCuspProjection.mean (fun x => scalar u ![x,y]*reducedSourceWork q ![x,y])=
      D4BMGlobalAngularResponse.principal u ![0,y]*principalSquare q ![0,y]*
        (sourceWorkWeights q 0*parameter q true*fullResponseCuspMean q true y+
          sourceWorkWeights q 1*parameter q false*fullResponseCuspMean q false y)+
      squareWorkCoefficient q*(D4BMGlobalAngularResponse.principal u ![0,y]*principalSquare q ![0,y] ^ (2 : ℕ)+
        D4BMCuspProjection.mean (fun x => testedSquareTail q u ![x,y]))+
      sourceWorkWeights q 0*parameter q true*D4BMCuspProjection.mean (fun x => testedResponseTail q true u ![x,y])+
      sourceWorkWeights q 1*parameter q false*D4BMCuspProjection.mean (fun x => testedResponseTail q false u ![x,y]) := by
  have hp : 0 < (y:ℝ) := lt_trans (by norm_num) y.2
  have hc : Continuous (fun x : ℝ => (![x,(y:ℝ)] : Fin 2 → ℝ)) := by fun_prop
  have hs : Continuous (fun x : ℝ => scalar u ![x,y]) :=
    (cuspLeg_contDiffOn .scalar u).continuousOn.comp_continuous hc (fun _ => hp)
  have hQ := square_slice_continuous q hp
  have hi (branch : Bool) : IntegrableOn (fun x : ℝ =>
      scalar u ![x,y]*fullSquarePotential q ![x,y]*fullAngularField q branch ![x,y])
      (Ioc (-1/2:ℝ) (1/2)) volume :=
    ((hs.mul hQ).mul (full_slice_continuous q branch hp)).integrableOn_Ioc
  have hQ2 : IntegrableOn (fun x : ℝ => scalar u ![x,y]*fullSquarePotential q ![x,y] ^ (2 : ℕ))
      (Ioc (-1/2:ℝ) (1/2)) volume := (hs.mul (hQ.pow 2)).integrableOn_Ioc
  change (∫ x in Ioc (-1/2:ℝ) (1/2), scalar u ![x,y]*reducedSourceWork q ![x,y])=_
  calc
    _ = ∫ x in Ioc (-1/2:ℝ) (1/2),
        (sourceWorkWeights q 0*parameter q true)*
          (scalar u ![x,y]*fullSquarePotential q ![x,y]*fullAngularField q true ![x,y])+
        (sourceWorkWeights q 1*parameter q false)*
          (scalar u ![x,y]*fullSquarePotential q ![x,y]*fullAngularField q false ![x,y])+
        squareWorkCoefficient q*(scalar u ![x,y]*fullSquarePotential q ![x,y] ^ (2 : ℕ)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _hx
      dsimp only [reducedSourceWork]
      ring
    _ = (sourceWorkWeights q 0*parameter q true)*D4BMCuspProjection.mean (fun x =>
          scalar u ![x,y]*fullSquarePotential q ![x,y]*fullAngularField q true ![x,y])+
        (sourceWorkWeights q 1*parameter q false)*D4BMCuspProjection.mean (fun x =>
          scalar u ![x,y]*fullSquarePotential q ![x,y]*fullAngularField q false ![x,y])+
        squareWorkCoefficient q*D4BMCuspProjection.mean (fun x => scalar u ![x,y]*fullSquarePotential q ![x,y] ^ (2 : ℕ)) := by
      have h0 := (hi true).const_mul (sourceWorkWeights q 0*parameter q true)
      have h1 := (hi false).const_mul (sourceWorkWeights q 1*parameter q false)
      have h2 := hQ2.const_mul (squareWorkCoefficient q)
      have h01 := integral_add h0 h1
      have h012 := integral_add (h0.add h1) h2
      simp only [Pi.add_apply] at h01 h012
      rw [h012,h01]
      simp only [integral_const_mul]
      rfl
    _ = _ := by
      rw [tested_square_response_cusp_mean q true u y,tested_square_response_cusp_mean q false u y,
        tested_square_cusp_mean q u y]
      ring

end
end RHTower.D4BMQuarticResponseCuspPair
