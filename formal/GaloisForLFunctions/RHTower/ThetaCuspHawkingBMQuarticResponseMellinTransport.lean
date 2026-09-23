import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticResponseCuspPair

/-!
# Source and endpoint transport of the actual physically tested response periods

The constructed full angular response obeys its original forced mean equation.
The three height weights of the physical scalar test times the theta principal
half-square are nonresonant on both actual branches. Their full-response periods
therefore equal explicit endpoint Wronskians minus complete source moments,
divided by the original spectral gaps. The full-test cusp remainder is retained
in the resulting finite-height pairing identity.

Both native response coefficients remain in the endpoint data. No infinite-height
limit, complete action identification or fixed-Hawking-clock extinction is assumed
or asserted. All height weights come from the original source and physical test.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff MatrixGroups
namespace RHTower.D4BMQuarticResponseMellinTransport
open D4BMModularCore D4BMGlobalAngularResponse D4BMJointSource D4BMCuspResponse
open D4BMQuarticResponseCuspPair D4BMAngularSeries
noncomputable section
set_option autoImplicit false

private def fullPlanar (q : XiZeroCopy) (branch : Bool) : ℂ → ℂ :=
  fullAngular q branch ∘ ofComplex

private def squarePlanar (q : XiZeroCopy) (z : ℂ) : ℂ :=
  fullSquarePotential q (angularCoordinates z)

/-- Horizontal mean of the constructed full angular response. -/
def fullMean (q : XiZeroCopy) (branch : Bool) : ℝ → ℂ := average (fullPlanar q branch)

/-- Complete theta half-square mean, including the full signed Fourier tail. -/
def sourceMean (q : XiZeroCopy) : ℝ → ℂ := average (squarePlanar q)

/-- The source mean is the actual half-square horizontal integral, without a cusp truncation. -/
theorem sourceMean_eq_horizontal (q : XiZeroCopy) (y : ℝ) :
    sourceMean q y=D4BMCuspProjection.mean (fun x => fullSquarePotential q ![x,y]) := by
  unfold sourceMean D4BMCuspResponse.average D4BMCuspProjection.mean
  apply integral_congr_ae
  filter_upwards with x
  have he : angularCoordinates (point x y)=![x,y] := by
    ext j
    fin_cases j <;> simp [angularCoordinates,point]
  simp only [squarePlanar,he]

private theorem fullPlanar_smooth (q : XiZeroCopy) (branch : Bool) :
    ContDiffOn ℝ ∞ (fullPlanar q branch) {z : ℂ | 0 < z.im} :=
  (fullAngular_smooth q branch).planar_contDiffOn

private theorem squarePlanar_smooth (q : XiZeroCopy) :
    ContDiffOn ℝ ∞ (squarePlanar q) {z : ℂ | 0 < z.im} := by
  have hs := cuspLeg_contDiffOn .scalar (center q)
  have hQ : ContDiffOn ℝ ∞ (fullSquarePotential q) domain :=
    contDiffOn_const.mul (hs.mul hs)
  exact hQ.comp angularCoordinates.contDiff.contDiffOn (fun _ hz => hz)

private theorem fullPlanar_periodic (q : XiZeroCopy) (branch : Bool) {y : ℝ}
    (hy : 0 < y) (x : ℝ) :
    fullPlanar q branch (point (x+1) y)=fullPlanar q branch (point x y) := by
  have hpos (t : ℝ) : 0 < (point t y).im := by simpa [point] using hy
  have ht : ofComplex (point (x+1) y)=T • ofComplex (point x y) := by
    rw [ofComplex_apply_of_im_pos (hpos x),ofComplex_apply_of_im_pos (hpos (x+1))]
    apply UpperHalfPlane.ext_re_im
    · rw [ModularGroup.re_T_smul]
      simp [point]
    · rw [ModularGroup.im_T_smul]
      simp [point]
  have h := fullAngular_invariant q branch (QuotientGroup.mk T) (ofComplex (point x y))
  simpa only [fullPlanar,Function.comp_apply,ht,PSL2Z_mk_smul] using h

private theorem fullPlanar_equation (q : XiZeroCopy) (branch : Bool) (z : ℂ)
    (hz : 0 < z.im) :
    (z.im:ℂ)^(2 : ℕ)*planarLaplacian (fullPlanar q branch) z=
      parameter q branch*(fullPlanar q branch z+squarePlanar q z) := by
  have h := fullAngular_classical_equation q branch ⟨z,hz⟩
  simp only [chartLaplacian,coordinates] at h
  change (z.im:ℂ)^(2 : ℕ)*planarLaplacian (fullPlanar q branch) z-
    parameter q branch*fullAngular q branch ⟨z,hz⟩=
      parameter q branch/2*scalar (center q) (angularCoordinates z)^(2 : ℕ) at h
  dsimp only [fullPlanar] at h
  dsimp only [fullPlanar,Function.comp_apply,squarePlanar,fullSquarePotential]
  rw [ofComplex_apply_of_im_pos hz]
  linear_combination h

private theorem fullMean_hasDerivAt (q : XiZeroCopy) (branch : Bool) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fullMean q branch) (deriv (fullMean q branch) y) y :=
  (average_hasDerivAt (fullPlanar q branch) (fullPlanar_smooth q branch) hy).differentiableAt.hasDerivAt

private theorem fullMean_second_hasDerivAt (q : XiZeroCopy) (branch : Bool) {y : ℝ}
    (hy : 0 < y) :
    HasDerivAt (deriv (fullMean q branch)) (deriv (deriv (fullMean q branch)) y) y :=
  (average_second_hasDerivAt (fullPlanar q branch) (fullPlanar_smooth q branch) hy).differentiableAt.hasDerivAt

/-- The constructed full mean solves the original equation, with no principal-source replacement. -/
theorem fullMean_equation (q : XiZeroCopy) (branch : Bool) (y : Ioi (0:ℝ)) :
    (y:ℂ)^(2 : ℕ)*deriv (deriv (fullMean q branch)) y-parameter q branch*fullMean q branch y=
      parameter q branch*sourceMean q y := by
  have hL := average_laplacian (fullPlanar q branch) (fullPlanar_smooth q branch) y.2
    (fullPlanar_periodic q branch y.2)
  have hA : IntegrableOn (fun x : ℝ => fullPlanar q branch (point x y))
      (Ioc (-1/2:ℝ) (1/2)) volume :=
    (slice_continuous (fullPlanar q branch) (fullPlanar_smooth q branch) y.2).integrableOn_Ioc
  have hQ : IntegrableOn (fun x : ℝ => squarePlanar q (point x y))
      (Ioc (-1/2:ℝ) (1/2)) volume :=
    (slice_continuous (squarePlanar q) (squarePlanar_smooth q) y.2).integrableOn_Ioc
  have he : (y:ℂ)^(2 : ℕ)*average (planarLaplacian (fullPlanar q branch)) y=
      parameter q branch*(fullMean q branch y+sourceMean q y) := by
    dsimp only [D4BMCuspResponse.average,D4BMCuspProjection.mean,fullMean,sourceMean]
    rw [← integral_const_mul]
    calc
      _ = ∫ x in Ioc (-1/2:ℝ) (1/2),
          parameter q branch*(fullPlanar q branch (point x y)+squarePlanar q (point x y)) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x _hx
        simpa only [point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,
          Complex.ofReal_re,zero_add] using
          fullPlanar_equation q branch (point x y) (by
            have hy : (0:ℝ) < (y:ℝ) := y.2
            simpa only [point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,
              Complex.ofReal_re,zero_add] using hy)
      _ = _ := by rw [integral_const_mul,integral_add hA hQ]
  rw [hL] at he
  change (y:ℂ)^(2 : ℕ)*deriv (deriv (fullMean q branch)) y=_ at he
  linear_combination he

/-- Agreement with the source-faithful cusp formula, retaining its native coefficients and moments. -/
theorem fullMean_eq_cusp_data (q : XiZeroCopy) (branch : Bool) (y : Ioi (3:ℝ)) :
    fullMean q branch y=fullResponseCuspMean q branch y := by
  rw [← fullAngularField_cusp_mean]
  rfl

/-- The three unchanged height weights of the actual physical scalar test times the source principal. -/
def physicalWeight (q : XiZeroCopy) (i : Fin 3) : ℂ :=
  1-(q.1:ℂ)/2+principalExponent q i

/-- The weights are exactly those of the original physical left test times all three source powers. -/
theorem physical_principal_square_expansion (q : XiZeroCopy) (y : Ioi (0:ℝ)) :
    D4BMGlobalAngularResponse.principal (physicalAngularParameter q) ![0,y]*principalSquare q ![0,y]=
      reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3,
        principalAmplitude q i*(y:ℂ)^(physicalWeight q i) := by
  rw [physicalScalar_principal,principalSquare_expansion q _ y.2]
  change reflectedCompletedLambda ((q.1:ℂ)-1)*(y:ℂ)^(1-(q.1:ℂ)/2)*
    (∑ i : Fin 3, principalAmplitude q i*(y:ℂ)^(principalExponent q i))=_
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [physicalWeight,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr y.2.ne')]
  ring

/-- Original response/source spectral gap for a physical testing weight. -/
def physicalGap (q : XiZeroCopy) (branch : Bool) (i : Fin 3) : ℂ :=
  parameter q branch-physicalWeight q i*(physicalWeight q i-1)

private theorem physicalWeight_ne_root (q : XiZeroCopy) (branch alternate : Bool) (i : Fin 3) :
    physicalWeight q i ≠ root q branch alternate := by
  have hi := xi_divisor_support_im_ne_zero q.1
  intro h
  have him := congrArg Complex.im h
  cases branch <;> cases alternate <;> fin_cases i <;>
    norm_num [physicalWeight,principalExponent,root,D4BMCuspProjection.physicalRate,
      Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.div_im] at him <;>
    apply hi <;> linarith

/-- Every physical testing weight is nonresonant on both actual Xi source branches. -/
theorem physicalGap_ne_zero (q : XiZeroCopy) (branch : Bool) (i : Fin 3) :
    physicalGap q branch i ≠ 0 := by
  have hfactor : physicalGap q branch i=
      -(physicalWeight q i-root q branch false)*(physicalWeight q i-root q branch true) := by
    rw [physicalGap,D4BMCuspProjection.physicalRate_parameter]
    simp only [root,Bool.false_eq_true,if_false,if_true]
    ring
  rw [hfactor]
  exact mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (physicalWeight_ne_root q branch false i)))
    (sub_ne_zero.mpr (physicalWeight_ne_root q branch true i))

/-- Actual full-response Wronskian against an original physical testing weight. -/
def physicalFlux (q : XiZeroCopy) (branch : Bool) (i : Fin 3) (y : ℝ) : ℂ :=
  (y:ℂ)^(physicalWeight q i)*deriv (fullMean q branch) y-
    physicalWeight q i*(y:ℂ)^(physicalWeight q i-1)*fullMean q branch y

private theorem power_step (a : ℂ) {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^a=(y:ℂ)^(a-2)*(y:ℂ)^(2 : ℕ) := by
  have he : (y:ℂ)^(2:ℂ)=(y:ℂ)^(2 : ℕ) := by norm_cast
  rw [← he,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
  congr 1
  ring

/-- Exact source-driven flux law at all six physical weights, retaining the full response. -/
theorem physicalFlux_hasDerivAt (q : XiZeroCopy) (branch : Bool) (i : Fin 3) (y : Ioi (0:ℝ)) :
    HasDerivAt (physicalFlux q branch i)
      ((y:ℂ)^(physicalWeight q i-2)*
        (parameter q branch*sourceMean q y+physicalGap q branch i*fullMean q branch y)) y := by
  let v := physicalWeight q i
  have hp := GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := v) y.2
  have hp1 := GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := v-1) y.2
  have h := (hp.mul (fullMean_second_hasDerivAt q branch y.2)).sub
    ((hp1.const_mul v).mul (fullMean_hasDerivAt q branch y.2))
  change HasDerivAt (physicalFlux q branch i) _ y at h
  convert h using 1
  have he := fullMean_equation q branch y
  rw [← he]
  dsimp only [physicalGap]
  rw [show v-1-1=v-2 by ring,power_step v y.2]
  dsimp only [v]
  ring

/-- The full response integral is determined by its actual endpoint jets and complete source moment. -/
theorem physical_response_segment (q : XiZeroCopy) (branch : Bool) (i : Fin 3)
    (a b : Ioi (0:ℝ)) :
    (∫ y in (a:ℝ)..b, (y:ℂ)^(physicalWeight q i-2)*fullMean q branch y)=
      (physicalFlux q branch i b-physicalFlux q branch i a-
        parameter q branch*(∫ y in (a:ℝ)..b, (y:ℂ)^(physicalWeight q i-2)*sourceMean q y))/
          physicalGap q branch i := by
  have hp : ∀ y ∈ uIcc (a:ℝ) b, 0 < y := by
    intro y hy
    exact (lt_min a.2 b.2).trans_le hy.1
  have hw : ContinuousOn (fun y : ℝ => (y:ℂ)^(physicalWeight q i-2)) (uIcc (a:ℝ) b) :=
    fun y hy => (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := physicalWeight q i-2)
      (hp y hy)).continuousAt.continuousWithinAt
  have hM : ContinuousOn (fullMean q branch) (uIcc (a:ℝ) b) :=
    fun y hy => (fullMean_hasDerivAt q branch (hp y hy)).continuousAt.continuousWithinAt
  have hQ : ContinuousOn (sourceMean q) (uIcc (a:ℝ) b) :=
    fun y hy => (average_hasDerivAt (squarePlanar q) (squarePlanar_smooth q)
      (hp y hy)).continuousAt.continuousWithinAt
  have hiM : IntervalIntegrable (fun y : ℝ => (y:ℂ)^(physicalWeight q i-2)*fullMean q branch y)
      volume (a:ℝ) b := (hw.mul hM).intervalIntegrable
  have hiQ : IntervalIntegrable (fun y : ℝ => (y:ℂ)^(physicalWeight q i-2)*sourceMean q y)
      volume (a:ℝ) b := (hw.mul hQ).intervalIntegrable
  have hi : IntervalIntegrable (fun y : ℝ => (y:ℂ)^(physicalWeight q i-2)*
      (parameter q branch*sourceMean q y+physicalGap q branch i*fullMean q branch y))
      volume (a:ℝ) b :=
    (hw.mul ((hQ.const_mul _).add (hM.const_mul _))).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => physicalFlux_hasDerivAt q branch i ⟨y,hp y hy⟩) hi
  have he : (fun y : ℝ => (y:ℂ)^(physicalWeight q i-2)*
      (parameter q branch*sourceMean q y+physicalGap q branch i*fullMean q branch y))=
      fun y : ℝ => parameter q branch*((y:ℂ)^(physicalWeight q i-2)*sourceMean q y)+
        physicalGap q branch i*((y:ℂ)^(physicalWeight q i-2)*fullMean q branch y) := by
    funext y
    ring
  rw [he,intervalIntegral.integral_add (hiQ.const_mul _) (hiM.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
  apply (eq_div_iff (physicalGap_ne_zero q branch i)).mpr
  linear_combination h

/-- The original physical principal/source pairing transports through all three complete response moments. -/
theorem physical_principal_response_segment (q : XiZeroCopy) (branch : Bool)
    (a b : Ioi (0:ℝ)) :
    (∫ y in (a:ℝ)..b,
      D4BMGlobalAngularResponse.principal (physicalAngularParameter q) ![0,y]*
        principalSquare q ![0,y]*fullMean q branch y/(y:ℂ)^(2 : ℕ))=
      reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3, principalAmplitude q i*
        ((physicalFlux q branch i b-physicalFlux q branch i a-
          parameter q branch*(∫ y in (a:ℝ)..b, (y:ℂ)^(physicalWeight q i-2)*sourceMean q y))/
            physicalGap q branch i) := by
  have hp : ∀ y ∈ uIcc (a:ℝ) b, 0 < y := by
    intro y hy
    exact (lt_min a.2 b.2).trans_le hy.1
  have hi (i : Fin 3) : IntervalIntegrable
      (fun y : ℝ => (y:ℂ)^(physicalWeight q i-2)*fullMean q branch y) volume (a:ℝ) b := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact ((GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := physicalWeight q i-2)
      (hp y hy)).continuousAt.mul (fullMean_hasDerivAt q branch (hp y hy)).continuousAt).continuousWithinAt
  calc
    _ = ∫ y in (a:ℝ)..b, reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3,
        principalAmplitude q i*((y:ℂ)^(physicalWeight q i-2)*fullMean q branch y) := by
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only
      rw [physical_principal_square_expansion q ⟨y,hp y hy⟩]
      rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [power_step (physicalWeight q i) (hp y hy)]
      field_simp [Complex.ofReal_ne_zero.mpr (hp y hy).ne']
    _ = reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3, principalAmplitude q i*
        (∫ y in (a:ℝ)..b, (y:ℂ)^(physicalWeight q i-2)*fullMean q branch y) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun i _ => (hi i).const_mul (principalAmplitude q i))]
      simp only [intervalIntegral.integral_const_mul]
    _ = _ := by simp_rw [physical_response_segment q branch]

/-- Actual full-test pairing after its admitted remainder is retained, with both source-derived endpoints explicit. -/
theorem physical_tested_response_segment (q : XiZeroCopy) (branch : Bool)
    (a b : Ioi (3:ℝ)) :
    (∫ y in (a:ℝ)..b,
      (D4BMCuspProjection.mean (fun x => scalar (physicalAngularParameter q) ![x,y]*
          fullSquarePotential q ![x,y]*fullAngularField q branch ![x,y])-
        D4BMCuspProjection.mean (fun x => testedResponseTail q branch (physicalAngularParameter q) ![x,y]))/
          (y:ℂ)^(2 : ℕ))=
      reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3, principalAmplitude q i*
        ((physicalFlux q branch i b-physicalFlux q branch i a-
          parameter q branch*(∫ y in (a:ℝ)..b, (y:ℂ)^(physicalWeight q i-2)*sourceMean q y))/
            physicalGap q branch i) := by
  calc
    _ = ∫ y in (a:ℝ)..b,
        D4BMGlobalAngularResponse.principal (physicalAngularParameter q) ![0,y]*
          principalSquare q ![0,y]*fullMean q branch y/(y:ℂ)^(2 : ℕ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hhigh : 3 < y := (lt_min a.2 b.2).trans_le hy.1
      have h := tested_square_response_cusp_mean q branch (physicalAngularParameter q) ⟨y,hhigh⟩
      rw [← fullMean_eq_cusp_data q branch ⟨y,hhigh⟩] at h
      dsimp only
      rw [h,add_sub_cancel_right]
    _ = _ := physical_principal_response_segment q branch
      ⟨(a:ℝ),lt_trans (by norm_num : (0:ℝ)<3) a.2⟩
      ⟨(b:ℝ),lt_trans (by norm_num : (0:ℝ)<3) b.2⟩

end
end RHTower.D4BMQuarticResponseMellinTransport
