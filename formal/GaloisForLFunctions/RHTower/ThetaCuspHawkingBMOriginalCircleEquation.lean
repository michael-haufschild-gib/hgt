import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCircleFlux

/-!
The original theta-circle finite part satisfies the physical Darboux equation.
The genuine metric Laplacian, differentiated cutoff corrections and original
Green flux determine the equation. The physical reader kernel has no real
radius zeros; its conserved Wronskian determines the original period from its
radius-zero source coefficient. No temporal or horizon limit is interchanged.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ContDiff
open GaloisForLFunctions.HTGeometry ScalarTwoJet
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalCircleEquation
open D4BMJointSource D4BMNativeCircle D4BMNativeCuspJets D4BMOriginalCircleGreen
open D4BMOriginalCirclePeriod D4BMOriginalCircleFlux D4BMOriginalScalarRestoration
open D4BMOriginalCausalRestoration D4BMGlobalAngularResponse D4BMModularCore
open D4BMCausalKernel
private abbrev Point := Fin 2 → ℝ
private abbrev Field := Point → ℂ
private abbrev D := @coordDeriv 2
private abbrev L := D4BMAngularSeries.hyperbolicLaplacian
private theorem point_eta (z : Point) : (![z 0,z 1] : Point)=z := by
  ext i
  fin_cases i <;> rfl

private def chart (z : Point) : Point := ![z 0,Real.log (z 1)]
private def pull (F : Field) : Field := fun z => F (chart z)
private theorem positive_nhds {z : Point} (hz : 0 < z 1) : {v : Point | 0 < v 1} ∈ 𝓝 z :=
  (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
private theorem chart_smooth {z : Point} (hz : 0 < z 1) : ContDiffAt ℝ ∞ chart z := by
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact (contDiff_apply ℝ ℝ (0:Fin 2)).contDiffAt
  · exact (contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt.log hz.ne'
private theorem pull_smooth {F : Field} (hF : ContDiff ℝ ∞ F) {z : Point} (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (pull F) z := hF.contDiffAt.comp z (chart_smooth hz)
private theorem D_smooth {F : Field} (hF : ContDiff ℝ ∞ F) (i : Fin 2) :
    ContDiff ℝ ∞ (D i F) := (hF.fderiv_right (by simp)).clm_apply contDiff_const

private theorem chart_first {F : Field} (hF : ContDiff ℝ ∞ F) {z : Point} (hz : 0 < z 1)
    (i : Fin 2) : D i (pull F) z=(if i=0 then 1 else (z 1:ℂ)⁻¹)*D i F (chart z) := by
  let dc : Point →L[ℝ] Point := ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj 0,(z 1)⁻¹ • ContinuousLinearMap.proj 1]
  have hchart : HasFDerivAt chart dc z := by
    apply hasFDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact hasFDerivAt_apply (𝕜 := ℝ) 0 z
    · exact (hasFDerivAt_apply (𝕜 := ℝ) 1 z).log hz.ne'
  have hc := ((hF.differentiable (by simp) (chart z)).hasFDerivAt).comp z hchart
  change HasFDerivAt (pull F) _ z at hc
  change fderiv ℝ (pull F) z (Pi.single i 1)=_
  rw [hc.fderiv]
  change (fderiv ℝ F (chart z)) (dc (Pi.single i 1))=_
  have he : dc (Pi.single i 1)=(if i=0 then 1 else (z 1)⁻¹) • Pi.single i 1 := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [dc]
  rw [he,map_smul]
  fin_cases i <;> simp [D,coordDeriv,Complex.real_smul]

private theorem chart_second_zero {F : Field} (hF : ContDiff ℝ ∞ F)
    {z : Point} (hz : 0 < z 1) : D 0 (D 0 (pull F)) z=D 0 (D 0 F) (chart z) := by
  have he : D 0 (pull F)=ᶠ[𝓝 z] pull (D 0 F) := by
    filter_upwards [positive_nhds hz] with v hv
    simpa only [ite_true,one_mul,pull] using chart_first hF hv 0
  change fderiv ℝ (D 0 (pull F)) z (Pi.single 0 1)=_
  rw [he.fderiv_eq]
  exact (chart_first (D_smooth hF 0) hz 0).trans (by simp)

private theorem chart_second_one {F : Field} (hF : ContDiff ℝ ∞ F)
    {z : Point} (hz : 0 < z 1) :
    (z 1:ℂ)^2*D 1 (D 1 (pull F)) z=D 1 (D 1 F) (chart z)-D 1 F (chart z) := by
  have he : D 1 (pull F)=ᶠ[𝓝 z] fun v => (v 1:ℂ)⁻¹*pull (D 1 F) v := by
    filter_upwards [positive_nhds hz] with v hv
    simpa only [show ¬(1:Fin 2)=0 by decide,if_false,pull] using chart_first hF hv 1
  have hn : (z 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hi : HasFDerivAt (fun v : Point => (v 1:ℂ)⁻¹)
      ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).smulRight (-(z 1:ℂ)⁻¹^2)) z := by
    have hy := Complex.ofRealCLM.hasFDerivAt.comp z
      ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt)
    have h := (hasDerivAt_inv hn).comp_hasFDerivAt z hy
    convert! h using 1
    ext v
    simp [Complex.real_smul,smul_eq_mul]
    ring
  have hd : D 1 (fun v : Point => (v 1:ℂ)⁻¹) z= -(z 1:ℂ)⁻¹^2 := by
    change fderiv ℝ _ z (Pi.single 1 1)=_
    rw [hi.fderiv]
    simp
  have hD := (pull_smooth (D_smooth hF 1) hz).differentiableAt (by simp)
  change (z 1:ℂ)^2*fderiv ℝ (D 1 (pull F)) z (Pi.single 1 1)=_
  rw [he.fderiv_eq]
  change (z 1:ℂ)^2*D 1 (fun v : Point => (v 1:ℂ)⁻¹*pull (D 1 F) v) z=_
  have hp : D 1 (fun v : Point => (v 1:ℂ)⁻¹*pull (D 1 F) v) z=
      D 1 (fun v : Point => (v 1:ℂ)⁻¹) z*pull (D 1 F) z+(z 1:ℂ)⁻¹*D 1 (pull (D 1 F)) z :=
    coordDeriv_mul hi.differentiableAt hD 1
  rw [hp,hd,chart_first (D_smooth hF 1) hz 1]
  simp only [show ¬(1:Fin 2)=0 by decide,if_false,pull]
  field_simp [hn]
  ring

/-- Genuine height-coordinate Laplacian of every smooth logarithmic source field. -/
private theorem pull_laplacian {F : Field} (hF : ContDiff ℝ ∞ F) {z : Point} (hz : 0 < z 1) :
    L (pull F) z=(z 1:ℂ)^2*D 0 (D 0 F) (chart z)+D 1 (D 1 F) (chart z)-D 1 F (chart z) := by
  change (z 1:ℂ)^2*(D 0 (D 0 (pull F)) z+D 1 (D 1 (pull F)) z)=_
  rw [mul_add,chart_second_zero hF hz,chart_second_one hF hz]
  ring


private theorem slice_first {f : Field} (hf : ContDiff ℝ ∞ f) (i : Fin 2) (p : Point) :
    deriv (fun x => f (Function.update p i x)) (p i)=D i f p := by
  have hi : HasDerivAt (fun x : ℝ => Function.update p i x) (Pi.single i 1) (p i) := by
    apply hasDerivAt_pi.mpr
    intro j
    by_cases h : j=i
    · subst j
      simpa using! hasDerivAt_id (p i)
    · simpa [h] using! hasDerivAt_const (p i) (p j)
  have hF : HasFDerivAt f (fderiv ℝ f p) (Function.update p i (p i)) := by
    simpa only [Function.update_eq_self] using! (hf.differentiable (by simp) p).hasFDerivAt
  simpa [D,coordDeriv] using! (hF.comp_hasDerivAt (p i) hi).deriv
private theorem slice_second {f : Field} (hf : ContDiff ℝ ∞ f) (i : Fin 2) (p : Point) :
    deriv (deriv (fun x => f (Function.update p i x))) (p i)=D i (D i f) p := by
  have he : deriv (fun x => f (Function.update p i x))=fun x => D i f (Function.update p i x) := by
    funext x
    simpa using! slice_first hf i (Function.update p i x)
  rw [he,slice_first (D_smooth hf i)]

private theorem mean_base_smooth (q : XiZeroCopy) (d : ℝ) :
    ContDiff ℝ ∞ (fun z : Point => mean q d (z 0) (z 1)) := by
  have hm : ContDiff ℝ ∞ (fun v : ℝ × ℝ × ℝ => mean q v.1 v.2.1 v.2.2) :=
    D4BMNativeResponse.nativeMean_joint_smooth q
  have h := hm.comp (show ContDiff ℝ ∞ (fun z : Point => (d,z 0,z 1)) by fun_prop)
  simpa only [Function.comp_def] using! h

private theorem circle_laplacian (q : XiZeroCopy) (d x k : ℝ) :
    D4BMHorizon.scalarLaplacian (circleField q d) ![x,Real.exp k] =
      (Real.exp k:ℂ)^2*deriv (deriv (fun r => mean q d r k)) x+
        deriv (deriv (fun r => mean q d x r)) k-deriv (fun r => mean q d x r) k := by
  let F : Field := fun z => mean q d (z 0) (z 1)
  have hf : ContDiff ℝ ∞ F := mean_base_smooth q d
  have h0 (t : ℝ) : Function.update (![x,k]:Point) 0 t=![t,k] := by
    ext i; fin_cases i <;> simp
  have h1 (t : ℝ) : Function.update (![x,k]:Point) 1 t=![x,t] := by
    ext i; fin_cases i <;> simp
  have hx := slice_second hf 0 ![x,k]
  have hk := slice_first hf 1 ![x,k]
  have hk2 := slice_second hf 1 ![x,k]
  simp only [h0,h1,F,Matrix.cons_val] at hx hk hk2
  have h := pull_laplacian hf (z := ![x,Real.exp k]) (Real.exp_pos k)
  rw [D4BMHorizon.scalarLaplacian_eq _ _ (Real.exp_pos k)]
  change L (pull F) ![x,Real.exp k]=_ 
  simpa only [chart,Matrix.cons_val,Real.log_exp,F,← hx,← hk,← hk2] using h

theorem original_circle_darboux (q : XiZeroCopy) (d x k : ℝ) :
    (Real.sinh d:ℂ)^2*deriv (deriv (fun r => mean q r x k)) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv (fun r => mean q r x k) d =
      (Real.sinh d:ℂ)^2*D4BMHorizon.scalarLaplacian (circleField q d) ![x,Real.exp k] := by
  rw [circle_laplacian]
  exact mean_darboux q d x k

private def kernelFirst (a : ℂ) (d : ℝ) : ℂ :=
  (Real.sinh d:ℂ)*legendreKernelFirst (-a) (Real.cosh d)
private def kernelSecond (a : ℂ) (d : ℝ) : ℂ :=
  (Real.cosh d:ℂ)*legendreKernelFirst (-a) (Real.cosh d)+
    (Real.sinh d:ℂ)^2*legendreKernelSecond (-a) (Real.cosh d)
private theorem kernel_derivatives (a : ℂ) (d : ℝ) :
    HasDerivAt (powerCircle a) (kernelFirst a d) d ∧
    HasDerivAt (kernelFirst a) (kernelSecond a d) d := by
  obtain ⟨h,h1⟩ := legendreKernel_derivatives (-a) (Real.cosh_pos d)
  have he : powerCircle a=fun r => legendreKernel (-a) (Real.cosh r) :=
    funext (powerCircle_eq_legendre a)
  have hp : HasDerivAt (powerCircle a) (kernelFirst a d) d := by
    rw [he]
    simpa only [kernelFirst,Function.comp_def,Complex.real_smul] using!
      h.scomp d (Real.hasDerivAt_cosh d)
  refine ⟨hp,?_⟩
  have hg : HasDerivAt (fun r => legendreKernelFirst (-a) (Real.cosh r))
      ((Real.sinh d:ℂ)*legendreKernelSecond (-a) (Real.cosh d)) d := by
    simpa only [Function.comp_def,Complex.real_smul] using h1.scomp d (Real.hasDerivAt_cosh d)
  apply (((Real.hasDerivAt_sinh d).ofReal_comp).mul hg).congr_deriv
  dsimp [kernelSecond]
  ring
private theorem kernel_equation (a : ℂ) (d : ℝ) :
    (Real.sinh d:ℂ)^2*kernelSecond a d+(Real.sinh d:ℂ)*(Real.cosh d:ℂ)*kernelFirst a d =
      a*(a-1)*(Real.sinh d:ℂ)^2*powerCircle a d := by
  have he := legendreKernel_equation (-a) (Real.cosh_pos d)
  have hc : (Real.cosh d:ℂ)^2-(Real.sinh d:ℂ)^2=1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq d
  rw [powerCircle_eq_legendre]
  dsimp [kernelFirst,kernelSecond]
  linear_combination (Real.sinh d:ℂ)^2*he-
    (Real.sinh d:ℂ)^2*legendreKernelSecond (-a) (Real.cosh d)*hc

private def coeffFirst (q : XiZeroCopy) (d : ℝ) (i : Fin 3) : ℂ :=
  principalAmplitude q i*kernelFirst (principalExponent q i) d
private def coeffSecond (q : XiZeroCopy) (d : ℝ) (i : Fin 3) : ℂ :=
  principalAmplitude q i*kernelSecond (principalExponent q i) d
private theorem coeff_derivatives (q : XiZeroCopy) (d : ℝ) (i : Fin 3) :
    HasDerivAt (fun r => coefficient q r i) (coeffFirst q d i) d ∧
    HasDerivAt (fun r => coeffFirst q r i) (coeffSecond q d i) d :=
  ⟨((kernel_derivatives (principalExponent q i) d).1).const_mul _,
    ((kernel_derivatives (principalExponent q i) d).2).const_mul _⟩
private theorem coeff_equation (q : XiZeroCopy) (d : ℝ) (i : Fin 3) :
    (Real.sinh d:ℂ)^2*coeffSecond q d i+(Real.sinh d:ℂ)*(Real.cosh d:ℂ)*coeffFirst q d i =
      (Real.sinh d:ℂ)^2*principalExponent q i*(principalExponent q i-1)*coefficient q d i := by
  have h := kernel_equation (principalExponent q i) d
  dsimp [coeffFirst,coeffSecond,coefficient]
  linear_combination principalAmplitude q i*h

private theorem circle_smooth (a : ℂ) : ContDiff ℝ ∞ (powerCircle a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro d
  have h := (D4BMCausalSourceKernel.legendre_contDiffAt (-a) (Real.cosh_pos d)).comp d
    Real.contDiff_cosh.contDiffAt
  simpa only [Function.comp_def,← powerCircle_eq_legendre] using h

private theorem residualField_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (residualField q) := by
  have hm : ContDiff ℝ ∞ (fun p : Fin 3 → ℝ => mean q (p 0) (p 1) (p 2)) := by
    have hc : ContDiff ℝ ∞ (fun p : Fin 3 → ℝ => (p 0,p 1,p 2)) := by fun_prop
    have h := (D4BMNativeResponse.nativeMean_joint_smooth q).comp hc
    exact h
  apply hm.sub
  apply ContDiff.sum
  intro i _
  have hc : ContDiff ℝ ∞ (fun p : Fin 3 → ℝ => coefficient q (p 0) i) :=
    contDiff_const.mul ((circle_smooth _).comp (contDiff_apply ℝ ℝ (0:Fin 3)))
  exact hc.mul ((powerCutoffHeight_smooth _).comp
    (Real.contDiff_exp.comp (contDiff_apply ℝ ℝ (2:Fin 3))))

private theorem jet_smooth {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (word : List (Fin 3)) : ContDiff ℝ ∞ (nativeJet word f) := by
  induction word with
  | nil => exact hf
  | cons i word ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const


private theorem residualJet_radius_hasDerivAt (q : XiZeroCopy) (word : List (Fin 3))
    (x k d : ℝ) :
    HasDerivAt (fun t => nativeJet word (residualField q) ![t,x,k])
      (nativeJet (0::word) (residualField q) ![d,x,k]) d := by
  have hi : HasDerivAt (fun t : ℝ => (![t,x,k] : Fin 3 → ℝ)) (Pi.single 0 1) d := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using! hasDerivAt_id d
    · simpa using! hasDerivAt_const d x
    · simpa using! hasDerivAt_const d k
  have hf := ((jet_smooth (residualField_smooth q) word).differentiable (by simp) ![d,x,k]).hasFDerivAt
  exact hf.comp_hasDerivAt d hi


private theorem mean_radius_zero_decomposition (q : XiZeroCopy) (d x k : ℝ) :
    mean q d x k=nativeJet [] (residualField q) ![d,x,k]+
      ∑ i : Fin 3, coefficient q d i*powerCutoffHeight (principalExponent q i) (Real.exp k) := by
  simp only [nativeJet,residualField,Matrix.cons_val,sub_add_cancel]

private theorem mean_radius_first_decomposition (q : XiZeroCopy) (d x k : ℝ) :
    deriv (fun r => mean q r x k) d=nativeJet [0] (residualField q) ![d,x,k]+
      ∑ i : Fin 3, coeffFirst q d i*powerCutoffHeight (principalExponent q i) (Real.exp k) := by
  have hr := residualJet_radius_hasDerivAt q [] x k d
  have hp := HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    ((coeff_derivatives q d i).1).mul_const (powerCutoffHeight (principalExponent q i) (Real.exp k)))
  have he : (fun r => mean q r x k)=fun r => nativeJet [] (residualField q) ![r,x,k]+
      ∑ i : Fin 3, coefficient q r i*powerCutoffHeight (principalExponent q i) (Real.exp k) :=
    funext (fun r => mean_radius_zero_decomposition q r x k)
  rw [he]
  exact (hr.add hp).deriv

private theorem mean_radius_second_decomposition (q : XiZeroCopy) (d x k : ℝ) :
    deriv (deriv (fun r => mean q r x k)) d=nativeJet [0,0] (residualField q) ![d,x,k]+
      ∑ i : Fin 3, coeffSecond q d i*powerCutoffHeight (principalExponent q i) (Real.exp k) := by
  have hr := residualJet_radius_hasDerivAt q [0] x k d
  have hp := HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    ((coeff_derivatives q d i).2).mul_const (powerCutoffHeight (principalExponent q i) (Real.exp k)))
  have he : deriv (fun r => mean q r x k)=fun r => nativeJet [0] (residualField q) ![r,x,k]+
      ∑ i : Fin 3, coeffFirst q r i*powerCutoffHeight (principalExponent q i) (Real.exp k) :=
    funext (fun r => mean_radius_first_decomposition q r x k)
  rw [he]
  exact (hr.add hp).deriv

private def defectCoeff (q : XiZeroCopy) (d : ℝ) (i : Fin 3) : ℂ :=
  (Real.sinh d:ℂ)^2*coeffSecond q d i+
    (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*coeffFirst q d i-
    (Real.sinh d:ℂ)^2*readerEigenvalue q*coefficient q d i
private theorem gap_eigenvalue (q : XiZeroCopy) (i : Fin 3) :
    physicalAngularGap q q i=principalExponent q i*(principalExponent q i-1)-readerEigenvalue q := by
  rw [physicalAngularGap_self_indicial,readerEigenvalue_eq,physicalAngularParameter_eq]
  ring
private theorem defectCoeff_eq_gap (q : XiZeroCopy) (d : ℝ) (i : Fin 3) :
    defectCoeff q d i=(Real.sinh d:ℂ)^2*physicalAngularGap q q i*coefficient q d i := by
  rw [defectCoeff,coeff_equation,gap_eigenvalue]
  ring

private def residualDefect (q : XiZeroCopy) (d : ℝ) (z : UpperHalfPlane) : ℂ :=
  (Real.sinh d:ℂ)^2*nativeJet [0,0] (residualField q) ![d,z.re,Real.log z.im]+
    (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*nativeJet [0] (residualField q) ![d,z.re,Real.log z.im]-
    (Real.sinh d:ℂ)^2*readerEigenvalue q*nativeJet [] (residualField q) ![d,z.re,Real.log z.im]

private theorem original_defect_decomposition (q : XiZeroCopy) (d : ℝ) (z : UpperHalfPlane) :
    (Real.sinh d:ℂ)^2*scalarEquationDefect q d (coordinates z) =
      residualDefect q d z+∑ i : Fin 3, defectCoeff q d i*cutoffPower (principalExponent q i) (coordinates z) := by
  have hm := original_circle_darboux q d z.re (Real.log z.im)
  rw [mean_radius_first_decomposition,mean_radius_second_decomposition,Real.exp_log z.im_pos] at hm
  have hz : circleField q d (coordinates z)=mean q d z.re (Real.log z.im) := rfl
  have hcp (i : Fin 3) : powerCutoffHeight (principalExponent q i) z.im=
      cutoffPower (principalExponent q i) (coordinates z) := by
    simp only [powerCutoffHeight,cutoffPower,coordinates,cutoff,Matrix.cons_val]
  simp only [hcp] at hm
  rw [show (![z.re,z.im] : Point)=coordinates z from rfl] at hm
  unfold scalarEquationDefect
  rw [mul_sub,← readerEigenvalue_eq,← hm,hz,mean_radius_zero_decomposition]
  simp only [Real.exp_log z.im_pos,hcp]
  have hs :
      (Real.sinh d:ℂ)^2*(∑ i : Fin 3, coeffSecond q d i*cutoffPower (principalExponent q i) (coordinates z))+
        (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*(∑ i : Fin 3, coeffFirst q d i*cutoffPower (principalExponent q i) (coordinates z))-
        (Real.sinh d:ℂ)^2*readerEigenvalue q*(∑ i : Fin 3, coefficient q d i*cutoffPower (principalExponent q i) (coordinates z))=
      ∑ i : Fin 3, defectCoeff q d i*cutoffPower (principalExponent q i) (coordinates z) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold defectCoeff
    ring
  dsimp only [residualDefect]
  linear_combination hs

private theorem residualDefect_integrable (q : XiZeroCopy) (d : Ici (0:ℝ)) :
    Integrable (fun z => scalar (physicalAngularParameter q) (coordinates z)*residualDefect q d z) measure := by
  have h2 := (residualJet_scalar_integrable q [0,0] d).const_mul ((Real.sinh d:ℂ)^2)
  have h1 := (residualJet_scalar_integrable q [0] d).const_mul ((Real.sinh d:ℂ)*(Real.cosh d:ℂ))
  have h0 := (residualJet_scalar_integrable q [] d).const_mul ((Real.sinh d:ℂ)^2*readerEigenvalue q)
  apply ((h2.add h1).sub h0).congr
  filter_upwards with z
  dsimp [residualDefect]
  ring

private theorem residualDefect_integral (q : XiZeroCopy) (d : Ici (0:ℝ)) :
    (∫ z, scalar (physicalAngularParameter q) (coordinates z)*residualDefect q d z ∂measure) =
      (Real.sinh d:ℂ)^2*residualPeriodJet q [0,0] d+
        (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*residualPeriodJet q [0] d-
        (Real.sinh d:ℂ)^2*readerEigenvalue q*residualPeriodJet q [] d := by
  have h2 := (residualJet_scalar_integrable q [0,0] d).const_mul ((Real.sinh d:ℂ)^2)
  have h1 := (residualJet_scalar_integrable q [0] d).const_mul ((Real.sinh d:ℂ)*(Real.cosh d:ℂ))
  have h0 := (residualJet_scalar_integrable q [] d).const_mul ((Real.sinh d:ℂ)^2*readerEigenvalue q)
  have he : (fun z => scalar (physicalAngularParameter q) (coordinates z)*residualDefect q d z) =
      fun z => (Real.sinh d:ℂ)^2*(scalar (physicalAngularParameter q) (coordinates z)*
        nativeJet [0,0] (residualField q) ![d,z.re,Real.log z.im])+
        (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*(scalar (physicalAngularParameter q) (coordinates z)*
          nativeJet [0] (residualField q) ![d,z.re,Real.log z.im])-
        (Real.sinh d:ℂ)^2*readerEigenvalue q*(scalar (physicalAngularParameter q) (coordinates z)*
          nativeJet [] (residualField q) ![d,z.re,Real.log z.im]) := by
    funext z
    unfold residualDefect
    ring
  have hsub := integral_sub (h2.add h1) h0
  simp only [Pi.add_apply] at hsub
  rw [he,hsub,integral_add h2 h1]
  simp only [integral_const_mul,residualPeriodJet]

private def correctionFirst (q : XiZeroCopy) (d : ℝ) : ℂ :=
  ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
    physicalAngularGap q q i*coeffFirst q d i
private def correctionSecond (q : XiZeroCopy) (d : ℝ) : ℂ :=
  ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
    physicalAngularGap q q i*coeffSecond q d i
private theorem correction_derivatives (q : XiZeroCopy) (d : ℝ) :
    HasDerivAt (correction q) (correctionFirst q d) d ∧
    HasDerivAt (correctionFirst q) (correctionSecond q d) d := by
  constructor
  · exact HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      ((coeff_derivatives q d i).1).const_mul _)
  · exact HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      ((coeff_derivatives q d i).2).const_mul _)

/-- The first derivative of the actual period, extended through the original radius-zero datum. -/
def periodFirst (q : XiZeroCopy) (d : ℝ) : ℂ :=
  residualPeriodJet q [0] d-correctionFirst q d
/-- The corresponding second radius derivative on the positive-radius chart. -/
def periodSecond (q : XiZeroCopy) (d : ℝ) : ℂ :=
  residualPeriodJet q [0,0] d-correctionSecond q d

theorem original_period_derivatives (q : XiZeroCopy) (d : ℝ) (hd : 0 < d) :
    HasDerivAt (period q) (periodFirst q d) d ∧
    HasDerivAt (periodFirst q) (periodSecond q d) d := by
  constructor
  · have h := period_hasDerivAt q d hd
    rw [(correction_derivatives q d).1.deriv] at h
    exact h
  · exact (residualPeriodJet_hasDerivAt q [0] d hd).sub (correction_derivatives q d).2

private theorem restored_defect_integral (q : XiZeroCopy) (d : Ici (0:ℝ)) :
    (∫ z, scalar (physicalAngularParameter q) (coordinates z)*residualDefect q d z ∂measure)-
      (∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
        physicalAngularGap q q i*defectCoeff q d i) =
      (Real.sinh d:ℂ)^2*periodSecond q d+(Real.sinh d:ℂ)*(Real.cosh d:ℂ)*periodFirst q d-
        (Real.sinh d:ℂ)^2*readerEigenvalue q*period q d := by
  rw [residualDefect_integral,period_eq_residualJet_sub]
  unfold periodFirst periodSecond correctionFirst correctionSecond correction
  have hs : (∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
        physicalAngularGap q q i*defectCoeff q d i) =
      (Real.sinh d:ℂ)^2*(∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
        physicalAngularGap q q i*coeffSecond q d i)+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*(∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
        physicalAngularGap q q i*coeffFirst q d i)-
      (Real.sinh d:ℂ)^2*readerEigenvalue q*(∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
        physicalAngularGap q q i*coefficient q d i) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold defectCoeff
    ring
  rw [hs]
  ring

private theorem defect_counterterm (q : XiZeroCopy) (d Y : ℝ) :
    principalCounterterm q (defectCoeff q d) Y =
      (Real.sinh d:ℂ)^2*principalCounterterm q
        (fun i => physicalAngularGap q q i*coefficient q d i) Y := by
  unfold principalCounterterm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [defectCoeff_eq_gap]
  ring

/-- The original regularized period solves the reader's radial Darboux equation. -/
theorem original_period_equation (q : XiZeroCopy) (d : Ici (0:ℝ)) :
    (Real.sinh d:ℂ)^2*periodSecond q d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*periodFirst q d =
      (Real.sinh d:ℂ)^2*readerEigenvalue q*period q d := by
  let T (Y : ℝ) := truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
    ((Real.sinh d:ℂ)^2*scalarEquationDefect q d (coordinates z))) Y-principalCounterterm q (defectCoeff q d) Y
  have hr := (integrable_residual_restoration q (residualDefect q d) (defectCoeff q d)
    (residualDefect_integrable q d)).comp Real.tendsto_exp_atTop
  rw [restored_defect_integral] at hr
  have hT (Y : ℝ) : T Y =
      truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        (residualDefect q d z+∑ i : Fin 3, defectCoeff q d i*cutoffPower (principalExponent q i) (coordinates z))) Y-
        principalCounterterm q (defectCoeff q d) Y := by
    dsimp only [T]
    congr 1
    unfold truncatedIntegral
    apply integral_congr_ae
    filter_upwards with z
    rw [original_defect_decomposition]
  have hrest : Tendsto (fun k => T (Real.exp k)) atTop
      (𝓝 ((Real.sinh d:ℂ)^2*periodSecond q d+
        (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*periodFirst q d-
        (Real.sinh d:ℂ)^2*readerEigenvalue q*period q d)) :=
    hr.congr' (Eventually.of_forall (fun k => (hT (Real.exp k)).symm))
  have h0 : Tendsto (fun k : ℝ =>
      truncatedIntegral (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
        scalarEquationDefect q d (coordinates z)) (Real.exp k)-
        principalCounterterm q (fun i => physicalAngularGap q q i*coefficient q d i) (Real.exp k))
      atTop (𝓝 0) := by
    simpa only [zero_mul,Complex.exp_zero,one_mul,D4BMGlobalAngularResponse.scalar,
      D4BMLiteralCusp.scalar,coordinates,Matrix.cons_val] using
      original_angular_measure_green_finitePart q d 0
  have hscaled (Y : ℝ) : T Y=(Real.sinh d:ℂ)^2*
      (truncatedIntegral (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
        scalarEquationDefect q d (coordinates z)) Y-
        principalCounterterm q (fun i => physicalAngularGap q q i*coefficient q d i) Y) := by
    dsimp only [T]
    rw [defect_counterterm]
    have he : (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
        ((Real.sinh d:ℂ)^2*scalarEquationDefect q d (coordinates z))) =
        fun z => (Real.sinh d:ℂ)^2*(scalar (physicalAngularParameter q) (coordinates z)*
          scalarEquationDefect q d (coordinates z)) := by funext z; ring
    rw [he]
    unfold truncatedIntegral
    rw [integral_const_mul]
    ring
  have hz : Tendsto (fun k => T (Real.exp k)) atTop (𝓝 0) := by
    have h := h0.const_mul ((Real.sinh d:ℂ)^2)
    simp only [mul_zero] at h
    exact h.congr' (Eventually.of_forall (fun k => (hscaled (Real.exp k)).symm))
  have he := tendsto_nhds_unique hrest hz
  linear_combination he

private theorem period_continuousOn (q : XiZeroCopy) : ContinuousOn (period q) (Ici (0:ℝ)) := by
  intro d hd
  change 0 ≤ d at hd
  rcases eq_or_lt_of_le hd with rfl | hd
  · exact period_continuousAt_zero q
  · exact (original_period_derivatives q d hd).1.continuousAt.continuousWithinAt
private theorem periodFirst_continuousOn (q : XiZeroCopy) : ContinuousOn (periodFirst q) (Ici (0:ℝ)) := by
  intro d hd
  change 0 ≤ d at hd
  rcases eq_or_lt_of_le hd with rfl | hd
  · exact (residualPeriodJet_continuousAt_zero q [0]).sub
      (correction_derivatives q 0).2.continuousAt.continuousWithinAt
  · exact (original_period_derivatives q d hd).2.continuousAt.continuousWithinAt
private theorem kernel_continuous (a : ℂ) : Continuous (powerCircle a) :=
  continuous_iff_continuousAt.mpr (fun d => (kernel_derivatives a d).1.continuousAt)
private theorem kernelFirst_continuous (a : ℂ) : Continuous (kernelFirst a) :=
  continuous_iff_continuousAt.mpr (fun d => (kernel_derivatives a d).2.continuousAt)

private def periodWronskian (q : XiZeroCopy) (d : ℝ) : ℂ :=
  (Real.sinh d:ℂ)*(powerCircle (readerExponent q) d*periodFirst q d-
    kernelFirst (readerExponent q) d*period q d)
private theorem periodWronskian_derivative (q : XiZeroCopy) (d : ℝ) (hd : 0 < d) :
    HasDerivAt (periodWronskian q) 0 d := by
  obtain ⟨hp,hp1⟩ := original_period_derivatives q d hd
  obtain ⟨hk,hk1⟩ := kernel_derivatives (readerExponent q) d
  apply (((Real.hasDerivAt_sinh d).ofReal_comp).mul ((hk.mul hp1).sub (hk1.mul hp))).congr_deriv
  have hs : (Real.sinh d:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr (ne_of_gt hd))
  apply mul_left_cancel₀ hs
  have he := original_period_equation q ⟨d,hd.le⟩
  have hker := kernel_equation (readerExponent q) d
  dsimp only [readerEigenvalue] at he
  simp only [Pi.sub_apply,Pi.mul_apply]
  linear_combination powerCircle (readerExponent q) d*he-period q d*hker

private theorem periodWronskian_continuousOn (q : XiZeroCopy) (D : ℝ) :
    ContinuousOn (periodWronskian q) (Icc (0:ℝ) D) := by
  have hs : Continuous (fun d : ℝ => (Real.sinh d:ℂ)) := by fun_prop
  have hp : ContinuousOn (period q) (Icc (0:ℝ) D) :=
    (period_continuousOn q).mono (fun d hd => hd.1)
  have hp1 : ContinuousOn (periodFirst q) (Icc (0:ℝ) D) :=
    (periodFirst_continuousOn q).mono (fun d hd => hd.1)
  exact hs.continuousOn.mul
    (((kernel_continuous (readerExponent q)).continuousOn.mul hp1).sub
      ((kernelFirst_continuous (readerExponent q)).continuousOn.mul hp))
private theorem periodWronskian_zero (q : XiZeroCopy) (D : Ici (0:ℝ)) : periodWronskian q D=0 := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le D.property
    (periodWronskian_continuousOn q D)
    (fun d hd => periodWronskian_derivative q d hd.1) intervalIntegrable_const
  have h0 : periodWronskian q 0=0 := by simp [periodWronskian]
  simpa only [intervalIntegral.integral_zero,h0,sub_zero] using hi.symm

private theorem quotient_derivative (q : XiZeroCopy) (d : ℝ) (hd : 0 < d) :
    HasDerivAt (fun r => period q r/powerCircle (readerExponent q) r) 0 d := by
  have hp := (original_period_derivatives q d hd).1
  have hk := (kernel_derivatives (readerExponent q) d).1
  have hw := periodWronskian_zero q ⟨d,hd.le⟩
  have hs : (Real.sinh d:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr (ne_of_gt hd))
  change (Real.sinh d:ℂ)*(powerCircle (readerExponent q) d*periodFirst q d-
    kernelFirst (readerExponent q) d*period q d)=0 at hw
  have hz := (mul_eq_zero.mp hw).resolve_left hs
  apply (hp.fun_div hk (reader_powerCircle_ne_zero q d)).congr_deriv
  change (periodFirst q d*powerCircle (readerExponent q) d-
    period q d*kernelFirst (readerExponent q) d)/powerCircle (readerExponent q) d^2=0
  have he : periodFirst q d*powerCircle (readerExponent q) d-
    period q d*kernelFirst (readerExponent q) d=0 := by linear_combination hz
  rw [he,zero_div]

/-- The original full-source finite-part period is exactly its original zero-radius
coefficient times the unchanged physical reader kernel. -/
theorem original_circle_period (q : XiZeroCopy) (D : Ici (0:ℝ)) :
    period q D=physicalSelfSourceCoefficient q*powerCircle (readerExponent q) D := by
  have hc : ContinuousOn (fun r => period q r/powerCircle (readerExponent q) r) (Icc (0:ℝ) D) :=
    ((period_continuousOn q).mono (fun d hd => hd.1)).div
      (kernel_continuous (readerExponent q)).continuousOn (fun d _ => reader_powerCircle_ne_zero q d)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le D.property hc
    (fun d hd => quotient_derivative q d hd.1) intervalIntegrable_const
  have h0 : period q 0/powerCircle (readerExponent q) 0=physicalSelfSourceCoefficient q := by
    rw [period_zero,powerCircle_eq_legendre]
    simp only [Real.cosh_zero,legendreKernel_one,div_one]
  simp only [intervalIntegral.integral_zero,h0] at hi
  have he : period q D/powerCircle (readerExponent q) D=physicalSelfSourceCoefficient q := by
    linear_combination -hi
  exact (div_eq_iff (reader_powerCircle_ne_zero q D)).mp he

/-- The original height-cutoff scalar integral converges to the physical reader
kernel with its source-derived normalization and all original counterterms. -/
theorem original_circle_finitePart_kernel (q : XiZeroCopy) (d : Ici (0:ℝ)) :
    Tendsto (fun Y => truncatedIntegral (fun z =>
      scalar (physicalAngularParameter q) (coordinates z)*mean q d z.re (Real.log z.im)) Y-
        principalCounterterm q (coefficient q d) Y) atTop
      (𝓝 (physicalSelfSourceCoefficient q*powerCircle (readerExponent q) d)) := by
  rw [← original_circle_period q d]
  exact original_circle_finitePart q d

end RHTower.D4BMOriginalCircleEquation
