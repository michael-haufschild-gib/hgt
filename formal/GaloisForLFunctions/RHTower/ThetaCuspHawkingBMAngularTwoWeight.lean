import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularTwoTensor
import GaloisForLFunctions.RHTower.MaassWeightLift

/-!
# Modular weight of the original angular tensor remainder

The original scalar and its constructed shift-two inverse embed in the smooth
Maass function space. Their first and second ladder fields identify exactly with
the two tensor polarizations, including both derivatives of the height factor.
Automorphic invariance of the ladder expressions gives the original weight-four
modular transformation for each holomorphic polarization. No cusp condition or
vanishing assertion enters these transformation laws.
-/

open UpperHalfPlane Complex Set Filter Topology ModularGroup
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.MaassSmooth
open scoped ContDiff ComplexConjugate MatrixGroups
namespace RHTower.D4BMAngularTwoWeight
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMModularCore D4BMAngularTwo
noncomputable section
set_option autoImplicit false

/-- Differentiating automorphic invariance preserves both adjacent compact weights. -/
theorem weightLift_ladder_preserves (Γ : Subgroup SL2R) (m : ℤ) (f : FunctionSpace)
    (hf : weightLift m f ∈ automorphicFunctionSpace Γ) :
    weightLift (m+1) (raise m f) ∈ automorphicFunctionSpace Γ ∧
      weightLift (m-1) (lower m f) ∈ automorphicFunctionSpace Γ := by
  have heq (γ : Γ) (g : SL2R) (p : ℝ → SL2R) :
      (fun t => weightLift m f (((γ : SL2R)*g)*p t)) =
        (fun t => weightLift m f (g*p t)) := by
    funext t
    simpa only [mul_assoc] using hf γ (g*p t)
  have hstep (γ : Γ) (g : SL2R) :
      weightLift (m+1) (raise m f) ((γ : SL2R)*g) = weightLift (m+1) (raise m f) g ∧
      weightLift (m-1) (lower m f) ((γ : SL2R)*g) = weightLift (m-1) (lower m f) g := by
    have ha := weightLift_diagonal_hasDerivAt m f ((γ : SL2R)*g)
    have hb := weightLift_quarterDiagonal_hasDerivAt m f ((γ : SL2R)*g)
    rw [heq] at ha hb
    have ha' := ha.unique (weightLift_diagonal_hasDerivAt m f g)
    have hb' := hb.unique (weightLift_quarterDiagonal_hasDerivAt m f g)
    have hdiff :
        weightLift (m+1) (raise m f) ((γ : SL2R)*g) -
          weightLift (m-1) (lower m f) ((γ : SL2R)*g) =
        weightLift (m+1) (raise m f) g - weightLift (m-1) (lower m f) g :=
      mul_left_cancel₀ Complex.I_ne_zero hb'
    constructor
    · linear_combination (ha' + hdiff)/2
    · linear_combination (ha' - hdiff)/2
  exact ⟨fun γ g => (hstep γ g).1, fun γ g => (hstep γ g).2⟩

private theorem scalar_chartSmooth (q : XiZeroCopy) :
    ChartSmooth (fun z => scalar (D4BMGlobalAngularResponse.center q) (coordinates z)) := by
  have hC : ContDiff ℝ ∞ (fun z : ℂ => ![z.re,z.im]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  have hf : ContDiffOn ℝ ∞ (fun z : ℂ => scalar (D4BMGlobalAngularResponse.center q) ![z.re,z.im])
      {z : ℂ | 0 < z.im} :=
    (cuspLeg_contDiffOn .scalar (D4BMGlobalAngularResponse.center q)).comp hC.contDiffOn
      (fun _ hz => hz)
  intro z
  apply (hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw]
  rfl


/-- The actual original scalar in the smooth Maass function space. -/
def sourceFunction (q : XiZeroCopy) : FunctionSpace :=
  ⟨fun z => scalar (D4BMGlobalAngularResponse.center q) (coordinates z),
    (scalar_chartSmooth q).planar_contDiffOn⟩

/-- The constructed full shift-two inverse in the same smooth function space. -/
def responseFunction (q : XiZeroCopy) : FunctionSpace :=
  ⟨smoothFullResponse q,(smoothFullResponse_smooth q).planar_contDiffOn⟩

/-- Pointwise multiplication retains the complete smooth fields. -/
def productFunction (f g : FunctionSpace) : FunctionSpace :=
  ⟨fun z => f z*g z, f.property.mul g.property⟩

/-- The original integral matrix regarded as a real matrix. -/
def realMatrix (A : SL(2, ℤ)) : SL2R :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A

private theorem realMatrix_smul (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    realMatrix A • z = A • z := by
  rfl

/-- Original scalar invariance lifts to the actual group orbit. -/
theorem source_weight_zero (q : XiZeroCopy) (A : SL(2, ℤ)) (g : SL2R) :
    weightLift 0 (sourceFunction q) (realMatrix A*g) = weightLift 0 (sourceFunction q) g := by
  simp only [weightLift,realSphericalKTypeCharacter_apply,mul_zero,zpow_zero,mul_one,
    mul_smul,realMatrix_smul]
  exact xi_scalar_modular q A (g • UpperHalfPlane.I)

/-- The constructed full inverse has the same original group invariance. -/
theorem response_weight_zero (q : XiZeroCopy) (A : SL(2, ℤ)) (g : SL2R) :
    weightLift 0 (responseFunction q) (realMatrix A*g) = weightLift 0 (responseFunction q) g := by
  simp only [weightLift,realSphericalKTypeCharacter_apply,mul_zero,zpow_zero,mul_one,
    mul_smul,realMatrix_smul]
  exact smoothFullResponse_invariant q (QuotientGroup.mk A) (g • UpperHalfPlane.I)

/-- The image of the original integral modular group in the real group. -/
def modularRealGroup : Subgroup SL2R :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)).range

/-- The actual original source defines a weight-zero automorphic vector. -/
theorem source_automorphic (q : XiZeroCopy) :
    weightLift 0 (sourceFunction q) ∈ automorphicFunctionSpace modularRealGroup := by
  intro γ g
  have hγ : ∃ A : SL(2, ℤ), realMatrix A = (γ : SL2R) := γ.property
  obtain ⟨A,hA⟩ := hγ
  rw [← hA]
  exact source_weight_zero q A g

/-- The actual complete inverse defines a weight-zero automorphic vector. -/
theorem response_automorphic (q : XiZeroCopy) :
    weightLift 0 (responseFunction q) ∈ automorphicFunctionSpace modularRealGroup := by
  intro γ g
  have hγ : ∃ A : SL(2, ℤ), realMatrix A = (γ : SL2R) := γ.property
  obtain ⟨A,hA⟩ := hγ
  rw [← hA]
  exact response_weight_zero q A g

/-- Products add the literal compact weights. -/
theorem product_weightLift (m n : ℤ) (f h : FunctionSpace) (g : SL2R) :
    weightLift (m+n) (productFunction f h) g = weightLift m f g*weightLift n h g := by
  simp only [weightLift,productFunction,realSphericalKTypeCharacter_add]
  ring

/-- The product of actual automorphic fields has the summed weight. -/
theorem product_automorphic (m n : ℤ) (f h : FunctionSpace)
    (hf : weightLift m f ∈ automorphicFunctionSpace modularRealGroup)
    (hh : weightLift n h ∈ automorphicFunctionSpace modularRealGroup) :
    weightLift (m+n) (productFunction f h) ∈ automorphicFunctionSpace modularRealGroup := by
  intro γ g
  rw [product_weightLift,product_weightLift,hf γ g,hh γ g]

private theorem weightLift_add (m : ℤ) (f h : FunctionSpace) (g : SL2R) :
    weightLift m (f+h) g = weightLift m f g+weightLift m h g := by
  change (f (g • UpperHalfPlane.I)+h (g • UpperHalfPlane.I))*_ = _
  exact add_mul _ _ _

/-- The original tensor's negative compact-weight expression. -/
def lowerTensorFunction (q : XiZeroCopy) : FunctionSpace :=
  productFunction (lower 0 (sourceFunction q)) (lower 0 (sourceFunction q))+
    D4BMAngularTwoTensor.eigenvalue q • lower (-1) (lower 0 (responseFunction q))

/-- The original tensor's positive compact-weight expression. -/
def raiseTensorFunction (q : XiZeroCopy) : FunctionSpace :=
  productFunction (raise 0 (sourceFunction q)) (raise 0 (sourceFunction q))+
    D4BMAngularTwoTensor.eigenvalue q • raise 1 (raise 0 (responseFunction q))

/-- The entire constructed negative-weight tensor expression is automorphic. -/
theorem lowerTensorFunction_automorphic (q : XiZeroCopy) :
    weightLift (-2) (lowerTensorFunction q) ∈ automorphicFunctionSpace modularRealGroup := by
  have hs : weightLift (-1) (lower 0 (sourceFunction q)) ∈ automorphicFunctionSpace modularRealGroup := by
    simpa using (weightLift_ladder_preserves modularRealGroup 0 (sourceFunction q) (source_automorphic q)).2
  have hu : weightLift (-1) (lower 0 (responseFunction q)) ∈ automorphicFunctionSpace modularRealGroup := by
    simpa using (weightLift_ladder_preserves modularRealGroup 0 (responseFunction q) (response_automorphic q)).2
  have huu : weightLift (-2) (lower (-1) (lower 0 (responseFunction q))) ∈ automorphicFunctionSpace modularRealGroup := by
    simpa using (weightLift_ladder_preserves modularRealGroup (-1) (lower 0 (responseFunction q)) hu).2
  have hss : weightLift (-2) (productFunction (lower 0 (sourceFunction q)) (lower 0 (sourceFunction q))) ∈ automorphicFunctionSpace modularRealGroup := by
    simpa using product_automorphic (-1) (-1) _ _ hs hs
  intro γ g
  simp only [lowerTensorFunction,weightLift_add,weightLift_smul,Pi.smul_apply,smul_eq_mul]
  rw [hss γ g,huu γ g]

/-- The entire constructed positive-weight tensor expression is automorphic. -/
theorem raiseTensorFunction_automorphic (q : XiZeroCopy) :
    weightLift 2 (raiseTensorFunction q) ∈ automorphicFunctionSpace modularRealGroup := by
  have hs : weightLift 1 (raise 0 (sourceFunction q)) ∈ automorphicFunctionSpace modularRealGroup := by
    simpa using (weightLift_ladder_preserves modularRealGroup 0 (sourceFunction q) (source_automorphic q)).1
  have hu : weightLift 1 (raise 0 (responseFunction q)) ∈ automorphicFunctionSpace modularRealGroup := by
    simpa using (weightLift_ladder_preserves modularRealGroup 0 (responseFunction q) (response_automorphic q)).1
  have huu : weightLift 2 (raise 1 (raise 0 (responseFunction q))) ∈ automorphicFunctionSpace modularRealGroup := by
    simpa using (weightLift_ladder_preserves modularRealGroup 1 (raise 0 (responseFunction q)) hu).1
  have hss : weightLift 2 (productFunction (raise 0 (sourceFunction q)) (raise 0 (sourceFunction q))) ∈ automorphicFunctionSpace modularRealGroup := by
    simpa using product_automorphic 1 1 _ _ hs hs
  intro γ g
  simp only [raiseTensorFunction,weightLift_add,weightLift_smul,Pi.smul_apply,smul_eq_mul]
  rw [hss γ g,huu γ g]

private theorem first_jet (f : FunctionSpace) (F : (Fin 2 → ℝ) → ℂ)
    (hF : ∀ z : UpperHalfPlane, f z = F (coordinates z)) (i : Fin 2) (z : UpperHalfPlane) :
    directional (direction i) f z = ScalarTwoJet.coordDeriv i F (coordinates z) := by
  have he : ((f : UpperHalfPlane → ℂ) ∘ ofComplex) =ᶠ[𝓝 (z:ℂ)] F ∘ angularCoordinates := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,hF,coordinates,ofComplex_apply_of_im_pos hw]
    rfl
  rw [directional_apply,he.fderiv_eq,angularCoordinates_derivative]
  rfl

private theorem second_jet (f : FunctionSpace) (F : (Fin 2 → ℝ) → ℂ)
    (hF : ∀ z : UpperHalfPlane, f z = F (coordinates z)) (i j : Fin 2) (z : UpperHalfPlane) :
    directional (direction i) (directional (direction j) f) z =
      ScalarTwoJet.coordDeriv i (ScalarTwoJet.coordDeriv j F) (coordinates z) :=
  first_jet _ _ (fun w => first_jet f F hF j w) i z

private theorem lower_two (f : FunctionSpace) :
    lower (-1) (lower 0 f) =
      -height (height (directional 1 (directional 1 f)))+
      height (height (directional Complex.I (directional Complex.I f)))+
      (2*Complex.I) • height (height (directional 1 (directional Complex.I f)))+
      (2*Complex.I) • height (directional 1 f)+(2:ℂ) • height (directional Complex.I f) := by
  simp only [lower_apply,Int.cast_neg,Int.cast_one,Int.cast_zero,zero_smul,
    add_zero,map_sub,map_neg,X_X,Y_X,Y_Y]
  simp only [X_apply,Y_apply,directional_height_eq,
    Complex.one_im,Complex.ofReal_zero,zero_smul,add_zero,smul_smul]
  module

private theorem raise_two (f : FunctionSpace) :
    raise 1 (raise 0 f) =
      -height (height (directional 1 (directional 1 f)))+
      height (height (directional Complex.I (directional Complex.I f)))-
      (2*Complex.I) • height (height (directional 1 (directional Complex.I f)))-
      (2*Complex.I) • height (directional 1 f)+(2:ℂ) • height (directional Complex.I f) := by
  simp only [raise_apply,Int.cast_one,Int.cast_zero,zero_smul,one_smul,
    sub_zero,map_sub,X_X,Y_X,Y_Y]
  simp only [X_apply,Y_apply,directional_height_eq,
    Complex.one_im,Complex.ofReal_zero,zero_smul,add_zero]
  module

/-- The original complex automorphy denominator for a real modular matrix. -/
def matrixDenom (γ : SL2R) (z : UpperHalfPlane) : ℂ :=
  (γ 1 0 : ℂ)*(z:ℂ)+(γ 1 1 : ℂ)

private theorem orbit_phase_scaled (γ : SL2R) (z : UpperHalfPlane) :
    realSphericalKPhase (realIwasawaK (γ*z.toSL2R))*(Real.sqrt z.im : ℂ) =
      (Real.sqrt (γ • z).im : ℂ)*matrixDenom γ z := by
  have hy : (Real.sqrt z.im : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr z.im_pos)
  have hsq : (Real.sqrt z.im : ℂ)^2 = (z.im : ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt z.im_pos.le]
  rw [realIwasawaK_phase]
  have hb : (((realIwasawaB (γ*z.toSL2R) : realUpperBorel) : SL2R) 0 0 : ℂ) =
      (Real.sqrt (γ • z).im : ℂ) := by
    change (Real.sqrt ((γ*z.toSL2R) • UpperHalfPlane.I).im : ℂ) = _
    rw [mul_smul,UpperHalfPlane.toSL2R_smul_I]
  rw [hb]
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
    UpperHalfPlane.coe_toSL2R,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_one,mul_zero,add_zero,matrixDenom]
  rw [← Complex.re_add_im (z:ℂ)]
  simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  field_simp
  linear_combination (Real.sqrt (γ • z).im : ℂ)*Complex.I*(γ 1 0 : ℂ)*hsq

/-- Fourth powers of the actual compact phase retain the exact height ratio. -/
theorem orbit_phase_four (γ : SL2R) (z : UpperHalfPlane) :
    realSphericalKPhase (realIwasawaK (γ*z.toSL2R))^4*(z.im : ℂ)^2 =
      ((γ • z).im : ℂ)^2*matrixDenom γ z^4 := by
  have hy : (Real.sqrt z.im : ℂ)^2 = (z.im : ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt z.im_pos.le]
  have ht : (Real.sqrt (γ • z).im : ℂ)^2 = ((γ • z).im : ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (γ • z).im_pos.le]
  have he := congrArg (fun c : ℂ => c^4) (orbit_phase_scaled γ z)
  simp only [mul_pow,show (4:ℕ)=2*2 from rfl,pow_mul,hy,ht] at he
  simpa only [← pow_mul] using he

private theorem lower_tensor_value (f u : FunctionSpace) (F U : (Fin 2 → ℝ) → ℂ)
    (hF : ∀ z : UpperHalfPlane, f z = F (coordinates z))
    (hU : ∀ z : UpperHalfPlane, u z = U (coordinates z)) (μ : ℂ) (z : UpperHalfPlane) :
    (productFunction (lower 0 f) (lower 0 f) + μ • lower (-1) (lower 0 u)) z =
      -2*(z.im : ℂ)^2*(D4BMAngularTwoTensor.componentA F U μ (coordinates z)-
        Complex.I*D4BMAngularTwoTensor.componentB F U μ (coordinates z)) := by
  have hsx := first_jet f F hF 0 z
  have hsy := first_jet f F hF 1 z
  have hux := first_jet u U hU 0 z
  have huy := first_jet u U hU 1 z
  have hxx := second_jet u U hU 0 0 z
  have hyy := second_jet u U hU 1 1 z
  have hxy := second_jet u U hU 0 1 z
  change directional 1 f z = _ at hsx
  change directional Complex.I f z = _ at hsy
  change directional 1 u z = _ at hux
  change directional Complex.I u z = _ at huy
  change directional 1 (directional 1 u) z = _ at hxx
  change directional Complex.I (directional Complex.I u) z = _ at hyy
  change directional 1 (directional Complex.I u) z = _ at hxy
  rw [lower_two]
  simp only [lower_apply,Int.cast_zero,zero_smul,add_zero,X_apply,Y_apply]
  change (-(Complex.I*((z.im:ℂ)*directional 1 f z))-(z.im:ℂ)*directional Complex.I f z)*
    (-(Complex.I*((z.im:ℂ)*directional 1 f z))-(z.im:ℂ)*directional Complex.I f z)+
    μ*(-((z.im:ℂ)*((z.im:ℂ)*directional 1 (directional 1 u) z))+
      (z.im:ℂ)*((z.im:ℂ)*directional Complex.I (directional Complex.I u) z)+
      (2*Complex.I)*((z.im:ℂ)*((z.im:ℂ)*directional 1 (directional Complex.I u) z))+
      (2*Complex.I)*((z.im:ℂ)*directional 1 u z)+2*((z.im:ℂ)*directional Complex.I u z)) = _
  rw [hsx,hsy,hux,huy,hxx,hyy,hxy]
  simp only [D4BMAngularTwoTensor.componentA,D4BMAngularTwoTensor.componentB]
  have hy : (z.im:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  change _ = -2*(z.im:ℂ)^2*((_ - _)/2+μ*((_ - _)/2-(z.im:ℂ)⁻¹*_)-
    Complex.I*(_+μ*(_+(z.im:ℂ)⁻¹*_)))
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The negative compact weight is the original holomorphic tensor component. -/
theorem lowerTensorFunction_eq (q : XiZeroCopy) (z : UpperHalfPlane) :
    lowerTensorFunction q z = -2*(z.im:ℂ)^2*
      D4BMAngularTwoTensor.holomorphicPolarization q (z:ℂ) := by
  exact lower_tensor_value (sourceFunction q) (responseFunction q)
    (D4BMAngularTwoTensor.source q) (coordinateResponse q) (fun _ => rfl)
    (fun w => (coordinateResponse_coordinates q w).symm) _ z
private theorem raise_tensor_value (f u : FunctionSpace) (F U : (Fin 2 → ℝ) → ℂ)
    (hF : ∀ z : UpperHalfPlane, f z = F (coordinates z))
    (hU : ∀ z : UpperHalfPlane, u z = U (coordinates z)) (μ : ℂ) (z : UpperHalfPlane) :
    (productFunction (raise 0 f) (raise 0 f) + μ • raise 1 (raise 0 u)) z =
      -2*(z.im : ℂ)^2*(D4BMAngularTwoTensor.componentA F U μ (coordinates z)+
        Complex.I*D4BMAngularTwoTensor.componentB F U μ (coordinates z)) := by
  have hsx := first_jet f F hF 0 z
  have hsy := first_jet f F hF 1 z
  have hux := first_jet u U hU 0 z
  have huy := first_jet u U hU 1 z
  have hxx := second_jet u U hU 0 0 z
  have hyy := second_jet u U hU 1 1 z
  have hxy := second_jet u U hU 0 1 z
  change directional 1 f z = _ at hsx
  change directional Complex.I f z = _ at hsy
  change directional 1 u z = _ at hux
  change directional Complex.I u z = _ at huy
  change directional 1 (directional 1 u) z = _ at hxx
  change directional Complex.I (directional Complex.I u) z = _ at hyy
  change directional 1 (directional Complex.I u) z = _ at hxy
  rw [raise_two]
  simp only [raise_apply,Int.cast_zero,zero_smul,sub_zero,X_apply,Y_apply]
  change (Complex.I*((z.im:ℂ)*directional 1 f z)-(z.im:ℂ)*directional Complex.I f z)*
    (Complex.I*((z.im:ℂ)*directional 1 f z)-(z.im:ℂ)*directional Complex.I f z)+
    μ*(-((z.im:ℂ)*((z.im:ℂ)*directional 1 (directional 1 u) z))+
      (z.im:ℂ)*((z.im:ℂ)*directional Complex.I (directional Complex.I u) z)-
      (2*Complex.I)*((z.im:ℂ)*((z.im:ℂ)*directional 1 (directional Complex.I u) z))-
      (2*Complex.I)*((z.im:ℂ)*directional 1 u z)+2*((z.im:ℂ)*directional Complex.I u z)) = _
  rw [hsx,hsy,hux,huy,hxx,hyy,hxy]
  simp only [D4BMAngularTwoTensor.componentA,D4BMAngularTwoTensor.componentB]
  have hy : (z.im:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  change _ = -2*(z.im:ℂ)^2*((_ - _)/2+μ*((_ - _)/2-(z.im:ℂ)⁻¹*_)+
    Complex.I*(_+μ*(_+(z.im:ℂ)⁻¹*_)))
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring


/-- The positive compact weight is the independent antiholomorphic tensor component. -/
theorem raiseTensorFunction_eq (q : XiZeroCopy) (z : UpperHalfPlane) :
    raiseTensorFunction q z = -2*(z.im:ℂ)^2*
      (D4BMAngularTwoTensor.defectA q (coordinates z)+
        Complex.I*D4BMAngularTwoTensor.defectB q (coordinates z)) := by
  exact raise_tensor_value (sourceFunction q) (responseFunction q)
    (D4BMAngularTwoTensor.source q) (coordinateResponse q) (fun _ => rfl)
    (fun w => (coordinateResponse_coordinates q w).symm) _ z

private theorem negative_two_orbit (f : FunctionSpace)
    (hf : weightLift (-2) f ∈ automorphicFunctionSpace modularRealGroup)
    (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    f (realMatrix A • z) = f z*realSphericalKPhase (realIwasawaK (realMatrix A*z.toSL2R))^4 := by
  have hA : realMatrix A ∈ modularRealGroup := ⟨A,rfl⟩
  have he := hf ⟨realMatrix A,hA⟩ z.toSL2R
  rw [weightLift_section] at he
  change f ((realMatrix A*z.toSL2R) • UpperHalfPlane.I)*
    realSphericalKPhase (realIwasawaK (realMatrix A*z.toSL2R))^((2:ℤ)*(-2)) = f z at he
  rw [mul_smul,UpperHalfPlane.toSL2R_smul_I] at he
  have hp := realSphericalKPhase_ne_zero (realIwasawaK (realMatrix A*z.toSL2R))
  norm_num only [show (2:ℤ)*(-2) = -(4:ℤ) from rfl,zpow_neg,zpow_natCast] at he
  calc
    f (realMatrix A • z) =
        (f (realMatrix A • z)*(realSphericalKPhase (realIwasawaK (realMatrix A*z.toSL2R))^4)⁻¹)*
          realSphericalKPhase (realIwasawaK (realMatrix A*z.toSL2R))^4 := by field_simp
    _ = _ := congrArg (fun c : ℂ => c*realSphericalKPhase (realIwasawaK (realMatrix A*z.toSL2R))^4) he

private theorem weight_four_of_negative_two (f : FunctionSpace) (H : ℂ → ℂ)
    (hf : weightLift (-2) f ∈ automorphicFunctionSpace modularRealGroup)
    (hH : ∀ z : UpperHalfPlane, f z = -2*(z.im:ℂ)^2*H (z:ℂ))
    (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    H ((realMatrix A • z : UpperHalfPlane):ℂ) = matrixDenom (realMatrix A) z^4*H (z:ℂ) := by
  have he := negative_two_orbit f hf A z
  rw [hH,hH] at he
  have hp := orbit_phase_four (realMatrix A) z
  have hy : (z.im:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  have ht : ((realMatrix A • z).im:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (realMatrix A • z).im_pos.ne'
  apply mul_left_cancel₀ (show (-2:ℂ)*((realMatrix A • z).im:ℂ)^2*(z.im:ℂ)^2 ≠ 0 by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)) (pow_ne_zero 2 hy))
  calc
    -2*((realMatrix A • z).im:ℂ)^2*(z.im:ℂ)^2*H ((realMatrix A • z : UpperHalfPlane):ℂ) =
        (-2*((realMatrix A • z).im:ℂ)^2*H ((realMatrix A • z : UpperHalfPlane):ℂ))*(z.im:ℂ)^2 := by ring
    _ = (-2*(z.im:ℂ)^2*H (z:ℂ)*realSphericalKPhase
        (realIwasawaK (realMatrix A*z.toSL2R))^4)*(z.im:ℂ)^2 := by rw [he]
    _ = (-2*(z.im:ℂ)^2*H (z:ℂ))*(realSphericalKPhase
        (realIwasawaK (realMatrix A*z.toSL2R))^4*(z.im:ℂ)^2) := by ring
    _ = _ := by rw [hp]; ring

/-- The actual holomorphic remainder transforms with the original weight-four denominator. -/
theorem holomorphicPolarization_weight_four (q : XiZeroCopy) (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    D4BMAngularTwoTensor.holomorphicPolarization q ((A • z : UpperHalfPlane):ℂ) =
      ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ))^4*
        D4BMAngularTwoTensor.holomorphicPolarization q (z:ℂ) := by
  have hd : matrixDenom (realMatrix A) z = ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ)) := rfl
  simpa only [realMatrix_smul,hd] using
    weight_four_of_negative_two (lowerTensorFunction q)
      (D4BMAngularTwoTensor.holomorphicPolarization q) (lowerTensorFunction_automorphic q)
      (lowerTensorFunction_eq q) A z
/-- Conjugation on the complete smooth Maass space. -/
def conjugateFunction (f : FunctionSpace) : FunctionSpace :=
  ⟨fun z => conj (f z),Complex.conjCLE.contDiff.comp_contDiffOn f.property⟩

private theorem weightLift_conjugate_two (f : FunctionSpace) (g : SL2R) :
    weightLift (-2) (conjugateFunction f) g = conj (weightLift 2 f g) := by
  have hn : ‖realSphericalKPhase (realIwasawaK g)‖ = 1 := by
    rw [Complex.norm_def,realSphericalKPhase_normSq,Real.sqrt_one]
  have hc := (Complex.inv_eq_conj hn).symm
  change conj (f (g • UpperHalfPlane.I))*realSphericalKPhase (realIwasawaK g)^((2:ℤ)*(-2)) =
    conj (f (g • UpperHalfPlane.I)*realSphericalKPhase (realIwasawaK g)^((2:ℤ)*2))
  rw [map_mul,map_zpow₀,hc]
  norm_num only [show (2:ℤ)*(-2) = -(4:ℤ) from rfl,show (2:ℤ)*2 = (4:ℤ) from rfl,
    zpow_neg,zpow_ofNat,inv_pow]

private theorem conjugate_raise_automorphic (q : XiZeroCopy) :
    weightLift (-2) (conjugateFunction (raiseTensorFunction q)) ∈
      automorphicFunctionSpace modularRealGroup := by
  intro γ g
  rw [weightLift_conjugate_two,weightLift_conjugate_two,
    raiseTensorFunction_automorphic q γ g]

/-- Conjugating the positive compact weight gives the second holomorphic polarization. -/
theorem conjugate_raise_eq (q : XiZeroCopy) (z : UpperHalfPlane) :
    conjugateFunction (raiseTensorFunction q) z = -2*(z.im:ℂ)^2*
      D4BMAngularTwoTensor.conjugatePolarization q (z:ℂ) := by
  change conj (raiseTensorFunction q z) = _
  rw [raiseTensorFunction_eq]
  simp only [map_mul,map_neg,map_pow,map_add,map_ofNat,Complex.conj_ofReal,Complex.conj_I,
    neg_mul]
  rfl

/-- Both original complex polarizations have the same holomorphic weight four. -/
theorem conjugatePolarization_weight_four (q : XiZeroCopy) (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    D4BMAngularTwoTensor.conjugatePolarization q ((A • z : UpperHalfPlane):ℂ) =
      ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ))^4*
        D4BMAngularTwoTensor.conjugatePolarization q (z:ℂ) := by
  have hd : matrixDenom (realMatrix A) z = ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ)) := rfl
  simpa only [realMatrix_smul,hd] using
    weight_four_of_negative_two (conjugateFunction (raiseTensorFunction q))
      (D4BMAngularTwoTensor.conjugatePolarization q) (conjugate_raise_automorphic q)
      (conjugate_raise_eq q) A z

end
end RHTower.D4BMAngularTwoWeight
