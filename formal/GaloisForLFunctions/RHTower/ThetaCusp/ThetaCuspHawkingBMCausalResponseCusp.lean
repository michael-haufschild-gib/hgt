import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeAngularCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeResidualAdmission

/-!
Original causal integration of the complete theta-source cusp remainder.

The principal coefficients are the existing physical radial responses. Subtracting
their three original source integrals gives an exact integral for the full uncut
remainder and every actual ordered angular derivative. The native cusp-jet bound
passes through the original double integral, uniformly on compact nonnegative
causal rectangles and for arbitrary horizontal positions.

Subtracting the three scalar Goursat equations from the full source equation
identifies the remainder's forcing and both actual first null derivatives. The
source weight, null Jacobian, angular Laplacian, and characteristic edges are kept.
These statements do not assert physical-current cancellation or RH.
-/
open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMCausalCusp
open D4BMNativeCircle D4BMNativeResponse D4BMNativeCuspJets D4BMJointSource
open D4BMNativeAngularCurrent D4BMCausalKernel D4BMModularCore D4BMSquareCuspJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev Angular := Fin 2 → ℝ
private abbrev Native := Fin 3 → ℝ

/-- The original continuous causal radius, including both characteristic edges. -/
def radius (p r a b : ℝ) : ℝ :=
  Real.arcosh (max 1 (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)))
private theorem radius_nonneg (p r a b : ℝ) : 0 ≤ radius p r a b :=
  Real.arcosh_nonneg (le_max_left _ _)
private theorem radius_continuous :
    Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => radius z.1.1 z.1.2 z.2.1 z.2.2) := by
  apply Real.continuousOn_arcosh.comp_continuous
  · unfold invariant
    apply Continuous.max continuous_const
    apply Continuous.div <;> try fun_prop
    intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  · intro z; change (1:ℝ) ≤ max 1 _; exact le_max_left (1:ℝ) _
@[fun_prop] private theorem radius_comp {P : Type*} [TopologicalSpace P]
    (p r a b : P → ℝ) (hp : Continuous p) (hr : Continuous r)
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun z => radius (p z) (r z) (a z) (b z)) := by
  have h := radius_continuous.comp ((hp.prodMk hr).prodMk (ha.prodMk hb))
  simpa only [Function.comp_def] using! h

/-- The original odd source and its null-coordinate Jacobian are kept separately. -/
def sourceWeight (s amplitude : ℂ) (a b : ℝ) : ℂ :=
  oddSource s amplitude ((a+b)/2) ((a-b)/2)
private theorem odd_continuous (s amplitude : ℂ) :
    Continuous (fun z : ℝ × ℝ => oddSource s amplitude z.1 z.2) := by
  have h₁ := (timeReducedCoefficient_joint_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min z.2 0)) by fun_prop)
  have h₂ := (timeReducedCoefficient_joint_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min (-z.2) 0)) by fun_prop)
  convert! h₁.sub h₂ using 1
@[fun_prop] private theorem weight_comp {P : Type*} [TopologicalSpace P]
    (s amplitude : ℂ) (a b : P → ℝ) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun z => sourceWeight s amplitude (a z) (b z)) := by
  have h := (odd_continuous s amplitude).comp
    ((ha.add hb).div_const 2 |>.prodMk ((ha.sub hb).div_const 2))
  simpa only [sourceWeight,Function.comp_def] using! h

private theorem circle_smooth (a : ℂ) : ContDiff ℝ ∞ (powerCircle a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro d
  have h := (D4BMCausalSourceKernel.legendre_contDiffAt (-a) (Real.cosh_pos d)).comp d
    (show ContDiffAt ℝ ∞ Real.cosh d by fun_prop)
  simpa only [Function.comp_def,← powerCircle_eq_legendre] using h
private theorem exp_cpow (a : ℂ) (k : ℝ) : (Real.exp k:ℂ)^a=Complex.exp (a*(k:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
    ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
  congr 1
  ring
private theorem native_remainder_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (nativeRemainder q) := by
  have hf := (nativeMean_joint_smooth q).comp
    (show ContDiff ℝ ∞ (fun p : Native => (p 0,p 1,p 2)) by fun_prop)
  have hp : ContDiff ℝ ∞ (fun p : Native => transportedPrincipal q (p 0) (p 2)) := by
    simp only [transportedPrincipal,exp_cpow]
    apply ContDiff.sum
    intro i _
    have he : ContDiff ℝ ∞ (fun p : Native => Complex.exp (principalExponent q i*(p 2:ℂ))) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (2:Fin 3)))).cexp
    exact (contDiff_const.mul he).mul
      ((circle_smooth _).comp (contDiff_apply ℝ ℝ (0:Fin 3)))
  simpa only [nativeRemainder,cuspMeanRemainder,Function.comp_def] using! hf.sub hp
private theorem native_jet_smooth (q : XiZeroCopy) (word : List (Fin 3)) :
    ContDiff ℝ ∞ (nativeJet word (nativeRemainder q)) := by
  induction word with
  | nil => exact native_remainder_smooth q
  | cons i word ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- The exact uncut three-channel principal response, with the original radial coefficients. -/
def principalResponse (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : Angular) : ℂ :=
  ∑ i : Fin 3, principalNullResponse q s amplitude i p r*
    Complex.exp (principalExponent q i*(z 1:ℂ))
/-- The literal full response minus its three complete principal channels. -/
def responseRemainder (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : Angular) : ℂ :=
  fullNullResponse q s amplitude p r (z 0) (z 1)-principalResponse q s amplitude p r z
private theorem response_smooth (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) :
    ContDiff ℝ ∞ (responseRemainder q s amplitude p r) := by
  have hf := (fullNullResponse_angular_smooth q s amplitude p r).comp
    (show ContDiff ℝ ∞ (fun z : Angular => (z 0,z 1)) by fun_prop)
  have hp : ContDiff ℝ ∞ (principalResponse q s amplitude p r) := by
    unfold principalResponse
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul ((contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 2)))).cexp)
  simpa only [responseRemainder,Function.comp_def] using! hf.sub hp

/-- Original causal integral of every ordered angular native-remainder derivative. -/
def jetIntegral (q : XiZeroCopy) (s amplitude : ℂ) (word : List (Fin 2))
    (p r : ℝ) (z : Angular) : ℂ :=
  (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
    nativeJet (word.map Fin.succ) (nativeRemainder q) ![radius p r a b,z 0,z 1]*
      sourceWeight s amplitude a b

private theorem full_integral (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : Angular) :
    fullNullResponse q s amplitude p r (z 0) (z 1)=
      (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        mean q (radius p r a b) (z 0) (z 1)*sourceWeight s amplitude a b := by
  change (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
    ((1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..(2*Real.pi),
      source q (radius p r a b) theta (z 0) (z 1))*sourceWeight s amplitude a b = _
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  rfl
private theorem scalar_radius (nu : ℂ) {p r a b : ℝ} (ha : a ≤ p) (hb : b ≤ r) :
    riemannKernel nu ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)=
      legendreKernel nu (Real.cosh (radius p r a b)) := by
  have hc : |(p-r)/2-(a-b)/2| ≤ (p+r-a-b)/2 := by rw [abs_le]; constructor <;> linarith
  rw [radius,Real.cosh_arcosh (le_max_left _ _),max_eq_right (invariant_causal ⟨_,_,_,hc⟩)]
  rfl

/-- The integrated principal channels are the existing original physical radial responses. -/
theorem principal_coefficient_integral (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 3)
    (p r : Ici (0:ℝ)) :
    principalNullResponse q s amplitude i p.val r.val=
      (1/4:ℂ)*∫ a in (0:ℝ)..p.val, ∫ b in (0:ℝ)..r.val,
        principalAmplitude q i*powerCircle (principalExponent q i) (radius p.val r.val a b)*
          sourceWeight s amplitude a b := by
  unfold principalNullResponse
  rw [radialResponse_null_native _ s amplitude p.property r.property]
  have he : principalAmplitude q i*((1/4:ℂ)*
      (∫ a in (0:ℝ)..p.val, ∫ b in (0:ℝ)..r.val,
        riemannKernel (-principalExponent q i) ((p.val+r.val-a-b)/2) ((p.val-r.val)/2) ((a-b)/2)*
          oddSource s amplitude ((a+b)/2) ((a-b)/2)))=
      (1/4:ℂ)*∫ a in (0:ℝ)..p.val, ∫ b in (0:ℝ)..r.val,
        principalAmplitude q i*(riemannKernel (-principalExponent q i)
          ((p.val+r.val-a-b)/2) ((p.val-r.val)/2) ((a-b)/2)*sourceWeight s amplitude a b) := by
    simp only [intervalIntegral.integral_const_mul,sourceWeight]
    ring
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  apply intervalIntegral.integral_congr
  intro b hb
  dsimp only
  rw [powerCircle_eq_legendre,scalar_radius _
    (show a ≤ p.val from (show a ∈ Icc 0 p.val by simpa only [uIcc_of_le (show 0 ≤ p.val from p.property)] using ha).2)
    (show b ≤ r.val from (show b ∈ Icc 0 r.val by simpa only [uIcc_of_le (show 0 ≤ r.val from r.property)] using hb).2)]
  ring

@[fun_prop] private theorem mean_comp {P : Type*} [TopologicalSpace P]
    (q : XiZeroCopy) (d X k : P → ℝ) (hd : Continuous d) (hX : Continuous X) (hk : Continuous k) :
    Continuous (fun z => mean q (d z) (X z) (k z)) := by
  have h := (nativeMean_joint_smooth q).continuous.comp (hd.prodMk (hX.prodMk hk))
  simpa only [Function.comp_def] using! h
@[fun_prop] private theorem jet_comp {P : Type*} [TopologicalSpace P]
    (q : XiZeroCopy) (word : List (Fin 3)) (d X k : P → ℝ)
    (hd : Continuous d) (hX : Continuous X) (hk : Continuous k) :
    Continuous (fun z => nativeJet word (nativeRemainder q) ![d z,X z,k z]) := by
  have h := (native_jet_smooth q word).continuous.comp
    (show Continuous (fun z => (![d z,X z,k z]:Native)) by fun_prop)
  simpa only [Function.comp_def] using! h

@[fun_prop] private theorem integral_continuous {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] (f : P → ℝ → ℂ) (hf : Continuous (Function.uncurry f))
    (l r : P → ℝ) (hl : Continuous l) (hr : Continuous r) :
    Continuous (fun x => ∫ t in l x..r x, f x t) := by
  have h₁ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hr
  have h₂ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hl
  convert! h₁.sub h₂ using 1
  funext x
  exact (intervalIntegral.integral_interval_sub_left
    ((hf.uncurry_left x).intervalIntegrable 0 (r x))
    ((hf.uncurry_left x).intervalIntegrable 0 (l x))).symm

private theorem jetIntegral_continuous (q : XiZeroCopy) (s amplitude : ℂ) (word : List (Fin 2)) :
    Continuous (fun v : (ℝ × ℝ) × Angular => jetIntegral q s amplitude word v.1.1 v.1.2 v.2) := by
  unfold jetIntegral
  fun_prop

private def principalIntegrand (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 3)
    (p r : ℝ) (z : Angular) (a b : ℝ) : ℂ :=
  principalAmplitude q i*Complex.exp (principalExponent q i*(z 1:ℂ))*
    powerCircle (principalExponent q i) (radius p r a b)*sourceWeight s amplitude a b
private theorem principalIntegrand_continuous (q : XiZeroCopy) (s amplitude : ℂ)
    (i : Fin 3) (p r : ℝ) (z : Angular) :
    Continuous (Function.uncurry (principalIntegrand q s amplitude i p r z)) := by
  exact (continuous_const.mul ((circle_smooth _).continuous.comp
    (show Continuous (fun x : ℝ × ℝ => radius p r x.1 x.2) by fun_prop))).mul (by fun_prop)

private theorem principal_term_integral (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 3)
    (p r : Ici (0:ℝ)) (z : Angular) :
    principalNullResponse q s amplitude i p.val r.val*Complex.exp (principalExponent q i*(z 1:ℂ))=
      (1/4:ℂ)*∫ a in (0:ℝ)..p.val, ∫ b in (0:ℝ)..r.val,
        principalIntegrand q s amplitude i p.val r.val z a b := by
  rw [principal_coefficient_integral]
  calc
    _ = (1/4:ℂ)*∫ a in (0:ℝ)..p.val, ∫ b in (0:ℝ)..r.val,
        (principalAmplitude q i*powerCircle (principalExponent q i) (radius p.val r.val a b)*
          sourceWeight s amplitude a b)*Complex.exp (principalExponent q i*(z 1:ℂ)) := by
      simp only [intervalIntegral.integral_mul_const]
      ring
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro a _
      apply intervalIntegral.integral_congr
      intro b _
      unfold principalIntegrand
      ring

private theorem rectangle_sub_sum (f : ℝ → ℝ → ℂ) (g : Fin 3 → ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (hg : ∀ i, Continuous (Function.uncurry (g i))) (p r : ℝ) :
    (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, f a b-∑ i : Fin 3, g i a b) =
      (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, f a b)-
        ∑ i : Fin 3, ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, g i a b := by
  have hs : Continuous (fun x : ℝ × ℝ => ∑ i : Fin 3, g i x.1 x.2) :=
    continuous_finsetSum _ (fun i _ => hg i)
  have hi (a : ℝ) : (∫ b in (0:ℝ)..r, f a b-∑ i : Fin 3, g i a b) =
      (∫ b in (0:ℝ)..r, f a b)-∑ i : Fin 3, ∫ b in (0:ℝ)..r, g i a b := by
    rw [intervalIntegral.integral_sub ((hf.uncurry_left a).intervalIntegrable 0 r)
      ((Continuous.uncurry_left (f := fun a b => ∑ i : Fin 3, g i a b) a hs).intervalIntegrable 0 r),
      intervalIntegral.integral_finsetSum (fun i _ => ((hg i).uncurry_left a).intervalIntegrable 0 r)]
  have ho (i : Fin 3) : Continuous (fun a => ∫ b in (0:ℝ)..r, g i a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hg i) 0 r
  simp_rw [hi]
  rw [intervalIntegral.integral_sub
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 r).intervalIntegrable 0 p)
    ((continuous_finsetSum _ (fun i _ => ho i)).intervalIntegrable 0 p),
    intervalIntegral.integral_finsetSum (fun i _ => (ho i).intervalIntegrable 0 p)]

/-- Exact source-integral identity for the entire response remainder, with all
three existing radial coefficients, the original odd source, and the null Jacobian. -/
theorem responseRemainder_integral (q : XiZeroCopy) (s amplitude : ℂ)
    (p r : Ici (0:ℝ)) (z : Angular) :
    responseRemainder q s amplitude p.val r.val z=jetIntegral q s amplitude [] p.val r.val z := by
  have hi : jetIntegral q s amplitude [] p.val r.val z=
      (1/4:ℂ)*∫ a in (0:ℝ)..p.val, ∫ b in (0:ℝ)..r.val,
        mean q (radius p.val r.val a b) (z 0) (z 1)*sourceWeight s amplitude a b-
          ∑ i : Fin 3, principalIntegrand q s amplitude i p.val r.val z a b := by
    unfold jetIntegral
    congr 1
    apply intervalIntegral.integral_congr
    intro a _
    apply intervalIntegral.integral_congr
    intro b _
    simp only [List.map_nil,nativeJet,nativeRemainder,cuspMeanRemainder,transportedPrincipal,
      principalIntegrand,Matrix.cons_val,exp_cpow,sub_mul,Finset.sum_mul]
  rw [hi,rectangle_sub_sum _ _ (by fun_prop)
    (fun i => principalIntegrand_continuous q s amplitude i p.val r.val z)]
  simp only [responseRemainder,principalResponse,full_integral,principal_term_integral]
  rw [mul_sub,Finset.mul_sum]


private theorem native_slice (q : XiZeroCopy) (word : List (Fin 3)) (d : ℝ)
    (z : Angular) (i : Fin 2) :
    HasDerivAt (fun x => nativeJet word (nativeRemainder q)
      ![d,Function.update z i x 0,Function.update z i x 1])
      (nativeJet (i.succ::word) (nativeRemainder q) ![d,z 0,z 1]) (z i) := by
  have hp : HasDerivAt (fun x : ℝ =>
      (![d,Function.update z i x 0,Function.update z i x 1]:Native))
      (Pi.single i.succ 1) (z i) := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | exact hasDerivAt_const _ _ | exact hasDerivAt_id _
  have h := ((native_jet_smooth q word).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt (z i) hp
  simpa only [Function.update_eq_self,nativeJet,coordDeriv] using! h

private theorem jetIntegral_slice (q : XiZeroCopy) (s amplitude : ℂ) (word : List (Fin 2))
    (p r : ℝ) (z : Angular) (i : Fin 2) :
    HasDerivAt (fun x => jetIntegral q s amplitude word p r (Function.update z i x))
      (jetIntegral q s amplitude (i::word) p r z) (z i) := by
  let f := fun x a b => nativeJet (word.map Fin.succ) (nativeRemainder q)
    ![radius p r a b,Function.update z i x 0,Function.update z i x 1]*sourceWeight s amplitude a b
  let df := fun x a b => nativeJet (i.succ::word.map Fin.succ) (nativeRemainder q)
    ![radius p r a b,Function.update z i x 0,Function.update z i x 1]*sourceWeight s amplitude a b
  have hd (x a b : ℝ) : HasDerivAt (fun y => f y a b) (df x a b) x := by
    simpa [f,df] using!
      (native_slice q (word.map Fin.succ) (radius p r a b)
        (Function.update z i x) i).mul_const (sourceWeight s amplitude a b)
  have hin (x a : ℝ) : HasDerivAt (fun y => ∫ b in (0:ℝ)..r, f y a b)
      (∫ b in (0:ℝ)..r, df x a b) x :=
    hasDerivAt_parametric_intervalIntegral (f := fun y b => f y a b)
      (f' := fun y b => df y a b) (by dsimp [f]; fun_prop)
      (by dsimp [df]; fun_prop) (fun y b => hd y a b) 0 r x
  have hout := hasDerivAt_parametric_intervalIntegral
    (f := fun x a => ∫ b in (0:ℝ)..r,
      nativeJet (word.map Fin.succ) (nativeRemainder q)
        ![radius p r a b,Function.update z i x 0,Function.update z i x 1]*sourceWeight s amplitude a b)
    (f' := fun x a => ∫ b in (0:ℝ)..r,
      nativeJet (i.succ::word.map Fin.succ) (nativeRemainder q)
        ![radius p r a b,Function.update z i x 0,Function.update z i x 1]*sourceWeight s amplitude a b)
      (by fun_prop) (by fun_prop) hin 0 p (z i)
  simpa only [jetIntegral,List.map_cons,Function.update_eq_self] using!
    hout.const_mul (1/4:ℂ)

private theorem responseJet_smooth (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ)
    (word : List (Fin 2)) :
    ContDiff ℝ ∞ (coordinateJet word (responseRemainder q s amplitude p r)) := by
  induction word with
  | nil => exact response_smooth q s amplitude p r
  | cons i word ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const
private theorem slice_first {f : Angular → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 2) (p : Angular) :
    deriv (fun x => f (Function.update p i x)) (p i)=coordDeriv i f p := by
  have hi : HasDerivAt (fun x : ℝ => Function.update p i x) (Pi.single i 1) (p i) := by
    apply hasDerivAt_pi.mpr
    intro j
    by_cases h : j=i
    · subst j
      simpa using! hasDerivAt_id (p i)
    · simpa [h] using! hasDerivAt_const (p i) (p j)
  have hF : HasFDerivAt f (fderiv ℝ f p) (Function.update p i (p i)) := by
    simpa only [Function.update_eq_self] using! (hf.differentiable (by simp) p).hasFDerivAt
  simpa [coordDeriv] using! (hF.comp_hasDerivAt (p i) hi).deriv

/-- Every actual ordered angular derivative of the entire causal remainder is
the original signed source integral of the matching native derivative. -/
theorem responseRemainder_jet_integral (q : XiZeroCopy) (s amplitude : ℂ)
    (p r : Ici (0:ℝ)) (word : List (Fin 2)) (z : Angular) :
    coordinateJet word (responseRemainder q s amplitude p.val r.val) z=
      jetIntegral q s amplitude word p.val r.val z := by
  induction word generalizing z with
  | nil => exact responseRemainder_integral q s amplitude p r z
  | cons i word ih =>
    change coordDeriv i (coordinateJet word (responseRemainder q s amplitude p.val r.val)) z = _
    rw [← slice_first (responseJet_smooth q s amplitude p.val r.val word) i z]
    have he : (fun x => coordinateJet word (responseRemainder q s amplitude p.val r.val)
        (Function.update z i x))=fun x => jetIntegral q s amplitude word p.val r.val (Function.update z i x) :=
      funext (fun x => ih (Function.update z i x))
    rw [he]
    exact (jetIntegral_slice q s amplitude word p.val r.val z i).deriv


private theorem geometry_bounds (s amplitude : ℂ) (T : Ici (0:ℝ)) :
    ∃ D : Ici (0:ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ Icc 0 T.val, ∀ r ∈ Icc 0 T.val, ∀ a ∈ Icc 0 p, ∀ b ∈ Icc 0 r,
        radius p r a b ≤ D.val ∧ ‖sourceWeight s amplitude a b‖ ≤ C := by
  let box : Set (ℝ × ℝ) := Icc 0 T.val ×ˢ Icc 0 T.val
  have hc : IsCompact box := isCompact_Icc.prod isCompact_Icc
  obtain ⟨D,hD⟩ := (hc.prod hc).exists_bound_of_continuousOn radius_continuous.continuousOn
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn
    (show Continuous (fun z : ℝ × ℝ => sourceWeight s amplitude z.1 z.2) by fun_prop).continuousOn
  refine ⟨⟨max D 0,show 0 ≤ max D 0 from le_max_right _ _⟩,max C 0,le_max_right _ _,?_⟩
  intro p hp r hr a ha b hb
  have hab : (a,b) ∈ box := ⟨⟨ha.1,ha.2.trans hp.2⟩,⟨hb.1,hb.2.trans hr.2⟩⟩
  constructor
  · calc
      radius p r a b ≤ ‖radius p r a b‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ D := hD ((p,r),(a,b)) ⟨⟨hp,hr⟩,hab⟩
      _ ≤ max D 0 := le_max_left _ _
  · exact (hC (a,b) hab).trans (le_max_left _ _)

/-- Every actual angular remainder derivative has arbitrary cusp decay,
uniformly over the original bounded causal rectangle and all horizontal positions. -/
theorem responseRemainder_jet_uniform_bound (q : XiZeroCopy) (s amplitude : ℂ)
    (word : List (Fin 2)) (N : ℕ) (T : Ici (0:ℝ)) :
    ∃ D B : ℝ, 0 ≤ D ∧ 0 ≤ B ∧
      ∀ p ∈ Icc 0 T.val, ∀ r ∈ Icc 0 T.val, ∀ X k : ℝ, D ≤ k →
        ‖coordinateJet word (responseRemainder q s amplitude p r) ![X,k]‖ ≤
          B*Real.exp ((N:ℝ)*(D-k)) := by
  have hT : 0 ≤ T.val := T.property
  obtain ⟨D,C,hC,hgeometry⟩ := geometry_bounds s amplitude T
  obtain ⟨B,hB,hjet⟩ := nativeCuspJet_rapid_bound q (word.map Fin.succ) N D
  refine ⟨D.val,B*C*T.val*T.val,D.property,by positivity,?_⟩
  intro p hp r hr X k hk
  rw [responseRemainder_jet_integral q s amplitude ⟨p,hp.1⟩ ⟨r,hr.1⟩ word ![X,k]]
  have hi (a : ℝ) (ha : a ∈ Icc 0 p) (b : ℝ) (hb : b ∈ Icc 0 r) :
      ‖nativeJet (word.map Fin.succ) (nativeRemainder q) ![radius p r a b,X,k]*
        sourceWeight s amplitude a b‖ ≤ B*C*Real.exp ((N:ℝ)*(D.val-k)) := by
    obtain ⟨hd,hs⟩ := hgeometry p hp r hr a ha b hb
    rw [norm_mul]
    calc
      _ ≤ (B*Real.exp ((N:ℝ)*(D.val-k)))*C := by
        apply mul_le_mul (hjet (radius p r a b) X k (radius_nonneg _ _ _ _) hd hk) hs
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  have hb (a : ℝ) (ha : a ∈ uIoc (0:ℝ) p) :
      ‖∫ b in (0:ℝ)..r, nativeJet (word.map Fin.succ) (nativeRemainder q) ![radius p r a b,X,k]*
        sourceWeight s amplitude a b‖ ≤ (B*C*Real.exp ((N:ℝ)*(D.val-k)))*r := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := r) (C := B*C*Real.exp ((N:ℝ)*(D.val-k)))
      (fun b hb => hi a (by rw [uIoc_of_le hp.1] at ha; exact ⟨ha.1.le,ha.2⟩)
        b (by rw [uIoc_of_le hr.1] at hb; exact ⟨hb.1.le,hb.2⟩))
    simpa only [sub_zero,abs_of_nonneg hr.1] using h
  have ho := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := p) (C := (B*C*Real.exp ((N:ℝ)*(D.val-k)))*r) hb
  simp only [sub_zero,abs_of_nonneg hp.1] at ho
  unfold jetIntegral
  simp only [Matrix.cons_val]
  calc
    _ ≤ ‖∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        nativeJet (word.map Fin.succ) (nativeRemainder q) ![radius p r a b,X,k]*
          sourceWeight s amplitude a b‖ := by
      rw [norm_mul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      norm_num
    _ ≤ B*C*Real.exp ((N:ℝ)*(D.val-k))*r*p := ho
    _ ≤ B*C*Real.exp ((N:ℝ)*(D.val-k))*T.val*T.val := by
      gcongr
      · exact hp.1
      · exact hr.2
      · exact hp.2
    _ = (B*C*T.val*T.val)*Real.exp ((N:ℝ)*(D.val-k)) := by ring

/-- Full causal integration preserves every complex-weighted angular cusp
limit, uniformly along arbitrary compact causal and horizontal paths. -/
theorem responseRemainder_jet_weighted_tendsto_zero (q : XiZeroCopy) (s amplitude : ℂ)
    (word : List (Fin 2)) (T : Ici (0:ℝ))
    (p r : ℝ → Icc 0 T.val) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      coordinateJet word (responseRemainder q s amplitude (p k).val (r k).val) ![X k,k])
      atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt w.re
  obtain ⟨D,B,hD,hB,hbound⟩ := responseRemainder_jet_uniform_bound q s amplitude word N T
  have ht := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (sub_neg.mpr hN)).2 tendsto_id)
  apply squeeze_zero_norm' _ (by simpa using ht.const_mul (B*Real.exp ((N:ℝ)*D)))
  filter_upwards [eventually_ge_atTop D] with k hk
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  calc
    _ ≤ Real.exp (w.re*k)*(B*Real.exp ((N:ℝ)*(D-k))) := by
      gcongr
      exact hbound (p k).val (p k).property (r k).val (r k).property (X k) k hk
    _ = B*Real.exp ((N:ℝ)*D)*Real.exp ((w.re-(N:ℝ))*k) := by
      have he : Real.exp (w.re*k)*Real.exp ((N:ℝ)*(D-k))=
          Real.exp ((N:ℝ)*D)*Real.exp ((w.re-(N:ℝ))*k) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      calc
        _ = B*(Real.exp (w.re*k)*Real.exp ((N:ℝ)*(D-k))) := by ring
        _ = _ := by rw [he]; ring

private def PJet (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (n : ℕ) (z : Angular) : ℂ :=
  ∑ i : Fin 3, principalNullResponse q s amplitude i p r*(principalExponent q i)^n*
    Complex.exp (principalExponent q i*(z 1:ℂ))
private theorem PJet_smooth (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (PJet q s amplitude p r n) := by
  unfold PJet
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_apply ℝ ℝ (1:Fin 2)))).cexp)
private theorem D_smooth {f : Angular → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 2) :
    ContDiff ℝ ∞ (coordDeriv i f) := (hf.fderiv_right (by simp)).clm_apply contDiff_const
private theorem D_sub {f g : Angular → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin 2) (z : Angular) :
    coordDeriv i (fun z => f z-g z) z=coordDeriv i f z-coordDeriv i g z := by
  simp only [coordDeriv,fderiv_fun_sub (hf.differentiable (by simp) z)
    (hg.differentiable (by simp) z),sub_apply]
private theorem PJet_first (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (n : ℕ) (z : Angular) :
    coordDeriv 0 (PJet q s amplitude p r n) z=0 ∧
      coordDeriv 1 (PJet q s amplitude p r n) z=PJet q s amplitude p r (n+1) z := by
  have h (j : Fin 2) : coordDeriv j (PJet q s amplitude p r n) z=
      ∑ i : Fin 3, principalNullResponse q s amplitude i p r*(principalExponent q i)^n*
        (if j=1 then principalExponent q i*Complex.exp (principalExponent q i*(z 1:ℂ)) else 0) := by
    unfold coordDeriv PJet
    rw [fderiv_fun_sum (fun i _ =>
      (show ContDiff ℝ ∞ (fun z : Angular => principalNullResponse q s amplitude i p r*
        (principalExponent q i)^n*Complex.exp (principalExponent q i*(z 1:ℂ))) from
        contDiff_const.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
          (contDiff_apply ℝ ℝ (1:Fin 2)))).cexp)).differentiable (by simp) z)]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hc := Complex.ofRealCLM.hasFDerivAt.comp z (hasFDerivAt_apply (𝕜 := ℝ) 1 z)
    have he := ((hc.const_mul (principalExponent q i)).cexp).const_mul
      (principalNullResponse q s amplitude i p r*(principalExponent q i)^n)
    dsimp only [Function.comp_def,Complex.ofRealCLM_apply] at he
    rw [he.fderiv]
    fin_cases j <;> simp [smul_eq_mul]
    ring_nf
    simp
  constructor
  · simp [h]
  · rw [h]
    simp only [ite_true,PJet]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
private theorem angular_decomposition (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : Angular) :
    let U := fun z : Angular => fullNullResponse q s amplitude p r (z 0) (z 1)
    let R := responseRemainder q s amplitude p r
    coordinateJet [1] U z=PJet q s amplitude p r 1 z+coordinateJet [1] R z ∧
      coordinateJet [1,1] U z=PJet q s amplitude p r 2 z+coordinateJet [1,1] R z ∧
      coordinateJet [0,0] U z=coordinateJet [0,0] R z := by
  dsimp only
  let U := fun z : Angular => fullNullResponse q s amplitude p r (z 0) (z 1)
  have hU : ContDiff ℝ ∞ U := by
    have h := (fullNullResponse_angular_smooth q s amplitude p r).comp
      (show ContDiff ℝ ∞ (fun z : Angular => (z 0,z 1)) by fun_prop)
    simpa only [U,Function.comp_def] using! h
  have he : responseRemainder q s amplitude p r=fun z => U z-PJet q s amplitude p r 0 z := by
    funext z
    simp only [responseRemainder,principalResponse,PJet,pow_zero,mul_one,U]
  have h1 : coordDeriv 1 (responseRemainder q s amplitude p r)=
      fun z => coordDeriv 1 U z-PJet q s amplitude p r 1 z := by
    funext z
    rw [he,D_sub hU (PJet_smooth q s amplitude p r 0),(PJet_first q s amplitude p r 0 z).2]
  have h0 : coordDeriv 0 (responseRemainder q s amplitude p r)=coordDeriv 0 U := by
    funext z
    rw [he,D_sub hU (PJet_smooth q s amplitude p r 0),(PJet_first q s amplitude p r 0 z).1,sub_zero]
  change coordDeriv 1 U z=_ ∧ coordDeriv 1 (coordDeriv 1 U) z=_ ∧ coordDeriv 0 (coordDeriv 0 U) z=_
  simp only [coordinateJet]
  rw [h1,D_sub (D_smooth hU 1) (PJet_smooth q s amplitude p r 1),
    (PJet_first q s amplitude p r 1 z).2,h0]
  exact ⟨by ring,by ring,rfl⟩

private theorem slice_second {f : Angular → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 2) (z : Angular) :
    deriv (deriv (fun x => f (Function.update z i x))) (z i)=coordinateJet [i,i] f z := by
  have he : deriv (fun x => f (Function.update z i x))=
      fun x => coordDeriv i f (Function.update z i x) := by
    funext x
    simpa using!
      slice_first hf i (Function.update z i x)
  rw [he]
  exact slice_first (D_smooth hf i) i z

private def remainderAction (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : Angular) : ℂ :=
  (Real.exp (z 1):ℂ)^(2 : ℕ)*jetIntegral q s amplitude [0,0] p r z+
    jetIntegral q s amplitude [1,1] p r z-jetIntegral q s amplitude [1] p r z
private def principalAction (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : Angular) : ℂ :=
  ∑ i : Fin 3, principalExponent q i*(principalExponent q i-1)*
    principalNullResponse q s amplitude i p r*Complex.exp (principalExponent q i*(z 1:ℂ))
private theorem full_action (q : XiZeroCopy) (s amplitude : ℂ) (p r : Ici (0:ℝ)) (X k : ℝ) :
    (Real.exp k:ℂ)^(2 : ℕ)*deriv (deriv (fun x => fullNullResponse q s amplitude p.val r.val x k)) X+
      deriv (deriv (fun x => fullNullResponse q s amplitude p.val r.val X x)) k-
      deriv (fun x => fullNullResponse q s amplitude p.val r.val X x) k=
        remainderAction q s amplitude p.val r.val ![X,k]+principalAction q s amplitude p.val r.val ![X,k] := by
  let U := fun z : Angular => fullNullResponse q s amplitude p.val r.val (z 0) (z 1)
  have hU : ContDiff ℝ ∞ U := by
    have h := (fullNullResponse_angular_smooth q s amplitude p.val r.val).comp
      (show ContDiff ℝ ∞ (fun z : Angular => (z 0,z 1)) by fun_prop)
    simpa only [U,Function.comp_def] using! h
  have hx : deriv (deriv (fun x => fullNullResponse q s amplitude p.val r.val x k)) X=
      coordinateJet [0,0] U ![X,k] := by simpa [U] using slice_second hU 0 ![X,k]
  have hkk : deriv (deriv (fun x => fullNullResponse q s amplitude p.val r.val X x)) k=
      coordinateJet [1,1] U ![X,k] := by simpa [U] using slice_second hU 1 ![X,k]
  have hk : deriv (fun x => fullNullResponse q s amplitude p.val r.val X x) k=
      coordinateJet [1] U ![X,k] := by simpa [U,coordinateJet] using slice_first hU 1 ![X,k]
  obtain ⟨h1,h2,h0⟩ := angular_decomposition q s amplitude p.val r.val ![X,k]
  rw [hx,hkk,hk,h1,h2,h0]
  simp_rw [responseRemainder_jet_integral q s amplitude p r]
  have he : PJet q s amplitude p.val r.val 2 ![X,k]-PJet q s amplitude p.val r.val 1 ![X,k]=
      principalAction q s amplitude p.val r.val ![X,k] := by
    simp only [PJet,principalAction,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  dsimp only [remainderAction,Matrix.cons_val]
  linear_combination he

@[fun_prop] private theorem principal_comp {P : Type*} [TopologicalSpace P]
    (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 3) (p r : P → ℝ)
    (hp : Continuous p) (hr : Continuous r) :
    Continuous (fun z => principalNullResponse q s amplitude i (p z) (r z)) := by
  have h := (radialResponse_continuous (-principalExponent q i) s amplitude).comp
    (show Continuous (fun z => ((p z+r z)/2,(p z-r z)/2)) by fun_prop)
  simpa only [principalNullResponse,Function.comp_def] using! h.const_mul (principalAmplitude q i)
@[fun_prop] private theorem jetIntegral_comp {P : Type*} [TopologicalSpace P]
    (q : XiZeroCopy) (s amplitude : ℂ) (word : List (Fin 2)) (p r : P → ℝ) (z : P → Angular)
    (hp : Continuous p) (hr : Continuous r) (hz : Continuous z) :
    Continuous (fun x => jetIntegral q s amplitude word (p x) (r x) (z x)) := by
  simpa only [Function.comp_def] using!
    (jetIntegral_continuous q s amplitude word).comp ((hp.prodMk hr).prodMk hz)
private def potential (p r : ℝ) : ℂ := 1/(4*(Real.cosh ((p-r)/2):ℂ)^(2 : ℕ))
@[fun_prop] private theorem potential_comp {P : Type*} [TopologicalSpace P]
    (p r : P → ℝ) (hp : Continuous p) (hr : Continuous r) :
    Continuous (fun z => potential (p z) (r z)) := by
  unfold potential
  apply Continuous.div continuous_const (by fun_prop)
  intro z
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))
private def effective (q : XiZeroCopy) (s amplitude : ℂ) (z : Angular) (p r : ℝ) : ℂ :=
  (1/4:ℂ)*nativeRemainder q ![0,z 0,z 1]*sourceWeight s amplitude p r+
    potential p r*remainderAction q s amplitude p r z
private def fullEffective (q : XiZeroCopy) (s amplitude : ℂ) (z : Angular) (p r : ℝ) : ℂ :=
  (1/4:ℂ)*fullSquarePotential q ![z 0,Real.exp (z 1)]*sourceWeight s amplitude p r+
    potential p r*(remainderAction q s amplitude p r z+principalAction q s amplitude p r z)
private def principalEffective (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 3) (p r : ℝ) : ℂ :=
  principalAmplitude q i*sourceWeight s amplitude p r/4+
    potential p r*(principalExponent q i*(principalExponent q i-1)*principalNullResponse q s amplitude i p r)
@[fun_prop] private theorem effective_continuous (q : XiZeroCopy) (s amplitude : ℂ) (z : Angular) :
    Continuous (Function.uncurry (effective q s amplitude z)) := by
  unfold effective remainderAction
  fun_prop
@[fun_prop] private theorem fullEffective_continuous (q : XiZeroCopy) (s amplitude : ℂ) (z : Angular) :
    Continuous (Function.uncurry (fullEffective q s amplitude z)) := by
  unfold fullEffective remainderAction principalAction
  fun_prop
@[fun_prop] private theorem principalEffective_continuous (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 3) :
    Continuous (Function.uncurry (principalEffective q s amplitude i)) := by
  unfold principalEffective
  fun_prop

private def rectangle (f : ℝ → ℝ → ℂ) (p r : ℝ) : ℂ := ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, f a b
private theorem rectangle_add (f g : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    rectangle (fun a b => f a b+g a b) p r=rectangle f p r+rectangle g p r := by
  unfold rectangle
  simp_rw [intervalIntegral.integral_add ((hf.uncurry_left _).intervalIntegrable 0 r)
    ((hg.uncurry_left _).intervalIntegrable 0 r)]
  exact intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 r).intervalIntegrable 0 p)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg 0 r).intervalIntegrable 0 p)
private theorem principal_primitive (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 3)
    (p r : Ici (0:ℝ)) :
    principalNullResponse q s amplitude i p.val r.val=rectangle (principalEffective q s amplitude i) p.val r.val := by
  let alpha := principalExponent q i
  let v := fun a b => (-alpha)*(-alpha+1)/(4*(Real.cosh ((a-b)/2):ℂ)^(2 : ℕ))*
    radialResponse (-alpha) s amplitude ((a+b)/2) ((a-b)/2)
  have hv : Continuous (Function.uncurry v) := by
    have hu := (radialResponse_continuous (-alpha) s amplitude).comp
      (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
    have hn := potential_comp (fun z : ℝ × ℝ => z.1) (fun z => z.2) continuous_fst continuous_snd
    convert! (hn.const_mul ((-alpha)*(-alpha+1))).mul hu using 1
    funext z
    dsimp only [Function.uncurry,v,potential,Function.comp_apply,Pi.mul_apply]
    ring
  have he : principalEffective q s amplitude i=fun a b =>
      principalAmplitude q i*((1/4:ℂ)*sourceWeight s amplitude a b+v a b) := by
    funext a b
    dsimp only [principalEffective,principalNullResponse,potential,v,alpha]
    ring
  rw [he]
  simp only [rectangle,intervalIntegral.integral_const_mul]
  change principalNullResponse q s amplitude i p.val r.val=principalAmplitude q i*
    rectangle (fun a b => (1/4:ℂ)*sourceWeight s amplitude a b+v a b) p.val r.val
  rw [rectangle_add _ _ (by fun_prop) hv]
  simp only [rectangle,intervalIntegral.integral_const_mul]
  exact congrArg (fun u => principalAmplitude q i*u)
    (radialResponse_goursat (-alpha) s amplitude p.property r.property)

private theorem full_primitive (q : XiZeroCopy) (s amplitude : ℂ) (p r : Ici (0:ℝ)) (X k : ℝ) :
    fullNullResponse q s amplitude p.val r.val X k=rectangle (fullEffective q s amplitude ![X,k]) p.val r.val := by
  unfold fullEffective
  rw [rectangle_add _ _ (by fun_prop) (by unfold remainderAction principalAction; fun_prop),
    fullNullResponse_goursat q s amplitude p.property r.property]
  congr 1
  · simp only [rectangle,intervalIntegral.integral_const_mul,sourceWeight,Matrix.cons_val]
    ring
  · unfold rectangle
    apply intervalIntegral.integral_congr
    intro a ha
    apply intervalIntegral.integral_congr
    intro b hb
    dsimp only
    have ha' : 0 ≤ a := (show a ∈ Icc 0 p.val by
      simpa only [uIcc_of_le (show 0 ≤ p.val from p.property)] using ha).1
    have hb' : 0 ≤ b := (show b ∈ Icc 0 r.val by
      simpa only [uIcc_of_le (show 0 ≤ r.val from r.property)] using hb).1
    rw [full_action q s amplitude ⟨a,ha'⟩ ⟨b,hb'⟩]
    unfold potential
    ring

private theorem source_remainder_zero (q : XiZeroCopy) (z : Angular) :
    nativeRemainder q ![0,z 0,z 1]=fullSquarePotential q ![z 0,Real.exp (z 1)]-
      ∑ i : Fin 3, principalAmplitude q i*Complex.exp (principalExponent q i*(z 1:ℂ)) := by
  simp only [nativeRemainder,cuspMeanRemainder,Matrix.cons_val,mean_zero,transportedPrincipal,
    powerCircle_eq_legendre,Real.cosh_zero,legendreKernel_one,exp_cpow,mul_one]
private theorem effective_decomposition (q : XiZeroCopy) (s amplitude : ℂ) (z : Angular) :
    effective q s amplitude z=fun p r => fullEffective q s amplitude z p r-
      ∑ i : Fin 3, principalEffective q s amplitude i p r*Complex.exp (principalExponent q i*(z 1:ℂ)) := by
  funext p r
  have hi (i : Fin 3) : principalEffective q s amplitude i p r*
      Complex.exp (principalExponent q i*(z 1:ℂ))=
      (principalAmplitude q i*Complex.exp (principalExponent q i*(z 1:ℂ)))*sourceWeight s amplitude p r/4+
        potential p r*(principalExponent q i*(principalExponent q i-1)*
          principalNullResponse q s amplitude i p r*Complex.exp (principalExponent q i*(z 1:ℂ))) := by
    unfold principalEffective
    ring
  rw [effective,source_remainder_zero,fullEffective]
  simp_rw [hi]
  rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul,← Finset.mul_sum]
  dsimp only [principalAction]
  ring
private theorem remainder_primitive (q : XiZeroCopy) (s amplitude : ℂ) (p r : Ici (0:ℝ)) (z : Angular) :
    responseRemainder q s amplitude p.val r.val z=rectangle (effective q s amplitude z) p.val r.val := by
  rw [effective_decomposition]
  change _=(∫ a in (0:ℝ)..p.val, ∫ b in (0:ℝ)..r.val,
    fullEffective q s amplitude z a b-
      ∑ i : Fin 3, principalEffective q s amplitude i a b*Complex.exp (principalExponent q i*(z 1:ℂ)))
  rw [rectangle_sub_sum (fullEffective q s amplitude z)
    (fun i a b => principalEffective q s amplitude i a b*Complex.exp (principalExponent q i*(z 1:ℂ)))
    (fullEffective_continuous q s amplitude z)
    (fun i => (principalEffective_continuous q s amplitude i).mul continuous_const)]
  simp only [intervalIntegral.integral_mul_const]
  change _=rectangle (fullEffective q s amplitude z) p.val r.val-
    ∑ i : Fin 3, rectangle (principalEffective q s amplitude i) p.val r.val*
      Complex.exp (principalExponent q i*(z 1:ℂ))
  simp_rw [← principal_primitive q s amplitude _ p r]
  have hz : ![z 0,z 1]=z := by ext i; fin_cases i <;> rfl
  rw [← hz,← full_primitive q s amplitude p r (z 0) (z 1)]
  rfl

/-- Exact Goursat equation of the complete uncut remainder, with the original
source and actual angular derivatives. Both characteristic edges are included. -/
theorem responseRemainder_goursat (q : XiZeroCopy) (s amplitude : ℂ) (p r : Ici (0:ℝ)) (z : Angular) :
    responseRemainder q s amplitude p.val r.val z=
      ∫ a in (0:ℝ)..p.val, ∫ b in (0:ℝ)..r.val,
        (1/4:ℂ)*nativeRemainder q ![0,z 0,z 1]*sourceWeight s amplitude a b+
          ((Real.exp (z 1):ℂ)^(2 : ℕ)*coordinateJet [0,0] (responseRemainder q s amplitude a b) z+
            coordinateJet [1,1] (responseRemainder q s amplitude a b) z-
            coordinateJet [1] (responseRemainder q s amplitude a b) z)/(4*(Real.cosh ((a-b)/2):ℂ)^(2 : ℕ)) := by
  rw [remainder_primitive]
  unfold rectangle
  apply intervalIntegral.integral_congr
  intro a ha
  apply intervalIntegral.integral_congr
  intro b hb
  have ha' : 0 ≤ a := (show a ∈ Icc 0 p.val by
    simpa only [uIcc_of_le (show 0 ≤ p.val from p.property)] using ha).1
  have hb' : 0 ≤ b := (show b ∈ Icc 0 r.val by
    simpa only [uIcc_of_le (show 0 ≤ r.val from r.property)] using hb).1
  dsimp only
  simp_rw [responseRemainder_jet_integral q s amplitude ⟨a,ha'⟩ ⟨b,hb'⟩]
  unfold effective remainderAction potential
  ring

/-- The original remainder source plus its actual hyperbolic angular Laplacian. -/
def remainderForcing (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : Angular) : ℂ :=
  (1/4:ℂ)*nativeRemainder q ![0,z 0,z 1]*sourceWeight s amplitude p r+
    ((Real.exp (z 1):ℂ)^(2 : ℕ)*coordinateJet [0,0] (responseRemainder q s amplitude p r) z+
      coordinateJet [1,1] (responseRemainder q s amplitude p r) z-
      coordinateJet [1] (responseRemainder q s amplitude p r) z)/(4*(Real.cosh ((p-r)/2):ℂ)^(2 : ℕ))
private theorem effective_actual (q : XiZeroCopy) (s amplitude : ℂ) (p r : Ici (0:ℝ)) (z : Angular) :
    effective q s amplitude z p.val r.val=remainderForcing q s amplitude p.val r.val z := by
  unfold remainderForcing
  simp_rw [responseRemainder_jet_integral q s amplitude p r]
  unfold effective remainderAction potential
  ring
private theorem rectangle_first (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) (p r : ℝ) :
    HasDerivAt (fun a => rectangle f a r) (∫ b in (0:ℝ)..r, f p b) p := by
  have hi : Continuous (fun a => ∫ b in (0:ℝ)..r, f a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 r
  exact intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 p)
    (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
private theorem rectangle_second (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) (p r : ℝ) :
    HasDerivAt (fun b => rectangle f p b) (∫ a in (0:ℝ)..p, f a r) r := by
  apply hasDerivAt_parametric_intervalIntegral (f := fun r a => ∫ b in (0:ℝ)..r, f a b)
    (f' := fun r a => f a r)
  · apply integral_continuous
    · exact hf.comp (continuous_fst.snd.prodMk continuous_snd)
    · exact continuous_const
    · exact continuous_fst
  · exact hf.comp (continuous_snd.prodMk continuous_fst)
  · intro b a
    have hi := hf.uncurry_left a
    exact intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 b)
      (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
private theorem remainder_first_effective (q : XiZeroCopy) (s amplitude : ℂ)
    (p : Ioi (0:ℝ)) (r : Ici (0:ℝ)) (z : Angular) :
    HasDerivAt (fun a => responseRemainder q s amplitude a r.val z)
      (∫ b in (0:ℝ)..r.val, effective q s amplitude z p.val b) p.val := by
  have hd := rectangle_first _ (effective_continuous q s amplitude z) p.val r.val
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds p.property] with a ha
  exact remainder_primitive q s amplitude ⟨a,show 0 ≤ a from le_of_lt ha⟩ r z
private theorem remainder_second_effective (q : XiZeroCopy) (s amplitude : ℂ)
    (p : Ici (0:ℝ)) (r : Ioi (0:ℝ)) (z : Angular) :
    HasDerivAt (fun b => responseRemainder q s amplitude p.val b z)
      (∫ a in (0:ℝ)..p.val, effective q s amplitude z a r.val) r.val := by
  have hd := rectangle_second _ (effective_continuous q s amplitude z) p.val r.val
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds r.property] with b hb
  exact remainder_primitive q s amplitude p ⟨b,show 0 ≤ b from le_of_lt hb⟩ z

/-- Actual first null derivative of the original causal remainder. The other
characteristic coordinate may equal zero. -/
theorem responseRemainder_first_null (q : XiZeroCopy) (s amplitude : ℂ)
    (p : Ioi (0:ℝ)) (r : Ici (0:ℝ)) (z : Angular) :
    HasDerivAt (fun a => responseRemainder q s amplitude a r.val z)
      (∫ b in (0:ℝ)..r.val, remainderForcing q s amplitude p.val b z) p.val := by
  have he : (∫ b in (0:ℝ)..r.val, effective q s amplitude z p.val b)=
      ∫ b in (0:ℝ)..r.val, remainderForcing q s amplitude p.val b z := by
    apply intervalIntegral.integral_congr
    intro b hb
    have hb' : 0 ≤ b := (show b ∈ Icc 0 r.val by
      simpa only [uIcc_of_le (show 0 ≤ r.val from r.property)] using hb).1
    exact effective_actual q s amplitude ⟨p.val,show 0 ≤ p.val from le_of_lt p.property⟩ ⟨b,hb'⟩ z
  rw [← he]
  exact remainder_first_effective q s amplitude p r z

/-- Actual second null-direction derivative of the original causal remainder,
with its original source and angular action. -/
theorem responseRemainder_second_null (q : XiZeroCopy) (s amplitude : ℂ)
    (p : Ici (0:ℝ)) (r : Ioi (0:ℝ)) (z : Angular) :
    HasDerivAt (fun b => responseRemainder q s amplitude p.val b z)
      (∫ a in (0:ℝ)..p.val, remainderForcing q s amplitude a r.val z) r.val := by
  have he : (∫ a in (0:ℝ)..p.val, effective q s amplitude z a r.val)=
      ∫ a in (0:ℝ)..p.val, remainderForcing q s amplitude a r.val z := by
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' : 0 ≤ a := (show a ∈ Icc 0 p.val by
      simpa only [uIcc_of_le (show 0 ≤ p.val from p.property)] using ha).1
    exact effective_actual q s amplitude ⟨a,ha'⟩ ⟨r.val,show 0 ≤ r.val from le_of_lt r.property⟩ z
  rw [← he]
  exact remainder_second_effective q s amplitude p r z


end
end RHTower.D4BMCausalCusp
