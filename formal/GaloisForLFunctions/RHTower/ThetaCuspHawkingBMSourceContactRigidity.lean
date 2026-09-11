import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCommonRadialSource
import GaloisForLFunctions.HTGeometry.ComplexCoordinateDerivativeRules

/-! Differential rigidity of the original theta-source contact. The literal scalar
equation and actual differentiated jets yield a complex bilinear Bochner identity
with no source or clock premises. It controls the source by its contact two-jet;
complete physical-action cancellation and fixed-clock extinction remain open. -/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMSourceContactRigidity
open D4BMCommonRadialSource D4BMModularCore D4BMHorizon D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private abbrev F (q : XiZeroCopy) : Field := scalar (center q)
private def kappa (q : XiZeroCopy) : ℂ := (3*scalarParameter q-2)/4

/-- The actual angular contact in the original common source producer. -/
def sourceContact (q : XiZeroCopy) (z : Point) : ℂ :=
  ((7*scalarParameter q-2)*fullSquarePotential q z-
    2*scalarLaplacian (fullSquarePotential q) z)/8

private theorem eigen (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    (z 1:ℂ)^2*(coordDeriv 0 (coordDeriv 0 (F q)) z+
      coordDeriv 1 (coordDeriv 1 (F q)) z)=scalarParameter q*F q z := by
  have h := scalar_physical_equation q true z hz
  rw [scalarLaplacian_eq _ z hz] at h
  convert h using 1
  dsimp [scalarParameter,physicalRate]
  ring

/-- The contact retains the full complex bilinear gradient energy. -/
theorem sourceContact_eq (q : XiZeroCopy) (z : UpperHalfPlane) :
    sourceContact q (coordinates z)=
      ((3*scalarParameter q-2)/4*scalar (center q) (coordinates z)^2-
        fullGradientEnergy q (coordinates z))/4 := by
  rw [sourceContact,fullSquarePotential_laplacian q true _ z.im_pos]
  dsimp [fullSquarePotential,scalarParameter,physicalRate]
  ring

private theorem smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (n : ℕ) :
    ContDiffAt ℝ n (F q) z := D4BMAngularSeries.cuspLeg_contDiffAt .scalar (center q) n z hz

private def Y (z : Point) : ℂ := z 1
private def rawContact (q : XiZeroCopy) (z : Point) : ℂ :=
  (1/4:ℂ)*(kappa q*(F q z*F q z)+
    -(Y z*Y z*(coordDeriv 0 (F q) z*coordDeriv 0 (F q) z+
      coordDeriv 1 (F q) z*coordDeriv 1 (F q) z)))

private theorem contact_germ (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    sourceContact q =ᶠ[𝓝 z] rawContact q := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
  rw [sourceContact,fullSquarePotential_laplacian q true w hw]
  dsimp [rawContact,kappa,F,Y,fullSquarePotential,fullGradientEnergy,scalarParameter,physicalRate]
  ring

private theorem jet_germ {f g : Field} {z : Point} (h : f =ᶠ[𝓝 z] g) :
    ofField f z=ofField g z := by
  ext i j
  · exact h.eq_of_nhds
  · exact congrArg (fun L => L (Pi.single i 1)) (h.fderiv_eq (𝕜 := ℝ))
  · have hd : coordDeriv j f =ᶠ[𝓝 z] coordDeriv j g :=
      (h.fderiv (𝕜 := ℝ)).mono (fun _ he => congrArg (fun L => L (Pi.single j 1)) he)
    exact congrArg (fun L => L (Pi.single i 1)) (hd.fderiv_eq (𝕜 := ℝ))

private theorem y_smooth (z : Point) : ContDiffAt ℝ 2 Y z :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp z
    (ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).contDiff.contDiffAt

private theorem y_jet (z : Point) :
    ofField Y z=⟨z 1,![0,1],fun _ _ => 0⟩ := by
  have hd (w : Point) : HasFDerivAt Y
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w
      (ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt
  have hf (j : Fin 2) : coordDeriv j Y=fun _ => if j=1 then 1 else 0 := by
    funext w
    rw [coordDeriv,(hd w).fderiv]
    fin_cases j <;> simp
  ext i j
  · rfl
  · fin_cases i <;> simp [ofField,hf]
  · simp [ofField,hf,coordDeriv]

private def contactJet (q : XiZeroCopy) (z : Point) : ScalarTwoJet (Fin 2) ℂ :=
  (constant (1/4)).mul ((constant (kappa q)).mul ((ofField (F q) z).mul (ofField (F q) z)) |>.add
    (neg (((ofField Y z).mul (ofField Y z)).mul
      (((ofField (coordDeriv 0 (F q)) z).mul (ofField (coordDeriv 0 (F q)) z)).add
        ((ofField (coordDeriv 1 (F q)) z).mul (ofField (coordDeriv 1 (F q)) z))))))

private theorem contact_jet (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    ofField (sourceContact q) z=contactJet q z := by
  have hs := smooth q z hz 2
  have hd (j : Fin 2) : ContDiffAt ℝ 2 (coordDeriv j (F q)) z :=
    coordDeriv_contDiffAt (smooth q z hz 3) (by norm_num) j
  rw [jet_germ (contact_germ q z hz)]
  unfold rawContact contactJet
  rw [ofField_mul contDiffAt_const
    ((contDiffAt_const.mul (hs.mul hs)).add
      (((y_smooth z).mul (y_smooth z)).mul ((hd 0|>.mul (hd 0)).add ((hd 1).mul (hd 1)))).neg),
    ofField_constant,
    ofField_add (contDiffAt_const.mul (hs.mul hs))
      (((y_smooth z).mul (y_smooth z)).mul ((hd 0|>.mul (hd 0)).add ((hd 1).mul (hd 1)))).neg,
    ofField_mul contDiffAt_const (hs.mul hs),ofField_constant,ofField_mul hs hs,
    ofField_neg,
    ofField_mul ((y_smooth z).mul (y_smooth z)) ((hd 0|>.mul (hd 0)).add ((hd 1).mul (hd 1))),
    ofField_mul (y_smooth z) (y_smooth z),
    ofField_add ((hd 0).mul (hd 0)) ((hd 1).mul (hd 1)),
    ofField_mul (hd 0) (hd 0),ofField_mul (hd 1) (hd 1)]

private theorem contact_algebra (f u v a b c lam : ℂ) (ht : a+c=lam*f) :
    let E := u^2+v^2;
    let k := (3*lam-2)/4;
    let J := (k*f^2-E)/4;
    let Jx := (k*f*u-a*u-b*v)/2;
    let Jy := (k*f*v-b*u-c*v)/2;
    let LJ := (k*lam*f^2+(k-lam+1)*E-(a^2+2*b^2+c^2))/2;
    (lam-2)*(lam-6)*f^2*E=
      16*(lam-2)*(2*f*(u*Jx+v*Jy)+J*E)-32*E*LJ-128*(Jx^2+Jy^2) := by
  have hc : c=lam*f-a := by linear_combination ht
  rw [hc]
  dsimp only
  ring

private theorem gradient_smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (j : Fin 2) :
    ContDiffAt ℝ 2 (coordDeriv j (F q)) z :=
  coordDeriv_contDiffAt (smooth q z hz 3) (by norm_num) j

private theorem eigen_first (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (i : Fin 2) :
    (z 1:ℂ)^2*(coordDeriv i (coordDeriv 0 (coordDeriv 0 (F q))) z+
      coordDeriv i (coordDeriv 1 (coordDeriv 1 (F q))) z)+
      (if i=1 then 2*(z 1:ℂ) else 0)*
        (coordDeriv 0 (coordDeriv 0 (F q)) z+coordDeriv 1 (coordDeriv 1 (F q)) z)=
      scalarParameter q*coordDeriv i (F q) z := by
  have he : (fun w => Y w*Y w*(coordDeriv 0 (coordDeriv 0 (F q)) w+
      coordDeriv 1 (coordDeriv 1 (F q)) w)) =ᶠ[𝓝 z] (fun w => scalarParameter q*F q w) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    simpa [Y,pow_two] using eigen q w hw
  have hd (j : Fin 2) : DifferentiableAt ℝ (coordDeriv j (coordDeriv j (F q))) z :=
    (ScalarTwoJet.coordDeriv_contDiffAt (gradient_smooth q z hz j) (m := 1)
      (by norm_num) j).differentiableAt (by norm_num)
  have hy : HasFDerivAt Y (Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z
      (ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt
  have hleft := (hy.mul hy).mul ((hd 0).hasFDerivAt.add (hd 1).hasFDerivAt)
  change HasFDerivAt (fun w => Y w*Y w*(coordDeriv 0 (coordDeriv 0 (F q)) w+
    coordDeriv 1 (coordDeriv 1 (F q)) w)) _ z at hleft
  have hright := ((smooth q z hz 1).differentiableAt (by norm_num)).hasFDerivAt.const_mul (scalarParameter q)
  have hh := congrArg (fun L => L (Pi.single i 1)) (he.fderiv_eq (𝕜 := ℝ))
  rw [hleft.fderiv,hright.fderiv] at hh
  fin_cases i <;> simp [Y,coordDeriv,smul_eq_mul] at hh ⊢ <;> linear_combination hh

private theorem third_shuffle (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (i j : Fin 2) :
    coordDeriv i (coordDeriv i (coordDeriv j (F q))) z=
      coordDeriv j (coordDeriv i (coordDeriv i (F q))) z := by
  have he : coordDeriv i (coordDeriv j (F q)) =ᶠ[𝓝 z] coordDeriv j (coordDeriv i (F q)) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    exact coordDeriv_comm (smooth q w hw 2) i j
  have h := congrArg (fun L => L (Pi.single i 1)) (he.fderiv_eq (𝕜 := ℝ))
  exact h.trans (coordDeriv_comm (gradient_smooth q z hz i) i j)

private def hessian (q : XiZeroCopy) (z : Point) : Fin 3 → ℂ :=
  ![(z 1:ℂ)^2*coordDeriv 0 (coordDeriv 0 (F q)) z-(z 1:ℂ)*coordDeriv 1 (F q) z,
    (z 1:ℂ)^2*coordDeriv 0 (coordDeriv 1 (F q)) z+(z 1:ℂ)*coordDeriv 0 (F q) z,
    (z 1:ℂ)^2*coordDeriv 1 (coordDeriv 1 (F q)) z+(z 1:ℂ)*coordDeriv 1 (F q) z]

private theorem contact_first (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    (z 1:ℂ)*coordDeriv 0 (sourceContact q) z=
      (kappa q*F q z*((z 1:ℂ)*coordDeriv 0 (F q) z)-
        hessian q z 0*((z 1:ℂ)*coordDeriv 0 (F q) z)-
        hessian q z 1*((z 1:ℂ)*coordDeriv 1 (F q) z))/2 ∧
    (z 1:ℂ)*coordDeriv 1 (sourceContact q) z=
      (kappa q*F q z*((z 1:ℂ)*coordDeriv 1 (F q) z)-
        hessian q z 1*((z 1:ℂ)*coordDeriv 0 (F q) z)-
        hessian q z 2*((z 1:ℂ)*coordDeriv 1 (F q) z))/2 := by
  have hc := coordDeriv_comm (smooth q z hz 2) 1 0
  have hj := contact_jet q z hz
  unfold contactJet at hj
  rw [y_jet] at hj
  have h0 := congrArg (fun J => J.first 0) hj
  have h1 := congrArg (fun J => J.first 1) hj
  simp only [ofField,ScalarTwoJet.mul,ScalarTwoJet.add,ScalarTwoJet.neg,constant,
    Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  dsimp [hessian]
  constructor
  · linear_combination (z 1:ℂ)*h0
  · rw [hc] at h1
    linear_combination (z 1:ℂ)*h1

private theorem contact_laplacian (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (sourceContact q) z=
      (kappa q*scalarParameter q*(F q z)^2+
        (kappa q-scalarParameter q+1)*fullGradientEnergy q z-
        (hessian q z 0^2+2*hessian q z 1^2+hessian q z 2^2))/2 := by
  have hj := contact_jet q z hz
  unfold contactJet at hj
  rw [y_jet] at hj
  have h0 := congrArg (fun J => J.second 0 0) hj
  have h1 := congrArg (fun J => J.second 1 1) hj
  simp only [ofField,ScalarTwoJet.mul,ScalarTwoJet.add,ScalarTwoJet.neg,constant,
    Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  have hc := coordDeriv_comm (smooth q z hz 2) 1 0
  have ht := eigen q z hz
  have hx := eigen_first q z hz 0
  have hy := eigen_first q z hz 1
  simp only [Fin.isValue,zero_ne_one,if_false,if_true,zero_mul,add_zero] at hx hy
  rw [third_shuffle q z hz 0 1] at h0
  rw [third_shuffle q z hz 1 0,hc] at h1
  rw [scalarLaplacian_eq _ z hz]
  dsimp [fullGradientEnergy,hessian]
  linear_combination (z 1:ℂ)^2*(h0+h1)+kappa q/2*F q z*ht-
    (z 1:ℂ)^2/2*coordDeriv 0 (F q) z*hx-
    (z 1:ℂ)^2/2*coordDeriv 1 (F q) z*hy

/-- Complex bilinear gradient pairing of the actual theta scalar with its source contact. -/
def scalarContactGradientPair (q : XiZeroCopy) (z : Point) : ℂ :=
  (z 1:ℂ)^2*(coordDeriv 0 (scalar (center q)) z*coordDeriv 0 (sourceContact q) z+
    coordDeriv 1 (scalar (center q)) z*coordDeriv 1 (sourceContact q) z)

/-- Complex bilinear gradient square of the original source contact. No conjugation is inserted. -/
def contactGradientEnergy (q : XiZeroCopy) (z : Point) : ℂ :=
  (z 1:ℂ)^2*(coordDeriv 0 (sourceContact q) z^2+coordDeriv 1 (sourceContact q) z^2)

/-- Exact differential rigidity identity for the literal theta contact. All derivatives and
the scalar equation are discharged from the original source, without a clock or sign premise. -/
private theorem contact_identity (q : XiZeroCopy) (z : UpperHalfPlane) :
    (scalarParameter q-2)*(scalarParameter q-6)*
        scalar (center q) (coordinates z)^2*fullGradientEnergy q (coordinates z)=
      16*(scalarParameter q-2)*
        (2*scalar (center q) (coordinates z)*scalarContactGradientPair q (coordinates z)+
          sourceContact q (coordinates z)*fullGradientEnergy q (coordinates z))-
      32*fullGradientEnergy q (coordinates z)*scalarLaplacian (sourceContact q) (coordinates z)-
      128*contactGradientEnergy q (coordinates z) := by
  let p := coordinates z
  have hp : 0 < p 1 := z.im_pos
  have ht : hessian q p 0+hessian q p 2=scalarParameter q*F q p := by
    dsimp [hessian]
    linear_combination eigen q p hp
  have hE : ((p 1:ℂ)*coordDeriv 0 (F q) p)^2+
      ((p 1:ℂ)*coordDeriv 1 (F q) p)^2=fullGradientEnergy q p := by
    dsimp [fullGradientEnergy,F]
    ring
  have hJ : (kappa q*F q p^2-fullGradientEnergy q p)/4=sourceContact q p := by
    dsimp [kappa,F,p]
    exact (sourceContact_eq q z).symm
  have ha := contact_algebra (F q p) ((p 1:ℂ)*coordDeriv 0 (F q) p)
    ((p 1:ℂ)*coordDeriv 1 (F q) p) (hessian q p 0) (hessian q p 1)
    (hessian q p 2) (scalarParameter q) ht
  dsimp only at ha
  rw [show (3*scalarParameter q-2)/4=kappa q from rfl] at ha
  rw [hE,hJ,← (contact_first q p hp).1,← (contact_first q p hp).2,
    ← contact_laplacian q p hp] at ha
  convert! ha using 1
  dsimp [scalarContactGradientPair,contactGradientEnergy,F,p]
  ring

/-- The original theta scalar is controlled by its complete angular contact two-jet.
The identity uses the actual source and carries no source equation, sign, or clock premise. -/
theorem sourceContact_differential_identity (q : XiZeroCopy) (z : UpperHalfPlane) :
    (scalarParameter q-2)*(scalarParameter q-6)*(3*scalarParameter q-2)*
        scalar (center q) (coordinates z)^4=
      16*(scalarParameter q-2)*(scalarParameter q-6)*
        scalar (center q) (coordinates z)^2*sourceContact q (coordinates z)+
      64*(scalarParameter q-2)*
        (2*scalar (center q) (coordinates z)*scalarContactGradientPair q (coordinates z)+
          sourceContact q (coordinates z)*fullGradientEnergy q (coordinates z))-
      128*fullGradientEnergy q (coordinates z)*scalarLaplacian (sourceContact q) (coordinates z)-
      512*contactGradientEnergy q (coordinates z) := by
  linear_combination 4*contact_identity q z-
    16*(scalarParameter q-2)*(scalarParameter q-6)*
      scalar (center q) (coordinates z)^2*sourceContact_eq q z

/-- Every actual Xi occurrence avoids all three exceptional local contact eigenvalues. -/
theorem sourceContact_rigidity_factor_ne_zero (q : XiZeroCopy) :
    (scalarParameter q-2)*(scalarParameter q-6)*(3*scalarParameter q-2) ≠ 0 := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  have hprod : (q.1:ℂ).re*((q.1:ℂ).re-1) < 0 :=
    mul_neg_of_pos_of_neg hq.1 (sub_neg.mpr hq.2)
  have hl : (scalarParameter q).re < 0 := by
    simp only [scalarParameter,Complex.mul_re,Complex.sub_re,Complex.sub_im,
      Complex.one_re,Complex.one_im,sub_zero]
    nlinarith [sq_nonneg (q.1:ℂ).im]
  have h2 : scalarParameter q-2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have h6 : scalarParameter q-6 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have h3 : 3*scalarParameter q-2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.mul_re] at hh
    linarith
  exact mul_ne_zero (mul_ne_zero h2 h6) h3

end
end RHTower.D4BMSourceContactRigidity
