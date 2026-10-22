import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeAngularGreen

/-! The original mixed-source causal potential, with the fixed onset lift restored. -/
open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMOriginalCausalPotential
open GaloisForLFunctions.HTGeometry D4BMNativeResponse D4BMNativeCircle
open D4BMJointSource D4BMModularCore D4BMHorizon
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace


def sourceProfile (q : XiZeroCopy) (X k : ℝ) : ℂ :=
  fullSquarePotential q ![X,Real.exp k]

def angularLaplacian (F : ℝ → ℝ → ℂ) (X k : ℝ) : ℂ :=
  (Real.exp k:ℂ)^(2 : ℕ)*deriv (deriv (fun x => F x k)) X+
    deriv (deriv (fun y => F X y)) k-deriv (fun y => F X y) k

def nullLift (s a : ℂ) (p r : ℝ) : ℂ :=
  radialLift s 0 a 1 ((p-r)/2)*timeOnset (2*s) p

def nullLiftFirst (s a : ℂ) (p r : ℝ) : ℂ :=
  radialLiftFirst s 0 a 1 ((p-r)/2)*timeOnset (2*s) p/2+
    radialLift s 0 a 1 ((p-r)/2)*timeOnsetFirst (2*s) p

def nullLiftMixed (s a : ℂ) (p r : ℝ) : ℂ :=
  -radialLiftSecond s 0 a 1 ((p-r)/2)*timeOnset (2*s) p/4-
    radialLiftFirst s 0 a 1 ((p-r)/2)*timeOnsetFirst (2*s) p/2

private theorem lift_first (s a : ℂ) (p r : ℝ) :
    HasDerivAt (fun u => nullLift s a u r) (nullLiftFirst s a p r) p := by
  have ht := ((hasDerivAt_id p).sub_const r).div_const 2
  have hL := (radialLift_hasDerivAt s 0 a 1 ((p-r)/2)).scomp p ht
  apply (hL.mul (timeOnset_hasDerivAt (2*s) p)).congr_deriv
  dsimp only [nullLiftFirst]
  simp only [Function.comp_apply,id_eq,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

private theorem lift_mixed (s a : ℂ) (p r : ℝ) :
    HasDerivAt (fun b => nullLiftFirst s a p b) (nullLiftMixed s a p r) r := by
  have ht := ((hasDerivAt_id r).const_sub p).div_const 2
  have hL := (radialLift_hasDerivAt s 0 a 1 ((p-r)/2)).scomp r ht
  have hL1 := (radialLiftFirst_hasDerivAt s 0 a 1 ((p-r)/2)).scomp r ht
  apply (((hL1.mul_const (timeOnset (2*s) p)).div_const 2).add
    (hL.mul_const (timeOnsetFirst (2*s) p))).congr_deriv
  dsimp only [nullLiftMixed]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

private theorem sourceProfile_smooth (q : XiZeroCopy) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => sourceProfile q z.1 z.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hf : ContDiffAt ℝ ∞ (fullSquarePotential q) ![z.1,Real.exp z.2] :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ (Real.exp_pos _) n)
  apply hf.comp z
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => x.1) z
    fun_prop
  · change ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => Real.exp x.2) z
    fun_prop

private theorem sourceProfile_laplacian (q : XiZeroCopy) (X k : ℝ) :
    angularLaplacian (sourceProfile q) X k=
      scalarLaplacian (fullSquarePotential q) ![X,Real.exp k] := by
  have h := mean_laplacian_commutes q 0 X k
  have he : (fun theta => scalarLaplacian (fullSquarePotential q) (logCircle 0 theta X k))=
      fun _ => scalarLaplacian (fullSquarePotential q) ![X,Real.exp k] := by
    funext theta
    simp [logCircle,circle,offset,height,denominator]
  simp only [mean_zero] at h
  rw [he] at h
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp only [D4BMNativeCircle.average] at h
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)] at h
  simp only [intervalIntegral.integral_const,sub_zero,Complex.real_smul,
    Complex.ofReal_mul,Complex.ofReal_ofNat] at h
  change angularLaplacian (sourceProfile q) X k=_ at h
  convert! h using 1
  field_simp [hpi]

private theorem second_add {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    deriv (deriv (fun y => f y+g y)) x=deriv (deriv f) x+deriv (deriv g) x := by
  have he : deriv (fun y => f y+g y)=fun y => deriv f y+deriv g y :=
    funext (fun y => deriv_add (hf.differentiable (by simp) y) (hg.differentiable (by simp) y))
  rw [he]
  exact deriv_add ((contDiff_infty.mp hf 2).differentiable_deriv_two x)
    ((contDiff_infty.mp hg 2).differentiable_deriv_two x)

private theorem angularLaplacian_add {F G : ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (fun z : ℝ × ℝ => F z.1 z.2))
    (hG : ContDiff ℝ ∞ (fun z : ℝ × ℝ => G z.1 z.2)) (X k : ℝ) :
    angularLaplacian (fun x y => F x y+G x y) X k=
      angularLaplacian F X k+angularLaplacian G X k := by
  have hxF : ContDiff ℝ ∞ (fun x => F x k) := hF.comp (show ContDiff ℝ ∞ (fun x : ℝ => (x,k)) by fun_prop)
  have hxG : ContDiff ℝ ∞ (fun x => G x k) := hG.comp (show ContDiff ℝ ∞ (fun x : ℝ => (x,k)) by fun_prop)
  have hkF : ContDiff ℝ ∞ (fun y => F X y) := hF.comp (show ContDiff ℝ ∞ (fun y : ℝ => (X,y)) by fun_prop)
  have hkG : ContDiff ℝ ∞ (fun y => G X y) := hG.comp (show ContDiff ℝ ∞ (fun y : ℝ => (X,y)) by fun_prop)
  dsimp only [angularLaplacian]
  have h1 : deriv (fun y => F X y+G X y) k=deriv (fun y => F X y) k+deriv (fun y => G X y) k :=
    ((hkF.differentiable (by simp) k).hasDerivAt.add
      (hkG.differentiable (by simp) k).hasDerivAt).deriv
  rw [second_add hxF hxG,second_add hkF hkG,h1]
  ring

private theorem angularLaplacian_const_mul (c : ℂ) (F : ℝ → ℝ → ℂ) (X k : ℝ) :
    angularLaplacian (fun x y => c*F x y) X k=c*angularLaplacian F X k := by
  simp only [angularLaplacian,deriv_const_mul_field',deriv_const_mul_field]
  ring

private theorem radial_metric (t : ℝ) : 1-(radialUnit t:ℂ)^(2 : ℕ)=1/(Real.cosh t:ℂ)^(2 : ℕ) := by
  have hn : (Real.cosh t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
  have he : (Real.cosh t:ℂ)^(2 : ℕ)-(Real.sinh t:ℂ)^(2 : ℕ)=1 := by exact_mod_cast Real.cosh_sq_sub_sinh_sq t
  dsimp only [radialUnit]
  simp only [Complex.ofReal_div,Complex.ofReal_neg]
  field_simp [hn]
  linear_combination he

private theorem lift_original_source (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p r X k : ℝ) :
    4*nullLiftMixed (physicalRate q branch) a p r*sourceProfile q X k-
      nullLift (physicalRate q branch) a p r*angularLaplacian (sourceProfile q) X k/
        (Real.cosh ((p-r)/2):ℂ)^(2 : ℕ)+
      timeReducedCoefficient (physicalRate q branch) a ((p+r)/2) ((p-r)/2)*sourceProfile q X k=
        timeOriginalForcing q branch a ((p+r)/2) ((p-r)/2) ![X,Real.exp k] := by
  have h := timeOriginalForcing_gradient_absorption q branch a ((p+r)/2) ((p-r)/2)
    ![X,Real.exp k] (Real.exp_pos k)
  rw [timeLiftField_wave q branch a _ _ _ (Real.exp_pos k),separatedScalarWave,
    (radialLift_derivatives (physicalRate q branch) 0 a 1).2,radial_metric] at h
  rw [sourceProfile_laplacian]
  dsimp only [nullLiftMixed,nullLift,sourceProfile]
  simp only [show (p+r)/2+(p-r)/2=p by ring] at h
  convert! h.symm using 1
  ring

/-- The complete native causal potential, with the original gradient-absorbing
lift restored at its fixed ingoing onset. -/
def originalPotential (q : XiZeroCopy) (branch : Bool) (a : ℂ) (p r X k : ℝ) : ℂ :=
  fullNullResponse q (physicalRate q branch) a p r X k+
    nullLift (physicalRate q branch) a p r*sourceProfile q X k

/-- All angular derivatives of the full restored causal potential exist. -/
theorem originalPotential_angular_smooth (q : XiZeroCopy) (branch : Bool) (a : ℂ) (p r : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => originalPotential q branch a p r z.1 z.2) :=
  (fullNullResponse_angular_smooth q (physicalRate q branch) a p r).add
    (contDiff_const.mul (sourceProfile_smooth q))

/-- The restored potential has its genuine first null derivative. -/
theorem originalPotential_first (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    {p r : ℝ} (hp : 0 < p) (hr : 0 ≤ r) (X k : ℝ) :
    HasDerivAt (fun u => originalPotential q branch a u r X k)
      (deriv (fun u => fullNullResponse q (physicalRate q branch) a u r X k) p+
        nullLiftFirst (physicalRate q branch) a p r*sourceProfile q X k) p :=
  (fullNullResponse_differentiable_first q (physicalRate q branch) a hp hr X k).hasDerivAt.add
    ((lift_first (physicalRate q branch) a p r).mul_const (sourceProfile q X k))

/-- The restored potential has its genuine mixed null derivative, including the lift. -/
theorem originalPotential_mixed (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    {p r : ℝ} (hp : 0 < p) (hr : 0 < r) (X k : ℝ) :
    HasDerivAt (fun b => deriv (fun u => originalPotential q branch a u b X k) p)
      (deriv (fun b => deriv (fun u => fullNullResponse q (physicalRate q branch) a u b X k) p) r+
        nullLiftMixed (physicalRate q branch) a p r*sourceProfile q X k) r := by
  have hd := (fullNullResponse_differentiable_mixed q (physicalRate q branch) a hp hr X k).hasDerivAt.add
    ((lift_mixed (physicalRate q branch) a p r).mul_const (sourceProfile q X k))
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hr] with b hb
  exact (originalPotential_first q branch a hp hb.le X k).deriv

/-- The constructed causal potential satisfies the complete original source equation
on the physical negative radial ray. The fixed onset and gradient source are retained. -/
theorem originalPotential_wave (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    {p r : ℝ} (hp : 0 < p) (hpr : p ≤ r) (X k : ℝ) :
    4*deriv (fun b => deriv (fun u => originalPotential q branch a u b X k) p) r-
      angularLaplacian (originalPotential q branch a p r) X k/(Real.cosh ((p-r)/2):ℂ)^(2 : ℕ)=
        timeOriginalForcing q branch a ((p+r)/2) ((p-r)/2) ![X,Real.exp k] := by
  have hr := hp.trans_le hpr
  have hU := fullNullResponse_wave q (physicalRate q branch) a hp hr X k
  have hL := lift_original_source q branch a p r X k
  have hneg : (p-r)/2 ≤ 0 := by linarith
  have ho : oddSource (physicalRate q branch) a ((p+r)/2) ((p-r)/2)=
      timeReducedCoefficient (physicalRate q branch) a ((p+r)/2) ((p-r)/2) := by
    simp only [oddSource,min_eq_left hneg,min_eq_right (neg_nonneg.mpr hneg),source_boundary,sub_zero]
  rw [ho] at hU
  rw [(originalPotential_mixed q branch a hp hr X k).deriv]
  have he : angularLaplacian (originalPotential q branch a p r) X k=
      angularLaplacian (fullNullResponse q (physicalRate q branch) a p r) X k+
        nullLift (physicalRate q branch) a p r*angularLaplacian (sourceProfile q) X k := by
    change angularLaplacian (fun x y => fullNullResponse q (physicalRate q branch) a p r x y+
      nullLift (physicalRate q branch) a p r*sourceProfile q x y) X k=_
    rw [angularLaplacian_add
      (fullNullResponse_angular_smooth q (physicalRate q branch) a p r)
      (contDiff_const.mul (sourceProfile_smooth q)),angularLaplacian_const_mul]
  rw [he]
  change _=(1/4:ℂ)*(sourceProfile q X k*_) +
    angularLaplacian (fullNullResponse q (physicalRate q branch) a p r) X k/
      (4*(Real.cosh ((p-r)/2):ℂ)^(2 : ℕ)) at hU
  linear_combination 4*hU+hL

/-- Restoring the original lift preserves the actual AdS Dirichlet value. -/
theorem originalPotential_boundary (q : XiZeroCopy) (branch : Bool) (a : ℂ) (p X k : ℝ) :
    originalPotential q branch a p p X k=0 := by
  simp [originalPotential,fullNullResponse_boundary,nullLift,radialLift,radialUnit]

/-- The full original-source causal potential vanishes before the fixed ingoing onset. -/
theorem originalPotential_before_onset (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    {p r : ℝ} (hp : p ≤ 0) (X k : ℝ) : originalPotential q branch a p r X k=0 := by
  rw [originalPotential,fullNullResponse_nonpositive q (physicalRate q branch) a (Or.inl hp)]
  simp only [nullLift,timeOnset_zero_of_nonpos (2*physicalRate q branch) hp,mul_zero,zero_mul,add_zero]

/-- The original-source lift preserves modular invariance of the full causal potential. -/
theorem originalPotential_modular (q : XiZeroCopy) (branch : Bool) (a : ℂ) (p r : ℝ)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    originalPotential q branch a p r (A • z).re (Real.log (A • z).im)=
      originalPotential q branch a p r z.re (Real.log z.im) := by
  simp only [originalPotential,fullNullResponse_modular,sourceProfile,
    Real.exp_log (A • z).im_pos,Real.exp_log z.im_pos]
  rw [show fullSquarePotential q ![(A • z).re,(A • z).im]=
    fullSquarePotential q ![z.re,z.im] from fullSquarePotential_modular q A z]

end
end RHTower.D4BMOriginalCausalPotential
