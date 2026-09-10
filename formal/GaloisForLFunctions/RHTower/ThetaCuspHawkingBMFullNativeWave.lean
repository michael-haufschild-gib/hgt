import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeGoursat
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeForcedIntegral
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativePhysicalIdentification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCutoffPowerHeight
import GaloisForLFunctions.HTGeometry.ClockParametricDerivative
import Mathlib.MeasureTheory.Integral.Prod

/-! The complete theta-source causal integral satisfies its forced wave equation.

Smooth angular source derivatives pass through the circle and source integrals. The original
full-kernel Goursat equation, causal Fubini interchange and endpoint FTC give the actual mixed
null derivative. Kernel reflection and the original odd source impose the Dirichlet boundary.
The continuous kernel extension is removed throughout every forward source rectangle.
Subtracting the three physical principal coefficients yields the exact cutoff-residual equation
with its actual angular derivatives, original cutoff commutators and Dirichlet boundary.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMNativeResponse
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMNativeCircle D4BMCausalKernel D4BMJointSource D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private def sourceJet (q : XiZeroCopy) (i : Fin 4) : ℕ → (Fin 4 → ℝ) → ℂ
  | 0 => fun p => source q (p 0) (p 1) (p 2) (p 3)
  | n+1 => fun p => fderiv ℝ (sourceJet q i n) p (Pi.single i 1)

private theorem sourceJet_smooth (q : XiZeroCopy) (i : Fin 4) (n : ℕ) :
    ContDiff ℝ ∞ (sourceJet q i n) := by
  induction n with
  | zero => exact source_smooth q
  | succ n ih =>
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (ih.contDiffAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

private theorem sourceJet_x (q : XiZeroCopy) (n : ℕ) (d theta X k : ℝ) :
    HasDerivAt (fun x => sourceJet q 2 n ![d,theta,x,k])
      (sourceJet q 2 (n+1) ![d,theta,X,k]) X := by
  have hp : HasDerivAt (fun x : ℝ => ![d,theta,x,k]) (Pi.single (2:Fin 4) 1) X := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> simp <;> first | exact hasDerivAt_const _ _ | exact hasDerivAt_id _
  exact ((sourceJet_smooth q 2 n).contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt X hp

private theorem sourceJet_k (q : XiZeroCopy) (n : ℕ) (d theta X k : ℝ) :
    HasDerivAt (fun x => sourceJet q 3 n ![d,theta,X,x])
      (sourceJet q 3 (n+1) ![d,theta,X,k]) k := by
  have hp : HasDerivAt (fun x : ℝ => ![d,theta,X,x]) (Pi.single (3:Fin 4) 1) k := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> simp <;> first | exact hasDerivAt_const _ _ | exact hasDerivAt_id _
  exact ((sourceJet_smooth q 3 n).contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k hp

private def circleJet (q : XiZeroCopy) (i : Fin 4) (n : ℕ) (d X k : ℝ) : ℂ :=
  (1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..(2*Real.pi), sourceJet q i n ![d,theta,X,k]

private theorem circleJet_continuous (q : XiZeroCopy) (i : Fin 4) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ => circleJet q i n p.1 p.2.1 p.2.2) := by
  have hc : Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ =>
      sourceJet q i n ![p.1.1,p.2,p.1.2.1,p.1.2.2]) :=
    (sourceJet_smooth q i n).continuous.comp (by fun_prop)
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 (2*Real.pi))

private theorem circleJet_zero (q : XiZeroCopy) (i : Fin 4) (d X k : ℝ) :
    circleJet q i 0 d X k = mean q d X k := by
  unfold circleJet mean D4BMNativeCircle.average
  rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  rfl

private theorem circleJet_x (q : XiZeroCopy) (n : ℕ) (d X k : ℝ) :
    HasDerivAt (fun x => circleJet q 2 n d x k) (circleJet q 2 (n+1) d X k) X := by
  apply HasDerivAt.const_mul
  apply hasDerivAt_parametric_intervalIntegral
    (f := fun x theta => sourceJet q 2 n ![d,theta,x,k])
    (f' := fun x theta => sourceJet q 2 (n+1) ![d,theta,x,k])
  · exact (sourceJet_smooth q 2 n).continuous.comp (by fun_prop)
  · exact (sourceJet_smooth q 2 (n+1)).continuous.comp (by fun_prop)
  · intro x theta; exact sourceJet_x q n d theta x k

private theorem circleJet_k (q : XiZeroCopy) (n : ℕ) (d X k : ℝ) :
    HasDerivAt (fun x => circleJet q 3 n d X x) (circleJet q 3 (n+1) d X k) k := by
  apply HasDerivAt.const_mul
  apply hasDerivAt_parametric_intervalIntegral
    (f := fun x theta => sourceJet q 3 n ![d,theta,X,x])
    (f' := fun x theta => sourceJet q 3 (n+1) ![d,theta,X,x])
  · exact (sourceJet_smooth q 3 n).continuous.comp (by fun_prop)
  · exact (sourceJet_smooth q 3 (n+1)).continuous.comp (by fun_prop)
  · intro x theta; exact sourceJet_k q n d theta X x


@[fun_prop] private theorem integral_continuous {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (f : X → ℝ → ℂ) (hf : Continuous (Function.uncurry f))
    (l r : X → ℝ) (hl : Continuous l) (hr : Continuous r) :
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

private def nullRadius (p r a b : ℝ) : ℝ :=
  Real.arcosh (max 1 (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)))

@[fun_prop] private theorem nullRadius_continuous :
    Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => nullRadius z.1.1 z.1.2 z.2.1 z.2.2) := by
  apply Real.continuousOn_arcosh.comp_continuous
  · unfold invariant
    apply Continuous.max continuous_const
    apply Continuous.div <;> try fun_prop
    intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  · intro z; change (1:ℝ) ≤ max 1 _; exact le_max_left (1:ℝ) _

private theorem null_cone {p r a b : ℝ} (ha : a ≤ p) (hb : b ≤ r) :
    |(p-r)/2-(a-b)/2| ≤ (p+r-a-b)/2 := by
  rw [abs_le]
  constructor <;> linarith

private theorem nullRadius_eq {p r a b : ℝ} (ha : a ≤ p) (hb : b ≤ r) :
    nullRadius p r a b = Real.arcosh (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)) := by
  rw [nullRadius,max_eq_right (invariant_causal ⟨_,_,_,null_cone ha hb⟩)]

private def kernelJet (q : XiZeroCopy) (i : Fin 4) (n : ℕ) (p r a b X k : ℝ) : ℂ :=
  circleJet q i n (nullRadius p r a b) X k

@[fun_prop] private theorem kernelJet_continuous (q : XiZeroCopy) (i : Fin 4) (n : ℕ) :
    Continuous (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × (ℝ × ℝ) =>
      kernelJet q i n z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2.1 z.2.2) :=
  (circleJet_continuous q i n).comp
    ((nullRadius_continuous.comp continuous_fst).prodMk continuous_snd)

@[fun_prop] private theorem kernelJet_comp {P : Type*} [TopologicalSpace P]
    (q : XiZeroCopy) (i : Fin 4) (n : ℕ) (p r a b X k : P → ℝ)
    (hp : Continuous p) (hr : Continuous r) (ha : Continuous a) (hb : Continuous b)
    (hX : Continuous X) (hk : Continuous k) :
    Continuous (fun z => kernelJet q i n (p z) (r z) (a z) (b z) (X z) (k z)) := by
  have hc := (kernelJet_continuous q i n).comp
    (((hp.prodMk hr).prodMk (ha.prodMk hb)).prodMk (hX.prodMk hk))
  convert! hc using 1

private theorem kernelJet_zero_eq (q : XiZeroCopy) (i : Fin 4) {p r a b : ℝ}
    (ha : a ≤ p) (hb : b ≤ r) (X k : ℝ) :
    kernelJet q i 0 p r a b X k =
      nativeRiemannKernel q ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2) X k := by
  rw [kernelJet,circleJet_zero,nullRadius_eq ha hb]
  rfl

private theorem actualSource_continuous (s amplitude : ℂ) :
    Continuous (fun z : ℝ × ℝ => oddSource s amplitude z.1 z.2) := by
  have h₁ := (timeReducedCoefficient_joint_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min z.2 0)) by fun_prop)
  have h₂ := (timeReducedCoefficient_joint_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min (-z.2) 0)) by fun_prop)
  convert! h₁.sub h₂ using 1

private def nullSource (s amplitude : ℂ) (a b : ℝ) : ℂ :=
  oddSource s amplitude ((a+b)/2) ((a-b)/2)

@[fun_prop] private theorem nullSource_continuous (s amplitude : ℂ) :
    Continuous (fun z : ℝ × ℝ => nullSource s amplitude z.1 z.2) := by
  have hc := (actualSource_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  convert! hc using 1

@[fun_prop] private theorem nullSource_comp {P : Type*} [TopologicalSpace P]
    (s amplitude : ℂ) (a b : P → ℝ) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun z => nullSource s amplitude (a z) (b z)) := by
  have hc := (nullSource_continuous s amplitude).comp (ha.prodMk hb)
  convert! hc using 1

private def responseJet (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 4) (n : ℕ)
    (p r X k : ℝ) : ℂ :=
  (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
    kernelJet q i n p r a b X k*nullSource s amplitude a b

@[fun_prop] private theorem responseJet_continuous (q : XiZeroCopy) (s amplitude : ℂ)
    (i : Fin 4) (n : ℕ) :
    Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => responseJet q s amplitude i n z.1.1 z.1.2 z.2.1 z.2.2) := by
  unfold responseJet
  fun_prop

/-- Full theta-source response in null coordinates. On the forward source rectangle,
the continuous kernel extension is exactly the original native Riemann kernel. -/
def fullNullResponse (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) : ℂ :=
  responseJet q s amplitude 2 0 p r X k

private theorem responseJet_zero (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 4)
    (p r X k : ℝ) : responseJet q s amplitude i 0 p r X k = fullNullResponse q s amplitude p r X k := by
  simp only [responseJet,kernelJet,circleJet_zero,fullNullResponse]

private theorem responseJet_x (q : XiZeroCopy) (s amplitude : ℂ) (n : ℕ) (p r X k : ℝ) :
    HasDerivAt (fun x => responseJet q s amplitude 2 n p r x k)
      (responseJet q s amplitude 2 (n+1) p r X k) X := by
  apply HasDerivAt.const_mul
  apply hasDerivAt_parametric_intervalIntegral
    (f := fun x a => ∫ b in (0:ℝ)..r, kernelJet q 2 n p r a b x k*nullSource s amplitude a b)
    (f' := fun x a => ∫ b in (0:ℝ)..r, kernelJet q 2 (n+1) p r a b x k*nullSource s amplitude a b)
  · fun_prop
  · fun_prop
  · intro x a
    apply hasDerivAt_parametric_intervalIntegral
      (f := fun x b => kernelJet q 2 n p r a b x k*nullSource s amplitude a b)
      (f' := fun x b => kernelJet q 2 (n+1) p r a b x k*nullSource s amplitude a b)
    · fun_prop
    · fun_prop
    · intro x b
      exact (circleJet_x q n (nullRadius p r a b) x k).mul_const _

private theorem responseJet_k (q : XiZeroCopy) (s amplitude : ℂ) (n : ℕ) (p r X k : ℝ) :
    HasDerivAt (fun x => responseJet q s amplitude 3 n p r X x)
      (responseJet q s amplitude 3 (n+1) p r X k) k := by
  apply HasDerivAt.const_mul
  apply hasDerivAt_parametric_intervalIntegral
    (f := fun x a => ∫ b in (0:ℝ)..r, kernelJet q 3 n p r a b X x*nullSource s amplitude a b)
    (f' := fun x a => ∫ b in (0:ℝ)..r, kernelJet q 3 (n+1) p r a b X x*nullSource s amplitude a b)
  · fun_prop
  · fun_prop
  · intro x a
    apply hasDerivAt_parametric_intervalIntegral
      (f := fun x b => kernelJet q 3 n p r a b X x*nullSource s amplitude a b)
      (f' := fun x b => kernelJet q 3 (n+1) p r a b X x*nullSource s amplitude a b)
    · fun_prop
    · fun_prop
    · intro x b
      exact (circleJet_k q n (nullRadius p r a b) X x).mul_const _

/-- The response retains the original full theta kernel and original odd source on
the entire closed source rectangle. -/
theorem fullNullResponse_native (q : XiZeroCopy) (s amplitude : ℂ) {p r : ℝ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) (X k : ℝ) :
    fullNullResponse q s amplitude p r X k =
      (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        nativeRiemannKernel q ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2) X k*
          oddSource s amplitude ((a+b)/2) ((a-b)/2) := by
  unfold fullNullResponse responseJet
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  have ha' : a ≤ p := (show a ∈ Icc 0 p by simpa [uIcc_of_le hp] using ha).2
  apply intervalIntegral.integral_congr
  intro b hb
  have hb' : b ≤ r := (show b ∈ Icc 0 r by simpa [uIcc_of_le hr] using hb).2
  dsimp only
  rw [kernelJet_zero_eq q 2 ha' hb']
  rfl

private def kernelAction (q : XiZeroCopy) (p r a b X k : ℝ) : ℂ :=
  (Real.exp k:ℂ)^2*kernelJet q 2 2 p r a b X k+
    kernelJet q 3 2 p r a b X k-kernelJet q 3 1 p r a b X k

private def responseAction (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) : ℂ :=
  (Real.exp k:ℂ)^2*responseJet q s amplitude 2 2 p r X k+
    responseJet q s amplitude 3 2 p r X k-responseJet q s amplitude 3 1 p r X k

private theorem responseAction_derivatives (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) :
    (Real.exp k:ℂ)^2*deriv (deriv (fun x => fullNullResponse q s amplitude p r x k)) X+
      deriv (deriv (fun x => fullNullResponse q s amplitude p r X x)) k-
      deriv (fun x => fullNullResponse q s amplitude p r X x) k = responseAction q s amplitude p r X k := by
  have hx : deriv (fun x => fullNullResponse q s amplitude p r x k) =
      fun x => responseJet q s amplitude 2 1 p r x k :=
    funext (fun x => (responseJet_x q s amplitude 0 p r x k).deriv)
  have hk : deriv (fun x => fullNullResponse q s amplitude p r X x) =
      fun x => responseJet q s amplitude 3 1 p r X x := by
    have he := funext (fun x => responseJet_zero q s amplitude 3 p r X x)
    rw [← he]
    exact funext (fun x => (responseJet_k q s amplitude 0 p r X x).deriv)
  rw [hx,hk,(responseJet_x q s amplitude 1 p r X k).deriv,
    (responseJet_k q s amplitude 1 p r X k).deriv]
  rfl



@[fun_prop] private theorem kernelAction_comp {P : Type*} [TopologicalSpace P]
    (q : XiZeroCopy) (p r a b X k : P → ℝ)
    (hp : Continuous p) (hr : Continuous r) (ha : Continuous a) (hb : Continuous b)
    (hX : Continuous X) (hk : Continuous k) :
    Continuous (fun z => kernelAction q (p z) (r z) (a z) (b z) (X z) (k z)) := by
  unfold kernelAction
  fun_prop

@[fun_prop] private theorem responseAction_continuous (q : XiZeroCopy) (s amplitude : ℂ) (X k : ℝ) :
    Continuous (fun z : ℝ × ℝ => responseAction q s amplitude z.1 z.2 X k) := by
  have hc (i : Fin 4) (n : ℕ) := (responseJet_continuous q s amplitude i n).comp
    (show Continuous (fun z : ℝ × ℝ => (z,(X,k))) by fun_prop)
  exact ((continuous_const.mul (hc 2 2)).add (hc 3 2)).sub (hc 3 1)

private theorem responseAction_integral (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) :
    responseAction q s amplitude p r X k =
      (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        kernelAction q p r a b X k*nullSource s amplitude a b := by
  let f (i : Fin 4) (n : ℕ) (a b : ℝ) :=
    kernelJet q i n p r a b X k*nullSource s amplitude a b
  have hc (i : Fin 4) (n : ℕ) : Continuous (Function.uncurry (f i n)) := by
    dsimp only [Function.uncurry,f]; fun_prop
  have hi (a : ℝ) : (∫ b in (0:ℝ)..r, kernelAction q p r a b X k*nullSource s amplitude a b) =
      (Real.exp k:ℂ)^2*(∫ b in (0:ℝ)..r, f 2 2 a b)+
        (∫ b in (0:ℝ)..r, f 3 2 a b)-(∫ b in (0:ℝ)..r, f 3 1 a b) := by
    simp only [kernelAction,sub_mul,add_mul,mul_assoc]
    change (∫ b in (0:ℝ)..r, (Real.exp k:ℂ)^2*f 2 2 a b+f 3 2 a b-f 3 1 a b) = _
    rw [intervalIntegral.integral_sub,intervalIntegral.integral_add,intervalIntegral.integral_const_mul]
    · exact (((hc 2 2).uncurry_left a).const_mul _).intervalIntegrable 0 r
    · exact ((hc 3 2).uncurry_left a).intervalIntegrable 0 r
    · exact ((((hc 2 2).uncurry_left a).const_mul _).add ((hc 3 2).uncurry_left a)).intervalIntegrable 0 r
    · exact ((hc 3 1).uncurry_left a).intervalIntegrable 0 r
  simp_rw [hi]
  have hI (i : Fin 4) (n : ℕ) : Continuous (fun a => ∫ b in (0:ℝ)..r, f i n a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hc i n) 0 r
  rw [intervalIntegral.integral_sub,intervalIntegral.integral_add,intervalIntegral.integral_const_mul]
  · dsimp only [responseAction,responseJet,f]
    ring
  · exact ((hI 2 2).const_mul _).intervalIntegrable 0 p
  · exact (hI 3 2).intervalIntegrable 0 p
  · exact (((hI 2 2).const_mul _).add (hI 3 2)).intervalIntegrable 0 p
  · exact (hI 3 1).intervalIntegrable 0 p

private theorem circleJet_action (q : XiZeroCopy) (d X k : ℝ) :
    (Real.exp k:ℂ)^2*circleJet q 2 2 d X k+circleJet q 3 2 d X k-circleJet q 3 1 d X k =
      (Real.exp k:ℂ)^2*deriv (deriv (fun x => mean q d x k)) X+
        deriv (deriv (fun x => mean q d X x)) k-deriv (fun x => mean q d X x) k := by
  have hx : deriv (fun x => mean q d x k) = fun x => circleJet q 2 1 d x k := by
    rw [← funext (fun x => circleJet_zero q 2 d x k)]
    exact funext (fun x => (circleJet_x q 0 d x k).deriv)
  have hk : deriv (fun x => mean q d X x) = fun x => circleJet q 3 1 d X x := by
    rw [← funext (fun x => circleJet_zero q 3 d X x)]
    exact funext (fun x => (circleJet_k q 0 d X x).deriv)
  rw [hx,hk,(circleJet_x q 1 d X k).deriv,(circleJet_k q 1 d X k).deriv]

private theorem kernelAction_eq (q : XiZeroCopy) {p r a b : ℝ}
    (ha : a ≤ p) (hb : b ≤ r) (X k : ℝ) :
    kernelAction q p r a b X k =
      angularAction q (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)) X k := by
  unfold kernelAction kernelJet
  rw [circleJet_action,nullRadius_eq ha hb]
  rfl

private def nullWeight (p r : ℝ) : ℂ := 1/(4*(Real.cosh ((p-r)/2):ℂ)^2)

@[fun_prop] private theorem nullWeight_comp {P : Type*} [TopologicalSpace P]
    (p r : P → ℝ) (hp : Continuous p) (hr : Continuous r) :
    Continuous (fun z => nullWeight (p z) (r z)) := by
  unfold nullWeight
  apply Continuous.div continuous_const
  · fun_prop
  · intro z
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (by exact_mod_cast (Real.cosh_pos _).ne'))

private theorem fullKernel_goursat (q : XiZeroCopy) {p r a b : ℝ}
    (ha : a ≤ p) (hb : b ≤ r) (X k : ℝ) :
    kernelJet q 2 0 p r a b X k = fullSquarePotential q ![X,Real.exp k]+
      ∫ c in a..p, ∫ d in b..r, nullWeight c d*kernelAction q c d a b X k := by
  have hg := nativeRiemannKernel_goursat q ⟨_,_,_,null_cone ha hb⟩ X k
  dsimp only at hg
  rw [kernelJet_zero_eq q 2 ha hb]
  rw [show (p+r-a-b)/2+(p-r)/2-(a-b)/2 = p-a by ring,
    show (p+r-a-b)/2-(p-r)/2+(a-b)/2 = r-b by ring] at hg
  rw [hg]
  congr 1
  let f (c d : ℝ) := nullWeight c d*kernelAction q c d a b X k
  have hs (c : ℝ) : (∫ v in (0:ℝ)..(r-b), f c (v+b)) = ∫ d in b..r, f c d := by
    simpa only [zero_add,sub_add_cancel] using
      intervalIntegral.integral_comp_add_right (f := f c) (a := (0:ℝ)) (b := r-b) b
  have ht : (∫ u in (0:ℝ)..(p-a), ∫ v in (0:ℝ)..(r-b), f (u+a) (v+b)) =
      ∫ c in a..p, ∫ d in b..r, f c d := by
    simp_rw [hs]
    simpa only [zero_add,sub_add_cancel] using intervalIntegral.integral_comp_add_right
      (f := fun c => ∫ d in b..r, f c d) (a := (0:ℝ)) (b := p-a) a
  rw [← ht]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu0 : 0 ≤ u := (show u ∈ Icc 0 (p-a) by simpa [uIcc_of_le (sub_nonneg.mpr ha)] using hu).1
  apply intervalIntegral.integral_congr
  intro v hv
  have hv0 : 0 ≤ v := (show v ∈ Icc 0 (r-b) by simpa [uIcc_of_le (sub_nonneg.mpr hb)] using hv).1
  dsimp only [f,nullWeight]
  rw [kernelAction_eq q (by linarith : a ≤ u+a) (by linarith : b ≤ v+b)]
  rw [show (u+a+(v+b)-a-b)/2 = (u+v)/2 by ring,
    show (u+a-(v+b))/2 = (a-b)/2+(u-v)/2 by ring]
  ring


private theorem rectangle_swap (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y := by
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  exact (hf.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

private theorem triangle_swap (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in l..r, ∫ y in x..r, f x y) = ∫ y in l..r, ∫ x in l..y, f x y := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  let g (x y : ℝ) := if x ≤ y then f x y else 0
  have hi : Integrable (Function.uncurry f) (μ.prod μ) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hg : Integrable (Function.uncurry g) (μ.prod μ) := by
    convert! hi.indicator (measurableSet_le measurable_fst measurable_snd) using 1
  have hswap := integral_integral_swap hg
  have hleft : (∫ x in l..r, ∫ y in x..r, f x y) = ∫ x, ∫ y, g x y ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hlr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    have hset : Ioc l r ∩ Ici x = Icc x r := by
      ext y
      simp only [mem_inter_iff,mem_Ioc,mem_Ici,mem_Icc]
      constructor
      · rintro ⟨hxy,hy⟩; exact ⟨hy,hxy.2⟩
      · rintro ⟨hxy,hy⟩; exact ⟨⟨hx.1.trans_le hxy,hy⟩,hxy⟩
    have he : g x = (Ici x).indicator (f x) := by
      ext y; simp only [g,Set.indicator_apply,mem_Ici]
    change _ = ∫ y in Ioc l r, g x y
    rw [he,setIntegral_indicator measurableSet_Ici,hset,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx.2]
  have hright : (∫ y in l..r, ∫ x in l..y, f x y) = ∫ y, ∫ x, g x y ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hlr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    dsimp only
    have hset : Ioc l r ∩ Iic y = Ioc l y := by
      ext x
      simp only [mem_inter_iff,mem_Ioc,mem_Iic]
      constructor
      · rintro ⟨hxy,hx⟩; exact ⟨hxy.1,hx⟩
      · rintro ⟨hx,hxy⟩; exact ⟨⟨hx,hxy.trans hy.2⟩,hxy⟩
    have he : (fun x => g x y) = (Iic y).indicator (fun x => f x y) := by
      ext x; simp only [g,Set.indicator_apply,mem_Iic]
    change _ = ∫ x in Ioc l r, g x y
    rw [he,setIntegral_indicator measurableSet_Iic,hset,intervalIntegral.integral_of_le hy.1.le]
  rw [hleft,hright]
  exact hswap


private theorem corner_swap (f : (ℝ × ℝ) × (ℝ × ℝ) → ℂ) (hf : Continuous f)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q,
      ∫ c in a..p, ∫ d in b..q, f ((a,b),(c,d))) =
      ∫ c in (0:ℝ)..p, ∫ d in (0:ℝ)..q,
        ∫ a in (0:ℝ)..c, ∫ b in (0:ℝ)..d, f ((a,b),(c,d)) := by
  calc
    _ = ∫ a in (0:ℝ)..p, ∫ c in a..p,
        ∫ b in (0:ℝ)..q, ∫ d in b..q, f ((a,b),(c,d)) := by
      apply intervalIntegral.integral_congr
      intro a ha
      exact rectangle_swap (fun b c => ∫ d in b..q, f ((a,b),(c,d))) (by fun_prop) 0 q a p
    _ = ∫ c in (0:ℝ)..p, ∫ a in (0:ℝ)..c,
        ∫ b in (0:ℝ)..q, ∫ d in b..q, f ((a,b),(c,d)) :=
      triangle_swap (fun a c => ∫ b in (0:ℝ)..q, ∫ d in b..q, f ((a,b),(c,d)))
        (by fun_prop) hp
    _ = ∫ c in (0:ℝ)..p, ∫ a in (0:ℝ)..c,
        ∫ d in (0:ℝ)..q, ∫ b in (0:ℝ)..d, f ((a,b),(c,d)) := by
      apply intervalIntegral.integral_congr
      intro c hc
      apply intervalIntegral.integral_congr
      intro a ha
      exact triangle_swap (fun b d => f ((a,b),(c,d))) (by fun_prop) hq
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro c hc
      exact rectangle_swap (fun a d => ∫ b in (0:ℝ)..d, f ((a,b),(c,d)))
        (by fun_prop) 0 c 0 q



private theorem fullResponse_goursat (q : XiZeroCopy) (s amplitude : ℂ) {p r : ℝ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) (X k : ℝ) :
    fullNullResponse q s amplitude p r X k =
      (1/4:ℂ)*(∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b)+
      ∫ c in (0:ℝ)..p, ∫ d in (0:ℝ)..r,
        nullWeight c d*responseAction q s amplitude c d X k := by
  let g (z : (ℝ × ℝ) × (ℝ × ℝ)) :=
    nullWeight z.2.1 z.2.2*kernelAction q z.2.1 z.2.2 z.1.1 z.1.2 X k*
      nullSource s amplitude z.1.1 z.1.2
  have hg : Continuous g := by dsimp only [g]; fun_prop
  have hF : Continuous (Function.uncurry (fun a b =>
      fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b)) := by fun_prop
  have he : (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
      kernelJet q 2 0 p r a b X k*nullSource s amplitude a b) =
      (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b)+
      ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, ∫ c in a..p, ∫ d in b..r, g ((a,b),(c,d)) := by
    have hpoint {a b : ℝ} (ha : a ≤ p) (hb : b ≤ r) :
        kernelJet q 2 0 p r a b X k*nullSource s amplitude a b =
          fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b+
          (∫ c in a..p, ∫ d in b..r, g ((a,b),(c,d))) := by
      rw [fullKernel_goursat q ha hb]
      dsimp only [g]
      simp_rw [intervalIntegral.integral_mul_const]
      ring
    have hL : (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        kernelJet q 2 0 p r a b X k*nullSource s amplitude a b) =
        ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
          fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b+
            (∫ c in a..p, ∫ d in b..r, g ((a,b),(c,d))) := by
      apply intervalIntegral.integral_congr
      intro a ha
      have ha' : a ≤ p := (show a ∈ Icc 0 p by simpa [uIcc_of_le hp] using ha).2
      apply intervalIntegral.integral_congr
      intro b hb
      have hb' : b ≤ r := (show b ∈ Icc 0 r by simpa [uIcc_of_le hr] using hb).2
      exact hpoint ha' hb'
    rw [hL]
    have hC : Continuous (fun z : ℝ × ℝ => ∫ c in z.1..p, ∫ d in z.2..r,
        g (z,(c,d))) := by fun_prop
    have hinner (a : ℝ) : (∫ b in (0:ℝ)..r,
        fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b+
          (∫ c in a..p, ∫ d in b..r, g ((a,b),(c,d)))) =
        (∫ b in (0:ℝ)..r, fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b)+
        ∫ b in (0:ℝ)..r, ∫ c in a..p, ∫ d in b..r, g ((a,b),(c,d)) :=
      intervalIntegral.integral_add
        ((hF.uncurry_left a).intervalIntegrable 0 r)
        ((Continuous.uncurry_left
          (f := fun a b => ∫ c in a..p, ∫ d in b..r, g ((a,b),(c,d))) a hC).intervalIntegrable 0 r)
    simp_rw [hinner]
    apply intervalIntegral.integral_add
    · exact (show Continuous (fun a => ∫ b in (0:ℝ)..r,
        fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b) by fun_prop).intervalIntegrable 0 p
    · exact (show Continuous (fun a => ∫ b in (0:ℝ)..r, ∫ c in a..p,
        ∫ d in b..r, g ((a,b),(c,d))) by fun_prop).intervalIntegrable 0 p
  have hs := corner_swap g hg hp hr
  unfold fullNullResponse responseJet
  rw [he,hs,mul_add]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro c hc
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro d hd
  dsimp only [g]
  rw [responseAction_integral]
  simp_rw [mul_assoc,intervalIntegral.integral_const_mul]
  ring

private def fullEffective (q : XiZeroCopy) (s amplitude : ℂ) (X k : ℝ) (p r : ℝ) : ℂ :=
  (1/4:ℂ)*(fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude p r)+
    nullWeight p r*responseAction q s amplitude p r X k

@[fun_prop] private theorem fullEffective_continuous (q : XiZeroCopy) (s amplitude : ℂ) (X k : ℝ) :
    Continuous (fun z : ℝ × ℝ => fullEffective q s amplitude X k z.1 z.2) := by
  unfold fullEffective
  exact (continuous_const.mul (continuous_const.mul (nullSource_continuous s amplitude))).add
    ((nullWeight_comp _ _ continuous_fst continuous_snd).mul (responseAction_continuous q s amplitude X k))

private theorem fullResponse_primitive (q : XiZeroCopy) (s amplitude : ℂ) {p r : ℝ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) (X k : ℝ) :
    fullNullResponse q s amplitude p r X k =
      ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, fullEffective q s amplitude X k a b := by
  rw [fullResponse_goursat q s amplitude hp hr]
  have hF : Continuous (Function.uncurry (fun a b =>
      fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b)) := by fun_prop
  have hV : Continuous (Function.uncurry (fun a b =>
      nullWeight a b*responseAction q s amplitude a b X k)) := by fun_prop
  have hi (a : ℝ) : (∫ b in (0:ℝ)..r, fullEffective q s amplitude X k a b) =
      (1/4:ℂ)*(∫ b in (0:ℝ)..r, fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b)+
        ∫ b in (0:ℝ)..r, nullWeight a b*responseAction q s amplitude a b X k := by
    dsimp only [fullEffective]
    rw [intervalIntegral.integral_add,intervalIntegral.integral_const_mul]
    · exact ((hF.uncurry_left a).const_mul _).intervalIntegrable 0 r
    · exact (hV.uncurry_left a).intervalIntegrable 0 r
  simp_rw [hi]
  rw [intervalIntegral.integral_add,intervalIntegral.integral_const_mul]
  · exact (show Continuous (fun a => (1/4:ℂ)*∫ b in (0:ℝ)..r,
      fullSquarePotential q ![X,Real.exp k]*nullSource s amplitude a b) by fun_prop).intervalIntegrable 0 p
  · exact (integral_continuous (fun a b => nullWeight a b*responseAction q s amplitude a b X k)
      hV (fun _ => 0) (fun _ => r) continuous_const continuous_const).intervalIntegrable 0 p

private theorem fullResponse_first (q : XiZeroCopy) (s amplitude : ℂ) {p r : ℝ}
    (hp : 0 < p) (hr : 0 ≤ r) (X k : ℝ) :
    HasDerivAt (fun a => fullNullResponse q s amplitude a r X k)
      (∫ b in (0:ℝ)..r, fullEffective q s amplitude X k p b) p := by
  have hi : Continuous (fun a => ∫ b in (0:ℝ)..r, fullEffective q s amplitude X k a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (fullEffective_continuous q s amplitude X k) 0 r
  have hd := intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 p)
    (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hp] with a ha
  exact fullResponse_primitive q s amplitude ha.le hr X k

/-- The original full-source causal integral obeys its forced wave equation, with
actual angular derivatives and the original source impulse. -/
theorem fullNullResponse_wave (q : XiZeroCopy) (s amplitude : ℂ) {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (X k : ℝ) :
    deriv (fun b => deriv (fun a => fullNullResponse q s amplitude a b X k) p) r =
      (1/4:ℂ)*(fullSquarePotential q ![X,Real.exp k]*
        oddSource s amplitude ((p+r)/2) ((p-r)/2))+
      ((Real.exp k:ℂ)^2*deriv (deriv (fun x => fullNullResponse q s amplitude p r x k)) X+
        deriv (deriv (fun x => fullNullResponse q s amplitude p r X x)) k-
        deriv (fun x => fullNullResponse q s amplitude p r X x) k)/
          (4*(Real.cosh ((p-r)/2):ℂ)^2) := by
  have hi := Continuous.uncurry_left (f := fullEffective q s amplitude X k) p
    (fullEffective_continuous q s amplitude X k)
  have hd := intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 r)
    (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
  have he : (fun b => deriv (fun a => fullNullResponse q s amplitude a b X k) p) =ᶠ[𝓝 r]
      (fun b => ∫ d in (0:ℝ)..b, fullEffective q s amplitude X k p d) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with b hb
    exact (fullResponse_first q s amplitude hp hb.le X k).deriv
  have h := (hd.congr_of_eventuallyEq he).deriv
  rw [responseAction_derivatives]
  rw [h]
  dsimp only [fullEffective,nullSource,nullWeight]
  ring



/-- The full causal response is a double primitive of its original source and actual
angular Laplacian, including both zero-length characteristic edges. -/
theorem fullNullResponse_goursat (q : XiZeroCopy) (s amplitude : ℂ) {p r : ℝ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) (X k : ℝ) :
    fullNullResponse q s amplitude p r X k =
      (1/4:ℂ)*(∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        fullSquarePotential q ![X,Real.exp k]*oddSource s amplitude ((a+b)/2) ((a-b)/2))+
      ∫ c in (0:ℝ)..p, ∫ d in (0:ℝ)..r,
        ((Real.exp k:ℂ)^2*deriv (deriv (fun x => fullNullResponse q s amplitude c d x k)) X+
          deriv (deriv (fun x => fullNullResponse q s amplitude c d X x)) k-
          deriv (fun x => fullNullResponse q s amplitude c d X x) k)/
            (4*(Real.cosh ((c-d)/2):ℂ)^2) := by
  rw [fullResponse_goursat q s amplitude hp hr]
  congr 1
  apply intervalIntegral.integral_congr
  intro c hc
  apply intervalIntegral.integral_congr
  intro d hd
  dsimp only
  rw [responseAction_derivatives]
  dsimp only [nullWeight]
  ring

private theorem nullSource_swap (s amplitude : ℂ) (a b : ℝ) :
    nullSource s amplitude b a = -nullSource s amplitude a b := by
  rw [nullSource,nullSource,show (b+a)/2 = (a+b)/2 by ring,
    show (b-a)/2 = -((a-b)/2) by ring]
  simp only [oddSource,neg_neg,neg_sub]

private theorem kernel_diagonal_swap (q : XiZeroCopy) (p a b X k : ℝ) :
    kernelJet q 2 0 p p b a X k = kernelJet q 2 0 p p a b X k := by
  unfold kernelJet nullRadius
  rw [show (p+p-b-a)/2 = (p+p-a-b)/2 by ring,
    show (b-a)/2 = -((a-b)/2) by ring]
  simp only [sub_self,zero_div,invariant,Real.sinh_zero,zero_mul,add_zero,Real.cosh_neg]

/-- The full source integral satisfies the original radial Dirichlet condition by
exact kernel reflection and odd-source cancellation. -/
theorem fullNullResponse_boundary (q : XiZeroCopy) (s amplitude : ℂ) (p X k : ℝ) :
    fullNullResponse q s amplitude p p X k = 0 := by
  let f (a b : ℝ) := kernelJet q 2 0 p p a b X k*nullSource s amplitude a b
  have hf : Continuous (Function.uncurry f) := by dsimp only [Function.uncurry,f]; fun_prop
  have he (a b : ℝ) : f b a = -f a b := by
    dsimp only [f]
    rw [kernel_diagonal_swap,nullSource_swap,mul_neg]
  have hs := rectangle_swap f hf 0 p 0 p
  have hneg : (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..p, f b a) =
      -(∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..p, f a b) := by
    calc
      _ = ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..p, -f a b := by
        apply intervalIntegral.integral_congr
        intro a ha
        apply intervalIntegral.integral_congr
        intro b hb
        exact he a b
      _ = _ := by simp only [intervalIntegral.integral_neg]
  have hz : (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..p, f a b) = 0 := by
    rw [hneg] at hs
    linear_combination hs/2
  change (1/4:ℂ)*(∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..p, f a b) = 0
  rw [hz,mul_zero]



private def cutoffLogPower (alpha : ℂ) (k : ℝ) : ℂ :=
  powerCutoffHeight alpha (Real.exp k)

private def cutoffLogJet (alpha : ℂ) (k : ℝ) : ℂ :=
  (Real.exp k:ℂ)*deriv (powerCutoffHeight alpha) (Real.exp k)

private theorem cutoffLogPower_first (alpha : ℂ) (k : ℝ) :
    HasDerivAt (cutoffLogPower alpha) (cutoffLogJet alpha k) k := by
  have hd := (((powerCutoffHeight_smooth alpha).differentiable (by simp))
    (Real.exp k)).hasDerivAt.scomp k (Real.hasDerivAt_exp k)
  convert! hd using 1

private theorem cutoffLogJet_first (alpha : ℂ) (k : ℝ) :
    HasDerivAt (cutoffLogJet alpha)
      (cutoffLogJet alpha k+(Real.exp k:ℂ)^2*
        deriv (deriv (powerCutoffHeight alpha)) (Real.exp k)) k := by
  have hs := (contDiff_infty_iff_deriv.mp (powerCutoffHeight_smooth alpha)).2
  have hd := ((hs.differentiable (by simp)) (Real.exp k)).hasDerivAt.scomp k
    (Real.hasDerivAt_exp k)
  have hp := (Real.hasDerivAt_exp k).ofReal_comp.mul hd
  convert! hp using 1
  simp only [cutoffLogJet,Complex.real_smul,Function.comp_apply]
  ring

/-- The original principal coefficient, with its full Weyl amplitude, in null coordinates. -/
def principalNullResponse (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 3) (p r : ℝ) : ℂ :=
  principalAmplitude q i*radialResponse (-principalExponent q i) s amplitude
    ((p+r)/2) ((p-r)/2)

/-- Literal full theta response after subtraction of its three transported cutoff powers. -/
def fullNullResidual (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) : ℂ :=
  fullNullResponse q s amplitude p r X k-
    ∑ i : Fin 3, principalNullResponse q s amplitude i p r*
      cutoffPower (principalExponent q i) ![X,Real.exp k]

private def residualHeightJet (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) : ℂ :=
  responseJet q s amplitude 3 1 p r X k-
    ∑ i : Fin 3, principalNullResponse q s amplitude i p r*cutoffLogJet (principalExponent q i) k

private theorem fullNullResidual_x (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) :
    HasDerivAt (fun x => fullNullResidual q s amplitude p r x k)
      (responseJet q s amplitude 2 1 p r X k) X := by
  have h := (responseJet_x q s amplitude 0 p r X k).sub_const
    (∑ i : Fin 3, principalNullResponse q s amplitude i p r*cutoffLogPower (principalExponent q i) k)
  convert! h using 1

private theorem fullNullResidual_k (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) :
    HasDerivAt (fun x => fullNullResidual q s amplitude p r X x)
      (residualHeightJet q s amplitude p r X k) k := by
  have h := (responseJet_k q s amplitude 0 p r X k).sub
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (cutoffLogPower_first (principalExponent q i) k).const_mul
        (principalNullResponse q s amplitude i p r)))
  convert! h using 1

private theorem residualHeightJet_first (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) :
    HasDerivAt (fun x => residualHeightJet q s amplitude p r X x)
      (responseJet q s amplitude 3 2 p r X k-
        ∑ i : Fin 3, principalNullResponse q s amplitude i p r*
          (cutoffLogJet (principalExponent q i) k+(Real.exp k:ℂ)^2*
            deriv (deriv (powerCutoffHeight (principalExponent q i))) (Real.exp k))) k := by
  exact (responseJet_k q s amplitude 1 p r X k).sub
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (cutoffLogJet_first (principalExponent q i) k).const_mul
        (principalNullResponse q s amplitude i p r)))

private def residualAction (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) : ℂ :=
  responseAction q s amplitude p r X k-
    ∑ i : Fin 3, principalNullResponse q s amplitude i p r*
      ((Real.exp k:ℂ)^2*deriv (deriv (powerCutoffHeight (principalExponent q i))) (Real.exp k))

private theorem residualAction_derivatives (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) :
    (Real.exp k:ℂ)^2*deriv (deriv (fun x => fullNullResidual q s amplitude p r x k)) X+
      deriv (deriv (fun x => fullNullResidual q s amplitude p r X x)) k-
      deriv (fun x => fullNullResidual q s amplitude p r X x) k = residualAction q s amplitude p r X k := by
  have hx : deriv (fun x => fullNullResidual q s amplitude p r x k) =
      fun x => responseJet q s amplitude 2 1 p r x k :=
    funext (fun x => (fullNullResidual_x q s amplitude p r x k).deriv)
  have hk : deriv (fun x => fullNullResidual q s amplitude p r X x) =
      fun x => residualHeightJet q s amplitude p r X x :=
    funext (fun x => (fullNullResidual_k q s amplitude p r X x).deriv)
  rw [hx,hk,(responseJet_x q s amplitude 1 p r X k).deriv,
    (residualHeightJet_first q s amplitude p r X k).deriv]
  simp only [residualHeightJet,residualAction,responseAction,mul_add,Finset.sum_add_distrib]
  ring

@[fun_prop] private theorem principalNullResponse_continuous (q : XiZeroCopy)
    (s amplitude : ℂ) (i : Fin 3) :
    Continuous (fun z : ℝ × ℝ => principalNullResponse q s amplitude i z.1 z.2) := by
  have hc := (radialResponse_continuous (-principalExponent q i) s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  convert! hc.const_mul (principalAmplitude q i) using 1

private def nullRectangle (f : ℝ → ℝ → ℂ) (p r : ℝ) : ℂ :=
  ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, f a b

private theorem nullRectangle_add (f g : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    nullRectangle (fun a b => f a b+g a b) p r = nullRectangle f p r+nullRectangle g p r := by
  unfold nullRectangle
  simp_rw [intervalIntegral.integral_add ((hf.uncurry_left _).intervalIntegrable 0 r)
    ((hg.uncurry_left _).intervalIntegrable 0 r)]
  exact intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 r).intervalIntegrable 0 p)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg 0 r).intervalIntegrable 0 p)

private theorem nullRectangle_sub (f g : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    nullRectangle (fun a b => f a b-g a b) p r = nullRectangle f p r-nullRectangle g p r := by
  unfold nullRectangle
  simp_rw [intervalIntegral.integral_sub ((hf.uncurry_left _).intervalIntegrable 0 r)
    ((hg.uncurry_left _).intervalIntegrable 0 r)]
  exact intervalIntegral.integral_sub
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 r).intervalIntegrable 0 p)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg 0 r).intervalIntegrable 0 p)

private theorem nullRectangle_const_mul (c : ℂ) (f : ℝ → ℝ → ℂ) (p r : ℝ) :
    nullRectangle (fun a b => c*f a b) p r = c*nullRectangle f p r := by
  simp only [nullRectangle,intervalIntegral.integral_const_mul]

private theorem nullRectangle_mul_const (c : ℂ) (f : ℝ → ℝ → ℂ) (p r : ℝ) :
    nullRectangle (fun a b => f a b*c) p r = nullRectangle f p r*c := by
  simp only [nullRectangle,intervalIntegral.integral_mul_const]

private theorem nullRectangle_sum (f : Fin 3 → ℝ → ℝ → ℂ)
    (hf : ∀ i, Continuous (Function.uncurry (f i))) (p r : ℝ) :
    nullRectangle (fun a b => ∑ i, f i a b) p r = ∑ i, nullRectangle (f i) p r := by
  unfold nullRectangle
  simp_rw [intervalIntegral.integral_finsetSum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => ((hf i).uncurry_left _).intervalIntegrable 0 r)]
  exact intervalIntegral.integral_finsetSum (fun i _ =>
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hf i) 0 r).intervalIntegrable 0 p)

private def principalEffective (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 3) (p r : ℝ) : ℂ :=
  principalAmplitude q i*nullSource s amplitude p r/4+
    nullWeight p r*(principalExponent q i*(principalExponent q i-1)*
      principalNullResponse q s amplitude i p r)

@[fun_prop] private theorem principalEffective_continuous (q : XiZeroCopy)
    (s amplitude : ℂ) (i : Fin 3) :
    Continuous (fun z : ℝ × ℝ => principalEffective q s amplitude i z.1 z.2) := by
  unfold principalEffective
  exact ((continuous_const.mul (nullSource_continuous s amplitude)).div_const 4).add
    ((nullWeight_comp _ _ continuous_fst continuous_snd).mul
      (continuous_const.mul (principalNullResponse_continuous q s amplitude i)))

private theorem principalNullResponse_primitive (q : XiZeroCopy) (s amplitude : ℂ)
    (i : Fin 3) {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) :
    principalNullResponse q s amplitude i p r =
      nullRectangle (principalEffective q s amplitude i) p r := by
  let alpha := principalExponent q i
  let f := nullSource s amplitude
  let v := fun a b => (-alpha)*(-alpha+1)/(4*(Real.cosh ((a-b)/2):ℂ)^2)*
    radialResponse (-alpha) s amplitude ((a+b)/2) ((a-b)/2)
  have hv : Continuous (Function.uncurry v) := by
    have hu := (radialResponse_continuous (-alpha) s amplitude).comp
      (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
    have hn := nullWeight_comp (fun z : ℝ × ℝ => z.1) (fun z => z.2) continuous_fst continuous_snd
    convert! (hn.const_mul ((-alpha)*(-alpha+1))).mul hu using 1
    funext z
    dsimp only [Function.uncurry,v,nullWeight,Function.comp_apply,Pi.mul_apply]
    ring
  have he : principalEffective q s amplitude i =
      fun a b => principalAmplitude q i*((1/4:ℂ)*f a b+v a b) := by
    funext a b
    dsimp only [principalEffective,principalNullResponse,nullWeight,v,f,alpha]
    ring
  rw [he,nullRectangle_const_mul,nullRectangle_add (fun a b => (1/4:ℂ)*f a b) v
    ((nullSource_continuous s amplitude).const_mul (1/4:ℂ)) hv,
    nullRectangle_const_mul]
  exact congrArg (fun z => principalAmplitude q i*z)
    (radialResponse_goursat (-alpha) s amplitude hp hr)

private theorem fullNullResponse_rectangle (q : XiZeroCopy) (s amplitude : ℂ)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (X k : ℝ) :
    fullNullResponse q s amplitude p r X k =
      nullRectangle (fullEffective q s amplitude X k) p r := by
  exact fullResponse_primitive q s amplitude hp hr X k

private def residualEffective (q : XiZeroCopy) (s amplitude : ℂ) (X k : ℝ) (p r : ℝ) : ℂ :=
  fullEffective q s amplitude X k p r-
    ∑ i : Fin 3, principalEffective q s amplitude i p r*cutoffLogPower (principalExponent q i) k

@[fun_prop] private theorem residualEffective_continuous (q : XiZeroCopy)
    (s amplitude : ℂ) (X k : ℝ) :
    Continuous (fun z : ℝ × ℝ => residualEffective q s amplitude X k z.1 z.2) := by
  exact (fullEffective_continuous q s amplitude X k).sub
    (continuous_finsetSum _ (fun i _ =>
      (principalEffective_continuous q s amplitude i).mul continuous_const))

private theorem fullNullResidual_primitive (q : XiZeroCopy) (s amplitude : ℂ)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (X k : ℝ) :
    fullNullResidual q s amplitude p r X k =
      nullRectangle (residualEffective q s amplitude X k) p r := by
  unfold residualEffective
  rw [nullRectangle_sub (fullEffective q s amplitude X k)
    (fun a b => ∑ i : Fin 3, principalEffective q s amplitude i a b*cutoffLogPower (principalExponent q i) k)
    (fullEffective_continuous q s amplitude X k)
    (continuous_finsetSum _ (fun i _ =>
      (principalEffective_continuous q s amplitude i).mul continuous_const)),
    nullRectangle_sum (fun i a b => principalEffective q s amplitude i a b*cutoffLogPower (principalExponent q i) k)
      (fun i => (principalEffective_continuous q s amplitude i).mul continuous_const)]
  simp_rw [nullRectangle_mul_const,← principalNullResponse_primitive q s amplitude _ hp hr]
  rw [← fullNullResponse_rectangle q s amplitude hp hr]
  rfl

private theorem residualEffective_source (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) :
    residualEffective q s amplitude X k p r =
      (1/4:ℂ)*(squareResidual q ![X,Real.exp k]*nullSource s amplitude p r)+
        nullWeight p r*(residualAction q s amplitude p r X k+
          ∑ i : Fin 3, principalNullResponse q s amplitude i p r*
            cutoffCommutator (principalExponent q i) ![X,Real.exp k]) := by
  let C := fun i : Fin 3 => cutoffLogPower (principalExponent q i) k
  let P := fun i : Fin 3 => principalNullResponse q s amplitude i p r
  let A := fun i : Fin 3 => principalAmplitude q i
  let L := fun i : Fin 3 => principalExponent q i*(principalExponent q i-1)
  have hcomm (i : Fin 3) : P i*cutoffCommutator (principalExponent q i) ![X,Real.exp k] =
      P i*((Real.exp k:ℂ)^2*deriv (deriv (powerCutoffHeight (principalExponent q i))) (Real.exp k))-
        (L i*P i)*C i := by
    rw [cutoffCommutator_height]
    dsimp only [P,C,L,cutoffLogPower,Matrix.cons_val_one,Matrix.cons_val_zero]
    ring
  have haction : residualAction q s amplitude p r X k+
      ∑ i : Fin 3, P i*cutoffCommutator (principalExponent q i) ![X,Real.exp k] =
        responseAction q s amplitude p r X k-∑ i : Fin 3, (L i*P i)*C i := by
    simp_rw [hcomm]
    rw [Finset.sum_sub_distrib]
    dsimp only [residualAction,P]
    ring
  have hsum : (∑ i : Fin 3, A i*C i) =
      D4BMGlobalAngularResponse.cutoff ![X,Real.exp k]*principalSquare q ![X,Real.exp k] := by
    rw [principalSquare_expansion q _ (Real.exp_pos k),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [A,C,cutoffLogPower,powerCutoffHeight,cutoffPower,D4BMGlobalAngularResponse.cutoff,
      Matrix.cons_val_one,Matrix.cons_val_zero]
    ring
  have he (i : Fin 3) : principalEffective q s amplitude i p r*C i =
      (A i*C i)*nullSource s amplitude p r/4+nullWeight p r*((L i*P i)*C i) := by
    dsimp only [principalEffective,A,L,P]
    ring
  change fullEffective q s amplitude X k p r-∑ i : Fin 3,
    principalEffective q s amplitude i p r*C i = _
  change _ = (1/4:ℂ)*(squareResidual q ![X,Real.exp k]*nullSource s amplitude p r)+
    nullWeight p r*(residualAction q s amplitude p r X k+
      ∑ i : Fin 3, P i*cutoffCommutator (principalExponent q i) ![X,Real.exp k])
  rw [haction]
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul,← Finset.mul_sum,hsum]
  dsimp only [fullEffective,squareResidual]
  ring

private theorem fullNullResidual_first (q : XiZeroCopy) (s amplitude : ℂ) {p r : ℝ}
    (hp : 0 < p) (hr : 0 ≤ r) (X k : ℝ) :
    HasDerivAt (fun a => fullNullResidual q s amplitude a r X k)
      (∫ b in (0:ℝ)..r, residualEffective q s amplitude X k p b) p := by
  have hi : Continuous (fun a => ∫ b in (0:ℝ)..r, residualEffective q s amplitude X k a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (residualEffective_continuous q s amplitude X k) 0 r
  have hd := intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 p)
    (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hp] with a ha
  exact fullNullResidual_primitive q s amplitude ha.le hr X k

/-- Subtracting the actual three principal responses produces precisely the original
cutoff residual source and the three transported cutoff commutators. All derivatives
are derivatives of the literal full theta response. -/
theorem fullNullResidual_wave (q : XiZeroCopy) (s amplitude : ℂ) {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (X k : ℝ) :
    deriv (fun b => deriv (fun a => fullNullResidual q s amplitude a b X k) p) r =
      (1/4:ℂ)*(squareResidual q ![X,Real.exp k]*
        oddSource s amplitude ((p+r)/2) ((p-r)/2))+
      ((Real.exp k:ℂ)^2*deriv (deriv (fun x => fullNullResidual q s amplitude p r x k)) X+
        deriv (deriv (fun x => fullNullResidual q s amplitude p r X x)) k-
        deriv (fun x => fullNullResidual q s amplitude p r X x) k+
        ∑ i : Fin 3, principalNullResponse q s amplitude i p r*
          cutoffCommutator (principalExponent q i) ![X,Real.exp k])/
            (4*(Real.cosh ((p-r)/2):ℂ)^2) := by
  have hi := Continuous.uncurry_left (f := residualEffective q s amplitude X k) p
    (residualEffective_continuous q s amplitude X k)
  have hd := intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 r)
    (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
  have he : (fun b => deriv (fun a => fullNullResidual q s amplitude a b X k) p) =ᶠ[𝓝 r]
      (fun b => ∫ d in (0:ℝ)..b, residualEffective q s amplitude X k p d) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with b hb
    exact (fullNullResidual_first q s amplitude hp hb.le X k).deriv
  rw [(hd.congr_of_eventuallyEq he).deriv,residualEffective_source,residualAction_derivatives]
  dsimp only [nullSource,nullWeight]
  ring

/-- The cutoff residual retains the original AdS Dirichlet boundary. -/
theorem fullNullResidual_boundary (q : XiZeroCopy) (s amplitude : ℂ) (p X k : ℝ) :
    fullNullResidual q s amplitude p p X k = 0 := by
  simp only [fullNullResidual,fullNullResponse_boundary,principalNullResponse,sub_self,zero_div,
    radialResponse_boundary,mul_zero,zero_mul,Finset.sum_const_zero]

/-- At the physical rate, the coefficients in the residual equation are representatives
of the already constructed physical principal evolution, in its original L² measure. -/
theorem principalNullResponse_physical_ae (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (i : Fin 3) (tau : ℝ) :
    (principalTimeResponse q branch amplitude i tau : ℝ → ℂ) =ᵐ[volume]
      (fun x => principalNullResponse q (physicalRate q branch) amplitude i (tau+x) (tau-x)) := by
  rw [← nativePrincipalResponse_eq_principalTimeResponse]
  filter_upwards [Lp.coeFn_smul (principalAmplitude q i)
    (radialResponseVector (-principalExponent q i) (physicalRate q branch) amplitude tau),
    (radialResponse_memLp (-principalExponent q i) (physicalRate q branch) amplitude tau).coeFn_toLp]
    with x hs hx
  change (principalAmplitude q i • radialResponseVector _ _ _ tau) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,principalNullResponse,
    show (tau+x+(tau-x))/2=tau by ring,show (tau+x-(tau-x))/2=x by ring]
  exact congrArg (fun z => principalAmplitude q i*z) hx

/-- The residual equation also holds as a closed-rectangle integral identity, including
both characteristic edges, with the actual residual Laplacian and cutoff forcing. -/
theorem fullNullResidual_goursat (q : XiZeroCopy) (s amplitude : ℂ) {p r : ℝ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) (X k : ℝ) :
    fullNullResidual q s amplitude p r X k =
      ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        (1/4:ℂ)*(squareResidual q ![X,Real.exp k]*
          oddSource s amplitude ((a+b)/2) ((a-b)/2))+
        ((Real.exp k:ℂ)^2*deriv (deriv (fun x => fullNullResidual q s amplitude a b x k)) X+
          deriv (deriv (fun x => fullNullResidual q s amplitude a b X x)) k-
          deriv (fun x => fullNullResidual q s amplitude a b X x) k+
          ∑ i : Fin 3, principalNullResponse q s amplitude i a b*
            cutoffCommutator (principalExponent q i) ![X,Real.exp k])/
              (4*(Real.cosh ((a-b)/2):ℂ)^2) := by
  rw [fullNullResidual_primitive q s amplitude hp hr]
  apply intervalIntegral.integral_congr
  intro a ha
  apply intervalIntegral.integral_congr
  intro b hb
  dsimp only
  rw [residualEffective_source,residualAction_derivatives]
  dsimp only [nullSource,nullWeight]
  ring

end
end RHTower.D4BMNativeResponse
