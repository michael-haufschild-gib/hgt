import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleRiemannKernel
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeField
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The actual reduced source coefficient, its fixed onset contact, and a rational
optical primitive retaining the native spin-two circle field. -/
open Set MeasureTheory
namespace RHTower.D4BMReducedOpticalTail
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMNativeCircle D4BMHorizon D4BMModularCore
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual wave-image remainder has a scalar half-square coefficient and one
explicit derivative of the original ingoing onset. -/
theorem timeReducedCoefficient_closed (s a : ℂ) (tau x : ℝ) :
    timeReducedCoefficient s a tau x =
      let u : ℂ := radialUnit x
      sourceAmplitude s 0 a 1 x*Complex.exp (2*s*((tau+x:ℝ):ℂ))*
        (-u*(1-u^(2 : ℕ))*(2*s+1)*(2*s+2)*(Real.smoothTransition (tau+x):ℂ)+
          s*(s-1)/2*u^(2 : ℕ)*(1-u)*(3+(2*s+3)*u)*
            ((deriv Real.smoothTransition (tau+x):ℝ):ℂ)) := by
  dsimp [timeReducedCoefficient,reducedCoefficient,reducedPolynomial,
    radialLiftFirst,liftFirstPolynomial,liftSecondPolynomial,amplitudeRate,
    timeOnset,timeOnsetFirst]
  ring

private theorem clock_derivative (v : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-6*x)*Real.smoothTransition x)
      (Real.exp (-6*v)*deriv Real.smoothTransition v-
        6*(Real.exp (-6*v)*Real.smoothTransition v)) v := by
  have hchi : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition v) v :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt
  apply ((((hasDerivAt_id v).const_mul (-6)).exp).mul hchi).congr_deriv
  simp only [id_eq,mul_one]
  ring

/-- Exact finite-clock contact, including the terminal value of the fixed onset. -/
theorem finite_clock_contact (b : ℝ) :
    (∫ v in (0:ℝ)..b, Real.exp (-6*v)*deriv Real.smoothTransition v) =
      Real.exp (-6*b)*Real.smoothTransition b+
        6*(∫ v in (0:ℝ)..b, Real.exp (-6*v)*Real.smoothTransition v) := by
  have he : Continuous (fun v : ℝ => Real.exp (-6*v)) := by fun_prop
  have hc : Continuous Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 0)).continuous
  have hi : IntervalIntegrable (fun v : ℝ => Real.exp (-6*v)*Real.smoothTransition v) volume 0 b :=
    (he.mul hc).intervalIntegrable 0 b
  have hd : IntervalIntegrable (fun v : ℝ => Real.exp (-6*v)*deriv Real.smoothTransition v) volume 0 b :=
    (he.mul continuous_deriv_smoothTransition).intervalIntegrable 0 b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => clock_derivative v) (hd.sub (hi.const_mul 6))
  rw [intervalIntegral.integral_sub hd (hi.const_mul 6),
    intervalIntegral.integral_const_mul] at h
  simp only [Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ)),mul_zero,sub_zero] at h
  linarith only [h]

/-- The long-delay clock consists of its literal transition integral and exponential tail. -/
def tailClock : ℝ :=
  (∫ v in (0:ℝ)..1, Real.exp (-6*v)*Real.smoothTransition v)+Real.exp (-6)/6

/-- The rationally normalized clock is exactly the original full half-line integral. -/
theorem tailClock_integral :
    (∫ v in Ioi (0:ℝ), Real.exp (-6*v)*Real.smoothTransition v)=tailClock := by
  have hi (c : ℝ) : IntegrableOn
      (fun v : ℝ => Real.exp (-6*v)*Real.smoothTransition v) (Ioi c) := by
    apply (integrableOn_exp_mul_Ioi (by norm_num : (-6:ℝ)<0) c).mono' (by fun_prop)
    filter_upwards with v
    rw [Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (Real.smoothTransition.nonneg v))]
    calc
      _ ≤ Real.exp (-6*v)*1 :=
        mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one v) (Real.exp_pos _).le
      _ = _ := mul_one _
  have ht : (∫ v in Ioi (1:ℝ), Real.exp (-6*v)*Real.smoothTransition v)=Real.exp (-6)/6 := by
    calc
      _ = ∫ v in Ioi (1:ℝ), Real.exp (-6*v) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        dsimp only
        rw [Real.smoothTransition.one_of_one_le hv.le,mul_one]
      _ = _ := by
        rw [integral_exp_mul_Ioi (by norm_num : (-6:ℝ)<0) 1]
        ring_nf
  have h := intervalIntegral.integral_interval_add_Ioi (hi 0) (hi 1)
  rw [ht] at h
  exact h.symm

/-- The earlier source-onset derivative contributes six times the complete tail clock. -/
theorem tail_clock_contact :
    (∫ v in (0:ℝ)..1, Real.exp (-6*v)*deriv Real.smoothTransition v)=6*tailClock := by
  have h := finite_clock_contact 1
  rw [Real.smoothTransition.one_of_one_le (le_refl (1:ℝ)),mul_one,mul_one] at h
  dsimp [tailClock]
  linarith only [h]

private def rationalBasis (i : Fin 5) (x : ℝ) : ℝ :=
  ![(-1/6)*(x^(6 : ℕ))⁻¹,(-1/5)*(x^(5 : ℕ))⁻¹,(-1/4)*(x^(4 : ℕ))⁻¹,
    (-1/3)*(x^(3 : ℕ))⁻¹,(-1/2)*(x^(2 : ℕ))⁻¹] i

private theorem rationalBasis_derivative (i : Fin 5) (x : Ioi (0:ℝ)) :
    HasDerivAt (rationalBasis i) (x.val^i.val/x.val^(7 : ℕ)) x.val := by
  have hx : x.val ≠ 0 := ne_of_gt x.property
  fin_cases i
  · convert (((hasDerivAt_id x.val).pow 6).inv (pow_ne_zero 6 hx)).const_mul (-1/6) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · convert (((hasDerivAt_id x.val).pow 5).inv (pow_ne_zero 5 hx)).const_mul (-1/5) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · convert (((hasDerivAt_id x.val).pow 4).inv (pow_ne_zero 4 hx)).const_mul (-1/4) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · convert (((hasDerivAt_id x.val).pow 3).inv (pow_ne_zero 3 hx)).const_mul (-1/3) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · convert (((hasDerivAt_id x.val).pow 2).inv (pow_ne_zero 2 hx)).const_mul (-1/2) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)

private def row11 (L d : ℂ) : Fin 5 → ℂ := ![0,L*d,-(L+d),1,0]
private def row21 (L d : ℂ) : Fin 5 → ℂ := ![-L^(2 : ℕ)*d,L^(2 : ℕ)+2*L*d,-(2*L+d),1,0]
private def row31 (L d : ℂ) : Fin 5 → ℂ :=
  ![L^(3 : ℕ)*d,-(L^(3 : ℕ)+3*L^(2 : ℕ)*d),3*L^(2 : ℕ)+3*L*d,-(3*L+d),1]

/-- The physical angular weight on the complete native circle mean. -/
def spinTwoMean (q : XiZeroCopy) (L z X k : ℝ) : ℂ :=
  let U := fun p : Point => angularKernel q ((L^(2 : ℕ)+1-z^(2 : ℕ))/(2*L)) (p 0) (Real.log (p 1))
  let p : Point := ![X,Real.exp k]
  (-scalarLaplacian (scalarLaplacian U) p+2*scalarLaplacian U p)

private def coefficients (q : XiZeroCopy) (branch : Bool) (L z : ℝ) (i : Fin 5) : ℂ :=
  let s := physicalRate q branch
  let t := -s-3
  let etaS := (2*s+1)*(2*s+2)
  let etaT := (2*t+1)*(2*t+2)
  let kt := t*(t-1)/4
  etaS*(etaT*row11 L (L-z) i-36*kt*row21 L (L-z) i+
    12*kt*(2*s+3)/(L:ℂ)*row31 L (L-z) i)

/-- Complete reduced long-delay density, including the earlier onset derivative.
The angular factor is the actual spin-two native mean. -/
def density (q : XiZeroCopy) (branch : Bool) (L z X k x : ℝ) : ℂ :=
  let s := physicalRate q branch
  let t := -s-3
  let etaS := (2*s+1)*(2*s+2)
  let etaT := (2*t+1)*(2*t+2)
  let kt := t*(t-1)/4
  let y : ℂ := x-L
  let u : ℂ := x-(L-z)
  etaS*(etaT*y*u/(x:ℂ)^(6 : ℕ)-36*kt*y^(2 : ℕ)*u/(x:ℂ)^(7 : ℕ)+
    12*kt*(2*s+3)/(L:ℂ)*y^(3 : ℕ)*u/(x:ℂ)^(7 : ℕ))*spinTwoMean q L z X k

/-- The explicit reduced primitive uses only five inverse powers of radius. -/
def primitive (q : XiZeroCopy) (branch : Bool) (L z X k x : ℝ) : ℂ :=
  (∑ i : Fin 5, coefficients q branch L z i*(rationalBasis i x:ℂ))*spinTwoMean q L z X k

/-- Actual differentiation gives every term of the original reduced radial density. -/
theorem primitive_derivative (q : XiZeroCopy) (branch : Bool) (L z X k : ℝ)
    (x : Ioi (0:ℝ)) :
    HasDerivAt (primitive q branch L z X k) (density q branch L z X k x.val) x.val := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (rationalBasis_derivative i x).ofReal_comp.const_mul
      (coefficients q branch L z i))).mul_const (spinTwoMean q L z X k)
  apply h.congr_deriv
  dsimp only [density]
  apply congrArg (fun v : ℂ => v*spinTwoMean q L z X k)
  simp only [coefficients,row11,row21,row31,Fin.sum_univ_succ,
    Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,Matrix.cons_val_succ]
  push_cast
  norm_num
  have hx : (x.val:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt x.property)
  by_cases hL : (L:ℂ)=0
  · simp [hL]
    field_simp [hx]
    ring
  · field_simp [hx,hL]
    ring

/-- The complete reduced radial integral is an explicit difference of endpoint values. -/
theorem density_integral (q : XiZeroCopy) (branch : Bool) (L z X k : ℝ)
    (a b : Ioi (0:ℝ)) :
    (∫ x in a.val..b.val, density q branch L z X k x)=
      primitive q branch L z X k b.val-primitive q branch L z X k a.val := by
  have hp (x : ℝ) (hx : x ∈ uIcc a.val b.val) : 0 < x :=
    lt_of_lt_of_le (lt_min a.property b.property) hx.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => primitive_derivative q branch L z X k ⟨x,hp x hx⟩)
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hn : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hp x hx))
  unfold density
  fun_prop (disch := exact pow_ne_zero _ hn)

end
end RHTower.D4BMReducedOpticalTail
