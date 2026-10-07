import GaloisForLFunctions.HTGeometry.ReflectedCubicExponentialModel
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# A periodic cubic section with infinite branching

The rational coordinate `t (t-a)/(1-a t)`, pulled back along an exponential,
admits an everywhere entire cubic lift. The exact Laurent factorization
records the cancellations before any meromorphic quotient is evaluated.
This is a countermodel to finite-branching rigidity, not a model of Xi.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.PeriodicLatticeSections

local notation "cubic" => ReflectedCubicExponentialModel.cubic

def a : ℂ := (Real.sqrt (2/3) : ℝ)
def numerator (t : ℂ) : ℂ := t*(t-a)
def denominator (t : ℂ) : ℂ := 1-a*t
def quartic (t : ℂ) : ℂ := t^4-3*a*t^3+3*t^2-3*a*t+1
def smallFactor (t : ℂ) : ℂ := a*t^2+t+a
def symmetricFactor (t : ℂ) : ℂ := t^6+a*t^5+(2/3)*t^4+(2/3)*t^2+a*t+1
def quotient (t : ℂ) : ℂ := -smallFactor t/t^7
def lift (t : ℂ) : ℂ := 2+3*(denominator t)^2*quotient t
def factor (t : ℂ) : ℂ := denominator t*(t-a)*symmetricFactor t

theorem a_sq : a^2=2/3 := by
  unfold a
  rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2/3)]
  norm_num

theorem a_cube : a^3=(2/3)*a := by
  calc
    a^3=a^2*a := by ring
    _=(2/3)*a := by rw [a_sq]

theorem a_ne_zero : a ≠ 0 := by
  intro h
  have := a_sq
  norm_num [h] at this

theorem a_conj : conj a=a := by simp [a]

theorem divisor_factor (t : ℂ) :
    numerator t^3-denominator t^3=(t^2-1)*quartic t := by
  dsimp [numerator,denominator,quartic]
  ring_nf
  rw [a_sq]
  ring

theorem residual_factor (t : ℂ) :
    t^8*denominator t-numerator t= -t*(t^2-1)*quartic t*smallFactor t := by
  dsimp [numerator,denominator,quartic,smallFactor]
  ring_nf
  rw [a_sq]
  ring

theorem quotient_factor {t : ℂ} (ht : t ≠ 0) :
    (numerator t^3-denominator t^3)*quotient t=
      denominator t-t⁻¹^8*numerator t := by
  rw [divisor_factor]
  dsimp [quotient]
  have he := residual_factor t
  field_simp
  linear_combination -he

theorem lift_plus {t : ℂ} (ht : t ≠ 0) :
    lift t+1=3*(t-a)*symmetricFactor t/t^7 := by
  dsimp [lift,quotient,denominator,smallFactor,symmetricFactor]
  field_simp
  ring_nf
  rw [a_cube,a_sq]
  ring

theorem cubic_factor {t : ℂ} (ht : t ≠ 0) :
    cubic (lift t)= -(27/4)*(factor t)^2*smallFactor t/t^21 := by
  rw [ReflectedCubicExponentialModel.cubic,lift_plus ht]
  dsimp [lift,quotient,factor]
  field_simp
  ring

theorem smallFactor_inv {t : ℂ} (ht : t ≠ 0) :
    smallFactor t⁻¹=smallFactor t/t^2 := by
  dsimp [smallFactor]
  field_simp
  ring

theorem symmetricFactor_inv {t : ℂ} (ht : t ≠ 0) :
    symmetricFactor t⁻¹=symmetricFactor t/t^6 := by
  dsimp [symmetricFactor]
  field_simp
  ring

theorem factor_inv {t : ℂ} (ht : t ≠ 0) : factor t⁻¹=factor t/t^8 := by
  simp only [factor,symmetricFactor_inv ht,denominator]
  field_simp

theorem cubic_inv {t : ℂ} (ht : t ≠ 0) :
    cubic (lift t⁻¹)=t^24*cubic (lift t) := by
  rw [cubic_factor (inv_ne_zero ht),cubic_factor ht,factor_inv ht,smallFactor_inv ht]
  field_simp

def parameter (L : ℝ) (s : ℂ) : ℂ := exp (L*(s-1/2)/12)
def markedLift (L : ℝ) (s : ℂ) : ℂ := lift (parameter L s)
def source (L : ℝ) (s : ℂ) : ℂ := exp (L*s)*cubic (markedLift L s)

theorem parameter_ne_zero (L : ℝ) (s : ℂ) : parameter L s ≠ 0 := exp_ne_zero _

theorem markedLift_entire (L : ℝ) : Differentiable ℂ (markedLift L) := by
  have ht : ∀ s : ℂ, exp ((L : ℂ)*(s-1/2)/12)^7 ≠ 0 :=
    fun s => pow_ne_zero _ (exp_ne_zero _)
  unfold markedLift lift quotient smallFactor denominator parameter
  fun_prop

theorem source_entire (L : ℝ) : Differentiable ℂ (source L) := by
  have hh := markedLift_entire L
  unfold source ReflectedCubicExponentialModel.cubic
  fun_prop

theorem parameter_reflection (L : ℝ) (s : ℂ) :
    parameter L (1-s)=(parameter L s)⁻¹ := by
  rw [parameter,parameter,← exp_neg]
  congr 1
  ring

theorem source_reflection (L : ℝ) (s : ℂ) : source L (1-s)=source L s := by
  have he : exp ((L : ℂ)*(1-s))*(parameter L s)^24=exp (L*s) := by
    rw [parameter,← exp_nat_mul,← exp_add]
    congr 1
    ring
  simp only [source,markedLift,parameter_reflection,cubic_inv (parameter_ne_zero L s)]
  rw [← mul_assoc,he]

theorem parameter_conj (L : ℝ) (s : ℂ) :
    parameter L (conj s)=conj (parameter L s) := by
  simp [parameter,← exp_conj,map_ofNat]

theorem lift_conj (t : ℂ) : lift (conj t)=conj (lift t) := by
  simp [lift,quotient,denominator,smallFactor,a_conj,map_ofNat]

theorem source_conj (L : ℝ) (s : ℂ) : source L (conj s)=conj (source L s) := by
  simp [source,markedLift,parameter_conj,lift_conj,
    ReflectedCubicExponentialModel.cubic,← exp_conj,map_ofNat]

theorem source_marked (L : ℝ) (s : ℂ) :
    source L s*exp (-L*s)=cubic (markedLift L s) := by
  have he : exp ((L : ℂ)*s)*exp (-L*s)=1 := by
    rw [← exp_add,show (L : ℂ)*s + -L*s=0 by ring,exp_zero]
  dsimp [source]
  linear_combination cubic (markedLift L s)*he

def point (L : ℝ) (t : ℂ) (k : ℤ) : ℂ :=
  1/2+12*(log t+k*(2*Real.pi*I))/L

theorem parameter_point {L : ℝ} (hL : L ≠ 0) {t : ℂ} (ht : t ≠ 0) (k : ℤ) :
    parameter L (point L t k)=t := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have he : (L : ℂ)*(point L t k-1/2)/12=log t+k*(2*Real.pi*I) := by
    dsimp [point]
    field_simp
    ring
  rw [parameter,he]
  calc
    exp (log t+k*(2*Real.pi*I))=exp (log t) :=
      exp_eq_exp_iff_exists_int.mpr ⟨k,rfl⟩
    _=t := exp_log ht

theorem point_injective {L : ℝ} (hL : L ≠ 0) (t : ℂ) :
    Function.Injective (point L t) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr (k : ℤ) :
      ((L : ℂ)*(point L t k-1/2)/12-log t)/(2*Real.pi*I)=(k : ℂ) := by
    dsimp [point]
    field_simp
    ring
  intro j k hjk
  have hh := congrArg (fun s : ℂ => ((L : ℂ)*(s-1/2)/12-log t)/(2*Real.pi*I)) hjk
  rw [hr,hr] at hh
  exact_mod_cast hh

theorem parameter_deriv (L : ℝ) (s : ℂ) :
    HasDerivAt (parameter L) (parameter L s*((L : ℂ)/12)) s := by
  have hs : HasDerivAt (fun s : ℂ => (L : ℂ)*(s-1/2)/12) ((L : ℂ)/12) s := by
    convert! (((hasDerivAt_id s).sub_const (1/2)).const_mul (L : ℂ)).div_const 12 using 1
    simp
  exact (hasDerivAt_exp _).comp s hs

theorem denominator_at_pole : denominator a⁻¹=0 := by
  simp [denominator,a_ne_zero]

theorem lift_at_pole : lift a⁻¹=2 := by simp [lift,denominator_at_pole]

theorem quotient_at_pole_ne_zero : quotient a⁻¹ ≠ 0 := by
  have hc : smallFactor a⁻¹=(8/3)/a := by
    dsimp [smallFactor]
    field_simp [a_ne_zero]
    ring_nf
    rw [a_sq]
    norm_num
  simp [quotient,hc,a_ne_zero]

theorem pole_off_line {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    (point L a⁻¹ k).re ≠ 1/2 := by
  let s := point L a⁻¹ k
  have ht : parameter L s=a⁻¹ := parameter_point hL (inv_ne_zero a_ne_zero) k
  intro hr
  have hs : conj s=1-s := by
    apply Complex.ext <;> simp [s,hr]
    ring
  have he := congrArg (parameter L) hs
  rw [parameter_conj,parameter_reflection,ht,map_inv₀,a_conj,inv_inv] at he
  have haa : a^2=1 := by
    have hh := congrArg (fun z : ℂ => z*a) he
    simpa [a_ne_zero,pow_two] using hh.symm
  rw [a_sq] at haa
  norm_num at haa

def sourceUnit (L : ℝ) (s : ℂ) : ℂ :=
  exp (L*s)*(3/4)*quotient (parameter L s)*(markedLift L s+1)^2

theorem sourceUnit_entire (L : ℝ) : Differentiable ℂ (sourceUnit L) := by
  have hh := markedLift_entire L
  have ht : ∀ s : ℂ, exp ((L : ℂ)*(s-1/2)/12)^7 ≠ 0 :=
    fun s => pow_ne_zero _ (exp_ne_zero _)
  unfold sourceUnit quotient smallFactor parameter
  fun_prop

theorem source_factor (L : ℝ) (s : ℂ) :
    source L s=(denominator (parameter L s))^2*sourceUnit L s := by
  simp only [source,sourceUnit,markedLift,ReflectedCubicExponentialModel.cubic,lift]
  ring

theorem source_zero {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    source L (point L a⁻¹ k)=0 := by
  rw [source_factor,parameter_point hL (inv_ne_zero a_ne_zero),denominator_at_pole]
  simp

theorem sourceUnit_at_pole_ne_zero {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    sourceUnit L (point L a⁻¹ k) ≠ 0 := by
  simp [sourceUnit,markedLift,parameter_point hL (inv_ne_zero a_ne_zero),
    lift_at_pole,exp_ne_zero,quotient_at_pole_ne_zero]
  norm_num

theorem source_order_at_pole {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    analyticOrderAt (source L) (point L a⁻¹ k)=2 := by
  let s := point L a⁻¹ k
  let q : ℂ → ℂ := fun z => denominator (parameter L z)
  have hq : Differentiable ℂ q := by unfold q denominator parameter; fun_prop
  have hq0 : q s=0 := by
    simp [q,s,parameter_point hL (inv_ne_zero a_ne_zero),denominator_at_pole]
  have hqd : HasDerivAt q (-((L : ℂ)/12)) s := by
    convert! ((parameter_deriv L s).const_mul a).const_sub 1 using 1
    rw [show parameter L s=a⁻¹ from parameter_point hL (inv_ne_zero a_ne_zero) k]
    field_simp [a_ne_zero]
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have ho : analyticOrderAt q s=1 :=
    (hq.analyticAt s).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hq0
      (by rw [hqd.deriv]; exact neg_ne_zero.mpr (div_ne_zero hLc (by norm_num)))
  have hu : analyticOrderAt (sourceUnit L) s=0 :=
    ((sourceUnit_entire L).analyticAt s).analyticOrderAt_eq_zero.mpr
      (sourceUnit_at_pole_ne_zero hL k)
  have he : source L=q^2*sourceUnit L := funext (source_factor L)
  rw [he,analyticOrderAt_mul ((hq.pow 2).analyticAt s)
    ((sourceUnit_entire L).analyticAt s),analyticOrderAt_pow (hq.analyticAt s),ho,hu]
  norm_num [nsmul_eq_mul]

/-- An entire reflected real source, with a cubic lift for mark two and infinitely
many distinct off-line zeros, each of exact order two. -/
theorem reflected_integer_marked_periodic_source :
    Differentiable ℂ (source (Real.log 2)) ∧
    Differentiable ℂ (markedLift (Real.log 2)) ∧
    (∀ s, source (Real.log 2) (1-s)=source (Real.log 2) s) ∧
    (∀ s, source (Real.log 2) (conj s)=conj (source (Real.log 2) s)) ∧
    (∀ s, source (Real.log 2) s*exp (-(Real.log 2 : ℂ)*s)=
      cubic (markedLift (Real.log 2) s)) ∧
    ∃ ρ : ℤ → ℂ, Function.Injective ρ ∧ ∀ k,
      (ρ k).re ≠ 1/2 ∧ source (Real.log 2) (ρ k)=0 ∧
      analyticOrderAt (source (Real.log 2)) (ρ k)=2 := by
  have hL : Real.log 2 ≠ 0 := Real.log_ne_zero.mpr (by norm_num)
  exact ⟨source_entire _,markedLift_entire _,source_reflection _,source_conj _,source_marked _,
    point (Real.log 2) a⁻¹,point_injective hL _,fun k =>
      ⟨pole_off_line hL k,source_zero hL k,source_order_at_pole hL k⟩⟩

end GaloisForLFunctions.HTGeometry.PeriodicLatticeSections
