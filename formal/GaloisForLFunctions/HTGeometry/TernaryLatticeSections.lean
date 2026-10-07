import GaloisForLFunctions.HTGeometry.TernaryLatticeCubic
import Mathlib.Data.List.Nodup

/-!
# Entire sections from the ternary lattice cubic family

Exact divided differences remove all nine distinguished fiber points.
No approximation, growth hypothesis, or inequality for the source is used.
-/

noncomputable section
open Complex Polynomial Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.TernaryLatticeSections

open TernaryLatticeCubic

def dividedQuotient (f : ℂ → ℂ) : List ℂ → ℂ → ℂ
  | [] => f
  | a::as => dividedQuotient (dslope f a) as

private theorem entire_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ (dslope f a) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (by simp)).mpr hf.differentiableOn

theorem dividedQuotient_entire (as : List ℂ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) : Differentiable ℂ (dividedQuotient f as) := by
  induction as generalizing f with
  | nil => exact hf
  | cons a as ih => exact ih (entire_dslope hf a)

theorem dividedQuotient_factor (as : List ℂ) (ha : as.Nodup) {f : ℂ → ℂ}
    (hf : ∀ a ∈ as, f a=0) (w : ℂ) :
    (as.map (fun a => w-a)).prod * dividedQuotient f as w=f w := by
  induction as generalizing f with
  | nil => simp [dividedQuotient]
  | cons a as ih =>
    obtain ⟨hna,has⟩ := List.nodup_cons.mp ha
    have hfa : f a=0 := hf a (by simp)
    have hg (b : ℂ) (hb : b ∈ as) : dslope f a b=0 := by
      have he := sub_smul_dslope f a b
      simp only [smul_eq_mul, hf b (by simp [hb]), hfa, sub_zero] at he
      exact (mul_eq_zero.mp he).resolve_left
        (sub_ne_zero.mpr (fun h => hna (h ▸ hb)))
    have hi := ih has hg
    simp only [List.map_cons, List.prod_cons, dividedQuotient]
    rw [mul_assoc, hi]
    simpa [smul_eq_mul, hfa] using sub_smul_dslope f a w

def integerRoots (m : ℤ) : List ℤ :=
  [0,3*q m,-3*q m,1,4,t m,-1,-4,-t m]

def fiberRoots (m : ℤ) : List ℂ := (integerRoots m).map (fun k : ℤ => (k : ℂ))

theorem integerRoots_nodup (m : ℤ) : (integerRoots m).Nodup := by
  have hq := q_ne_zero m
  have ht := t_mod_three m
  have ht1 := t_ne_one m
  have ht4 := t_ne_four m
  simp only [integerRoots, List.nodup_cons, List.mem_cons,
    List.mem_nil_iff, List.nodup_nil, or_false, not_or, and_true]
  repeat' apply And.intro
  all_goals first | omega | simp

theorem fiberRoots_nodup (m : ℤ) : (fiberRoots m).Nodup := by
  apply (List.nodup_map_iff (fun a b h => by exact_mod_cast h)).mpr
  exact integerRoots_nodup m

theorem fiberRoots_product (m : ℤ) (w : ℂ) :
    ((fiberRoots m).map (fun a => w-a)).prod=
      (A0 m).eval w*(A1 m).eval w*(A2 m).eval w := by
  simp [fiberRoots, integerRoots, eval_A0, eval_A1, eval_A2]
  ring

def mark (w : ℂ) : ℂ := exp (-ReflectedCubicExponentialModel.seam*w)

theorem mark_ne_zero (w : ℂ) : mark w ≠ 0 := exp_ne_zero _

theorem mark_add (u v : ℂ) : mark (u+v)=mark u*mark v := by
  simp only [mark, mul_add, exp_add]

theorem mark_neg (w : ℂ) : mark (-w)=(mark w)⁻¹ := by
  simp only [mark, mul_neg, exp_neg]

theorem mark_one : mark 1=omega^2 := by
  rw [mark, mul_one, ReflectedCubicExponentialModel.exp_neg_seam]
  have hq := omega_quadratic
  dsimp [omega] at hq ⊢
  linear_combination -hq

theorem mark_three : mark 3=1 := by
  rw [show (3 : ℂ)=1+1+1 by ring, mark_add, mark_add, mark_one]
  calc omega^2*omega^2*omega^2=(omega^3)^2 := by ring
    _=1 := by rw [omega_cube]; norm_num

theorem mark_three_int (k : ℤ) : mark (3*(k : ℂ))=1 := by
  change exp (-ReflectedCubicExponentialModel.seam*(3*(k : ℂ)))=1
  rw [show -ReflectedCubicExponentialModel.seam*(3*(k : ℂ))=
    (k : ℂ)*(-ReflectedCubicExponentialModel.seam*3) by ring, exp_int_mul]
  change (mark 3)^k=1
  rw [mark_three, one_zpow]

theorem mark_int_mod (k : ℤ) : mark (k : ℂ)=mark ((k%3 : ℤ) : ℂ) := by
  have hk : (k : ℂ)=((k%3 : ℤ) : ℂ)+3*((k/3 : ℤ) : ℂ) := by
    exact_mod_cast (Int.emod_add_mul_ediv k 3).symm
  rw [hk, mark_add, mark_three_int, mul_one]

theorem mark_int_zero {k : ℤ} (hk : k%3=0) : mark (k : ℂ)=1 := by
  rw [mark_int_mod, hk]
  simp [mark]

theorem mark_int_one {k : ℤ} (hk : k%3=1) : mark (k : ℂ)*omega=1 := by
  rw [mark_int_mod, hk]
  norm_cast
  rw [mark_one]
  convert omega_cube using 1
  ring

theorem mark_int_two {k : ℤ} (hk : k%3=2) : mark (k : ℂ)*omega^2=1 := by
  rw [mark_int_mod, hk]
  norm_cast
  rw [show (2 : ℂ)=1+1 by ring, mark_add, mark_one]
  calc omega^2*omega^2*omega^2=(omega^3)^2 := by ring
    _=1 := by rw [omega_cube]; norm_num

def residual (m : ℤ) (w : ℂ) : ℂ :=
  (denominator m).eval w-mark w*(numerator m).eval w

theorem residual_entire (m : ℤ) : Differentiable ℂ (residual m) := by
  have hn := (numerator m).differentiable
  have hd := (denominator m).differentiable
  change Differentiable ℂ (fun w => (denominator m).eval w-
    exp (-ReflectedCubicExponentialModel.seam*w)*(numerator m).eval w)
  fun_prop

theorem residual_zero_A0 (m : ℤ) (w : ℂ) (hw : (A0 m).eval w=0) :
    residual m w=0 := by
  have hf := (complete_fiber_one m w).mpr ((roots_A0 m w).mp hw)
  obtain ⟨k,rfl,hk⟩ := roots_A0_label m w hw
  simp [residual, hf, mark_int_zero hk]

theorem residual_zero_A1 (m : ℤ) (w : ℂ) (hw : (A1 m).eval w=0) :
    residual m w=0 := by
  have hf := (complete_fiber_omega m w).mpr ((roots_A1 m w).mp hw)
  obtain ⟨k,rfl,hk⟩ := roots_A1_label m w hw
  simp [residual, hf, ← mul_assoc, mark_int_one hk]

theorem residual_zero_A2 (m : ℤ) (w : ℂ) (hw : (A2 m).eval w=0) :
    residual m w=0 := by
  have hf := (complete_fiber_omega_sq m w).mpr ((roots_A2 m w).mp hw)
  obtain ⟨k,rfl,hk⟩ := roots_A2_label m w hw
  simp [residual, hf, ← mul_assoc, mark_int_two hk]

theorem residual_zero_root (m : ℤ) (w : ℂ) (hw : w ∈ fiberRoots m) :
    residual m w=0 := by
  have hp : ((fiberRoots m).map (fun a => w-a)).prod=0 := by
    apply List.prod_eq_zero_iff.mpr
    exact List.mem_map.mpr ⟨w,hw,sub_self w⟩
  rw [fiberRoots_product] at hp
  rcases mul_eq_zero.mp hp with hp | hp
  · rcases mul_eq_zero.mp hp with h0 | h1
    · exact residual_zero_A0 m w h0
    · exact residual_zero_A1 m w h1
  · exact residual_zero_A2 m w hp

def fiberConstant : ℂ := 6*(omega-omega^2)
def divisor (m : ℤ) (w : ℂ) : ℂ :=
  (numerator m).eval w^3-(denominator m).eval w^3

theorem fiberConstant_ne_zero : fiberConstant ≠ 0 :=
  mul_ne_zero (by norm_num) (sub_ne_zero.mpr omega_ne_sq)

theorem divisor_factor (m : ℤ) (w : ℂ) :
    divisor m w=fiberConstant*(A0 m).eval w*(A1 m).eval w*(A2 m).eval w := by
  have hs : (A1 m).eval w+(A2 m).eval w=2*(A0 m).eval w := by
    simpa using congrArg (fun p : ℂ[X] => p.eval w) (fiber_sum m)
  simp only [divisor, numerator, denominator, eval_sub, eval_mul, eval_C, fiberConstant]
  linear_combination 3*(omega-omega^2)*(A1 m).eval w*(A2 m).eval w*hs +
    ((A1 m).eval w^3+(A2 m).eval w^3)*omega_cube

def quotient (m : ℤ) (w : ℂ) : ℂ :=
  dividedQuotient (residual m) (fiberRoots m) w / fiberConstant

theorem quotient_entire (m : ℤ) : Differentiable ℂ (quotient m) := by
  exact (dividedQuotient_entire (fiberRoots m) (residual_entire m)).div_const _

theorem quotient_factor (m : ℤ) (w : ℂ) :
    divisor m w*quotient m w=residual m w := by
  have hq := dividedQuotient_factor (fiberRoots m) (fiberRoots_nodup m)
    (residual_zero_root m) w
  rw [fiberRoots_product] at hq
  rw [divisor_factor, quotient]
  calc
    _=(A0 m).eval w*(A1 m).eval w*(A2 m).eval w*
        dividedQuotient (residual m) (fiberRoots m) w := by
      field_simp [fiberConstant_ne_zero]
    _=residual m w := hq

theorem divisor_entire (m : ℤ) : Differentiable ℂ (divisor m) := by
  exact ((numerator m).differentiable.pow 3).sub ((denominator m).differentiable.pow 3)

theorem divisor_neg (m : ℤ) (w : ℂ) : divisor m (-w)= -divisor m w := by
  simp only [divisor, numerator_neg, denominator_neg]
  ring

theorem residual_neg (m : ℤ) (w : ℂ) :
    residual m (-w)= -(mark w)⁻¹*residual m w := by
  simp only [residual, numerator_neg, denominator_neg, mark_neg]
  field_simp [mark_ne_zero]
  ring

private theorem I_ne_int (k : ℤ) : I ≠ (k : ℂ) := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

theorem divisor_I_ne_zero (m : ℤ) : divisor m I ≠ 0 := by
  have h0 : (A0 m).eval I ≠ 0 := by
    intro h
    obtain ⟨k,hk,_⟩ := roots_A0_label m I h
    exact I_ne_int k hk
  have h1 : (A1 m).eval I ≠ 0 := by
    intro h
    obtain ⟨k,hk,_⟩ := roots_A1_label m I h
    exact I_ne_int k hk
  have h2 : (A2 m).eval I ≠ 0 := by
    intro h
    obtain ⟨k,hk,_⟩ := roots_A2_label m I h
    exact I_ne_int k hk
  rw [divisor_factor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero fiberConstant_ne_zero h0) h1) h2

private theorem quotient_unique (m : ℤ) {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (he : ∀ w, divisor m w*g w=residual m w) :
    g=quotient m := by
  apply AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => hg.analyticAt w)
    (fun w _ => (quotient_entire m).analyticAt w)
  filter_upwards [(divisor_entire m).continuous.continuousAt.eventually_ne
    (divisor_I_ne_zero m)] with w hw
  exact mul_left_cancel₀ hw ((he w).trans (quotient_factor m w).symm)

theorem quotient_neg (m : ℤ) (w : ℂ) :
    quotient m (-w)=(mark w)⁻¹*quotient m w := by
  have hg : Differentiable ℂ (fun z => mark z*quotient m (-z)) := by
    have hq := quotient_entire m
    dsimp [mark]
    fun_prop
  have he := quotient_unique m hg (fun z => by
    have hq := quotient_factor m (-z)
    rw [divisor_neg, residual_neg] at hq
    have hr := mark_ne_zero z
    field_simp at hq
    linear_combination -hq)
  have hz := congrFun he w
  have hr := mark_ne_zero w
  field_simp
  linear_combination hz

def lift (m : ℤ) (w : ℂ) : ℂ := 2+3*(denominator m).eval w^2*quotient m w

theorem lift_entire (m : ℤ) : Differentiable ℂ (lift m) := by
  have hd := (denominator m).differentiable
  have hq := quotient_entire m
  change Differentiable ℂ (fun w => 2+3*(denominator m).eval w^2*quotient m w)
  fun_prop

theorem lift_equation (m : ℤ) (w : ℂ) :
    divisor m w*lift m w=2*(numerator m).eval w^3-
      3*mark w*(numerator m).eval w*(denominator m).eval w^2+
      (denominator m).eval w^3 := by
  have hq := quotient_factor m w
  dsimp [divisor, residual] at hq
  dsimp [divisor, lift]
  linear_combination 3*(denominator m).eval w^2*hq

theorem lift_plus_cross (m : ℤ) (w : ℂ) :
    mark w*(numerator m).eval w*(lift m (-w)+1)=
      (denominator m).eval w*(lift m w+1) := by
  have hq := quotient_factor m w
  dsimp [divisor, residual] at hq
  rw [lift, lift, denominator_neg, quotient_neg]
  have hr := mark_ne_zero w
  field_simp
  linear_combination 3*hq

theorem cubic_lift_neg (m : ℤ) (w : ℂ) :
    mark w^3*ReflectedCubicExponentialModel.cubic (lift m (-w))=
      ReflectedCubicExponentialModel.cubic (lift m w) := by
  have hc := congrArg (fun z : ℂ => z^2) (lift_plus_cross m w)
  have hminus : lift m (-w)-2=
      3*(numerator m).eval w^2*(mark w)⁻¹*quotient m w := by
    rw [lift, denominator_neg, quotient_neg]
    ring
  have hplus : lift m w-2=3*(denominator m).eval w^2*quotient m w := by
    rw [lift]
    ring
  simp only [ReflectedCubicExponentialModel.cubic, hminus, hplus]
  have hr := mark_ne_zero w
  field_simp
  linear_combination quotient m w*hc

theorem mark_neg_conj (w : ℂ) : mark (-conj w)=conj (mark w) := by
  have hs : conj ReflectedCubicExponentialModel.seam=
      -ReflectedCubicExponentialModel.seam := by
    simp [ReflectedCubicExponentialModel.seam, map_ofNat]
  simp only [mark, ← exp_conj, map_mul, map_neg, hs]
  congr 1
  ring

theorem divisor_neg_conj (m : ℤ) (w : ℂ) :
    divisor m (-conj w)=conj (divisor m w) := by
  simp only [divisor, numerator_neg, denominator_neg, numerator_conj,
    denominator_conj, mul_pow, omega_cube, one_mul, map_sub, map_pow]

theorem residual_neg_conj (m : ℤ) (w : ℂ) :
    residual m (-conj w)=omega*conj (residual m w) := by
  simp only [residual, numerator_neg, denominator_neg, numerator_conj,
    denominator_conj, mark_neg_conj, map_sub, map_mul]
  ring

theorem quotient_neg_conj (m : ℤ) (w : ℂ) :
    quotient m (-conj w)=omega*conj (quotient m w) := by
  have hneg : Differentiable ℂ (fun z => quotient m (-z)) := by
    have hq := quotient_entire m
    fun_prop
  have hcon : Differentiable ℂ (fun z => conj (quotient m (-conj z))) := by
    intro z
    simpa [Function.comp_def] using (hneg (conj z)).conj_conj
  have hg : Differentiable ℂ (fun z => omega*conj (quotient m (-conj z))) := by
    fun_prop
  have he := quotient_unique m hg (fun z => by
    have hq := congrArg conj (quotient_factor m (-conj z))
    rw [divisor_neg_conj, residual_neg_conj] at hq
    simp only [map_mul, starRingEnd_self_apply, omega_conj] at hq
    linear_combination omega*hq+residual m z*omega_cube)
  have hw := congrArg conj (congrFun he w)
  simp only [map_mul, starRingEnd_self_apply, omega_conj] at hw
  linear_combination omega*hw-quotient m (-conj w)*omega_cube

theorem lift_neg_conj (m : ℤ) (w : ℂ) : lift m (-conj w)=conj (lift m w) := by
  simp only [lift, denominator_neg, numerator_conj, quotient_neg_conj,
    map_add, map_mul, map_ofNat, map_pow]
  linear_combination 3*conj ((denominator m).eval w)^2*
    conj (quotient m w)*omega_cube

theorem lift_at_pole (m : ℤ) (w : ℂ) (hw : (denominator m).eval w=0) :
    lift m w=2 := by simp [lift, hw]

theorem quotient_ne_zero_at_pole (m : ℤ) (w : ℂ)
    (hw : (denominator m).eval w=0) : quotient m w ≠ 0 := by
  have hn : (numerator m).eval w ≠ 0 := fun h => no_common_zero m w ⟨h,hw⟩
  intro hq
  have he := quotient_factor m w
  simp only [hq, mul_zero, residual, hw, zero_sub] at he
  exact mul_ne_zero (mark_ne_zero w) hn (neg_eq_zero.mp he.symm)

def sourceUnit (m : ℤ) (w : ℂ) : ℂ :=
  (3/4 : ℂ)*quotient m w*(lift m w+1)^2

theorem cubic_factor (m : ℤ) (w : ℂ) :
    ReflectedCubicExponentialModel.cubic (lift m w)=
      (denominator m).eval w^2*sourceUnit m w := by
  simp only [ReflectedCubicExponentialModel.cubic, sourceUnit]
  rw [lift]
  ring

theorem sourceUnit_entire (m : ℤ) : Differentiable ℂ (sourceUnit m) := by
  have hq := quotient_entire m
  have hh := lift_entire m
  change Differentiable ℂ (fun w => (3/4 : ℂ)*quotient m w*(lift m w+1)^2)
  fun_prop

theorem sourceUnit_ne_zero_at_pole (m : ℤ) (w : ℂ)
    (hw : (denominator m).eval w=0) : sourceUnit m w ≠ 0 := by
  rw [sourceUnit, lift_at_pole m w hw]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (quotient_ne_zero_at_pole m w hw))
    (by norm_num)

theorem cubic_order_at_pole (m : ℤ) (w : ℂ)
    (hw : (denominator m).eval w=0) :
    analyticOrderAt (fun z => ReflectedCubicExponentialModel.cubic (lift m z)) w=
      2*analyticOrderAt (fun z => (denominator m).eval z) w := by
  have he : (fun z => ReflectedCubicExponentialModel.cubic (lift m z))=
      (fun z => (denominator m).eval z)^2*(sourceUnit m) := funext (cubic_factor m)
  rw [he, analyticOrderAt_mul (((denominator m).differentiable.analyticAt w).pow 2)
    ((sourceUnit_entire m).analyticAt w),
    analyticOrderAt_pow ((denominator m).differentiable.analyticAt w)]
  have hu : analyticOrderAt (sourceUnit m) w=0 :=
    ((sourceUnit_entire m).analyticAt w).analyticOrderAt_eq_zero.mpr
      (sourceUnit_ne_zero_at_pole m w hw)
  rw [hu, add_zero]
  simp [nsmul_eq_mul]

end GaloisForLFunctions.HTGeometry.TernaryLatticeSections
