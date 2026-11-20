import GaloisForLFunctions.ArithmeticPositiveDuality.DistinctRootsForcedByABoundedPolyharmonicProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Minimal-degree coefficients at each nonlinear exponent

For derivative order k and p ≠ 1 use the profile
[1+(p−1)x²]₊^(k/(1−p)). Differentiation reduces the exponent by one
and raises the polynomial factor degree by at most one. At order k
the remaining power is exactly the p-th power of the original profile.
The sublinear profiles have compact support and are C^k across both
endpoints. The superlinear profiles are everywhere positive.
-/

noncomputable section
open Polynomial Filter Set
open scoped ContDiff Topology
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Power of the positive part, extended by zero on the negative ray for positive exponents. -/
def positivePartPower (b x : ℝ) := (max x 0)^b

theorem hasDerivAt_positivePartPower (b x : ℝ) (h : 0 < x ∨ 1 < b) :
    HasDerivAt (positivePartPower b) (b*positivePartPower (b-1) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hb := h.resolve_left hx.not_gt
    simp only [positivePartPower,max_eq_right hx.le,Real.zero_rpow (sub_pos.mpr hb).ne',mul_zero]
    apply (hasDerivAt_const x ((0:ℝ)^b)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx] with y hy
    simp only [positivePartPower,max_eq_right hy.le]
  · have hb := h.resolve_left (lt_irrefl _)
    have hL : HasDerivWithinAt (positivePartPower b) 0 (Iic 0) 0 := by
      have hl := (hasDerivAt_const (0:ℝ) ((0:ℝ)^b)).hasDerivWithinAt (s:=Iic 0)
      exact hl.congr_of_mem (fun y hy => by simp only [positivePartPower,max_eq_right (show y ≤ 0 from hy)])
        (show (0:ℝ) ∈ Iic 0 by simp)
    have hR : HasDerivWithinAt (positivePartPower b) 0 (Ici 0) 0 := by
      have hr := (Real.hasDerivAt_rpow_const (x:=(0:ℝ)) (p:=b) (Or.inr hb.le)).hasDerivWithinAt
        (s:=Ici 0)
      rw [Real.zero_rpow (sub_pos.mpr hb).ne',mul_zero] at hr
      exact hr.congr_of_mem (fun y hy => by simp only [positivePartPower,max_eq_left (show 0 ≤ y from hy)])
        (show (0:ℝ) ∈ Ici 0 by simp)
    simpa only [Iic_union_Ici,hasDerivWithinAt_univ,positivePartPower,max_self,
      Real.zero_rpow (sub_pos.mpr hb).ne',mul_zero] using hL.union hR
  · rw [show positivePartPower (b-1) x=x^(b-1) by simp only [positivePartPower,max_eq_left hx.le]]
    apply (Real.hasDerivAt_rpow_const (p:=b) (Or.inl hx.ne')).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with y hy
    simp only [positivePartPower,max_eq_left hy.le]

theorem lower_positivePartPower (b x : ℝ) (h : 0 < x ∨ 1 < b) :
    positivePartPower b x=x*positivePartPower (b-1) x := by
  by_cases hx : 0 < x
  · simpa only [positivePartPower,max_eq_left hx.le,sub_add_cancel,mul_comm] using Real.rpow_add_one hx.ne' (b-1)
  · have hb := h.resolve_left hx
    simp only [positivePartPower,max_eq_right (le_of_not_gt hx),Real.zero_rpow (zero_lt_one.trans hb).ne',
      Real.zero_rpow (sub_pos.mpr hb).ne',mul_zero]

/-- Polynomial factor multiplying the lowered quadratic weight after j
derivatives. The recurrence differentiates the preceding polynomial
and the preceding weight separately. -/
def quadraticPowerFactor (a d : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | j+1 => (1+C d*X^2)*(quadraticPowerFactor a d j).derivative+
      C (2*d*(a-j))*X*quadraticPowerFactor a d j

private theorem degree_quadraticPowerFactor (a d : ℝ) (j : ℕ) :
    (quadraticPowerFactor a d j).natDegree ≤ j := by
  induction j with
  | zero => simp [quadraticPowerFactor]
  | succ j ih =>
    cases j with
    | zero =>
      simp only [quadraticPowerFactor,derivative_one,mul_zero,zero_add,mul_one,Nat.cast_zero,sub_zero]
      exact (natDegree_C_mul_le (2*d*a) (X:ℝ[X])).trans_eq natDegree_X
    | succ j =>
      rw [quadraticPowerFactor]
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · have hq : (1+C d*X^2 : ℝ[X]).natDegree ≤ 2 := (natDegree_add_le _ _).trans
          (max_le (by norm_num) ((natDegree_C_mul_le d (X^2:ℝ[X])).trans_eq (natDegree_X_pow 2)))
        have hd := (natDegree_derivative_le (quadraticPowerFactor a d (j+1))).trans
          (Nat.sub_le_sub_right ih 1)
        exact natDegree_mul_le.trans (by omega)
      · have h₁ : (C (2*d*(a-(j+1:ℕ)))*X : ℝ[X]).natDegree ≤ 1 :=
          (natDegree_C_mul_le _ (X:ℝ[X])).trans_eq natDegree_X
        exact natDegree_mul_le.trans (by omega)

private def quadraticWeight (d x : ℝ) := 1+d*x^2

private theorem diff_quadraticWeight (d x : ℝ) :
    HasDerivAt (quadraticWeight d) (2*d*x) x := by
  apply ((((hasDerivAt_id x).pow 2).const_mul d).const_add 1).congr_deriv
  simp only [id_eq]
  ring

private theorem diff_weighted_factor (a d : ℝ) (j : ℕ) (x : ℝ)
    (h : 0 < quadraticWeight d x ∨ 1 < a-j) :
    HasDerivAt (fun y => (quadraticPowerFactor a d j).eval y*positivePartPower (a-j) (quadraticWeight d y))
      ((quadraticPowerFactor a d (j+1)).eval x*positivePartPower (a-(j+1:ℕ)) (quadraticWeight d x)) x := by
  have hq := diff_quadraticWeight d x
  have hpow := (hasDerivAt_positivePartPower _ _ h).comp x hq
  apply (((quadraticPowerFactor a d j).hasDerivAt x).mul hpow).congr_deriv
  simp only [quadraticPowerFactor,eval_add,eval_one,eval_mul,eval_C,eval_pow,eval_X,Nat.cast_add,Nat.cast_one,
    Function.comp_apply]
  rw [lower_positivePartPower _ _ h,show a-((j:ℝ)+1)=a-j-1 by ring]
  unfold quadraticWeight
  ring

private theorem weight_jet (a d : ℝ) (k : ℕ) (h : (∀ x, 0 < quadraticWeight d x) ∨ (k:ℝ)<a)
    (j : ℕ) (hj : j ≤ k) :
    iteratedDeriv j (fun x => positivePartPower a (quadraticWeight d x)) =
      fun x => (quadraticPowerFactor a d j).eval x*positivePartPower (a-j) (quadraticWeight d x) := by
  induction j with
  | zero => simp only [iteratedDeriv_zero,quadraticPowerFactor,eval_one,Nat.cast_zero,sub_zero,one_mul]
  | succ j ih =>
    rw [iteratedDeriv_succ,ih (by omega)]
    funext x
    apply (diff_weighted_factor a d j x _).deriv
    rcases h with h | h
    · exact Or.inl (h x)
    · exact Or.inr (by linarith only [h,show (j:ℝ)+1 ≤ k by exact_mod_cast hj])

private theorem smooth_quadratic_profile (a d : ℝ) (k : ℕ)
    (h : (∀ x, 0 < quadraticWeight d x) ∨ (k:ℝ)<a) :
    ContDiff ℝ (k:ℕ∞ω) (fun x => positivePartPower a (quadraticWeight d x)) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro j hj
    rw [weight_jet a d k h j hj]
    apply (quadraticPowerFactor a d j).continuous.mul
    apply continuous_iff_continuousAt.mpr
    intro x
    have hq : ContinuousAt (fun y => max (quadraticWeight d y) 0) x :=
      (diff_quadraticWeight d x).continuousAt.max continuousAt_const
    apply hq.rpow_const
    rcases h with he | he
    · exact Or.inl (ne_of_gt ((he x).trans_le (le_max_left _ _)))
    · exact Or.inr (by linarith only [he,show (j:ℝ) ≤ k by exact_mod_cast hj])
  · intro j hj
    rw [weight_jet a d k h j hj.le]
    intro x
    apply (diff_weighted_factor a d j x _).differentiableAt
    rcases h with he | he
    · exact Or.inl (he x)
    · exact Or.inr (by linarith only [he,show (j:ℝ)+1 ≤ k by exact_mod_cast hj])

/-- Explicit minimal-degree solution away from exponent one. Its quadratic
base is positive everywhere in the superlinear regime. -/
theorem quadratic_profile_at_nonlinear_power {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0 < p) (hp₁ : p≠1) :
    let k := 2*m
    let a := (k:ℝ)/(1-p)
    let u := fun x : ℝ => (max (1+(p-1)*x^2) 0)^a
    let P := C ((-1:ℝ)^m)*quadraticPowerFactor a (p-1) k
    P ≠ 0 ∧ P.natDegree=k ∧ ContDiff ℝ (k:ℕ∞ω) u ∧ (∃ M : ℝ, ∀ x, |u x|≤M) ∧
      (∀ x, 0≤u x) ∧ (∃ x, u x≠0) ∧
      ∀ x, (-1:ℝ)^m*iteratedDeriv k u x=P.eval x*(u x)^p := by
  let k := 2*m
  let d := p-1
  let a := (k:ℝ)/(1-p)
  let u := fun x => positivePartPower a (quadraticWeight d x)
  let P := C ((-1:ℝ)^m)*quadraticPowerFactor a d k
  have hk : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by dsimp [k]; omega)
  have hexp : a-(k:ℝ)=a*p := by
    have h := div_mul_cancel₀ (k:ℝ) (sub_ne_zero.mpr (Ne.symm hp₁))
    change a*(1-p)=(k:ℝ) at h
    linarith only [h]
  have ha' (h : p < 1) : (k:ℝ) < a := by
    apply (lt_div_iff₀ (sub_pos.mpr h)).mpr
    nlinarith only [mul_pos hk hp]
  have ha'' (h : 1 < p) : a < 0 := div_neg_of_pos_of_neg hk (sub_neg.mpr h)
  have hq (h : 1 < p) (x : ℝ) : 1 ≤ quadraticWeight d x :=
    le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr h.le) (sq_nonneg x))
  have hcase : (∀ x, 0 < quadraticWeight d x) ∨ (k:ℝ) < a := by
    rcases lt_or_gt_of_ne hp₁ with h | h
    · exact Or.inr (ha' h)
    · exact Or.inl fun x => zero_lt_one.trans_le (hq h x)
  have hu := smooth_quadratic_profile a d k hcase
  have hpos (x : ℝ) : 0 ≤ u x := Real.rpow_nonneg (le_max_right _ _) _
  have hb (x : ℝ) : |u x| ≤ 1 := by
    rw [abs_of_nonneg (hpos x)]
    rcases lt_or_gt_of_ne hp₁ with h | h
    · apply Real.rpow_le_one (le_max_right _ _) _ (hk.trans (ha' h)).le
      have hw : quadraticWeight d x ≤ 1 := by
        unfold quadraticWeight
        linarith only [mul_nonpos_of_nonpos_of_nonneg (show d ≤ 0 from sub_nonpos.mpr h.le) (sq_nonneg x)]
      exact max_le hw zero_le_one
    · exact Real.rpow_le_one_of_one_le_of_nonpos ((hq h x).trans (le_max_left _ _)) (ha'' h).le
  have h₀ : u 0=1 := by simp [u,positivePartPower,quadraticWeight]
  have hleft : u (-1)<u 0 := by
    have hq' : quadraticWeight d (-1)=p := by dsimp only [quadraticWeight,d]; ring
    rw [h₀]
    change (max (quadraticWeight d (-1)) 0)^a<1
    rw [hq',max_eq_left hp.le]
    rcases lt_or_gt_of_ne hp₁ with h | h
    · exact Real.rpow_lt_one hp.le h (hk.trans (ha' h))
    · exact Real.rpow_lt_one_of_one_lt_of_neg h (ha'' h)
  have he (x : ℝ) : (-1:ℝ)^m*iteratedDeriv k u x=P.eval x*(u x)^p := by
    have hj := congrFun (weight_jet a d k hcase k le_rfl) x
    change iteratedDeriv k u x=_ at hj
    rw [hj,hexp]
    simp only [P,eval_mul,eval_C,u,positivePartPower,Real.rpow_mul (le_max_right _ _),mul_assoc]
  have hP : P ≠ 0 := by
    intro hz
    have hk' : k-1+1=k := by dsimp only [k]; omega
    obtain ⟨t,_,ht⟩ := ordered_derivative_signs_of_rising_secant (by norm_num : (-1:ℝ)<0)
      hleft ⟨1,hb⟩ (k-1) (by simpa only [hk'] using hu)
    have hder := ht 0 (Nat.zero_le _)
    simp only [pow_zero,one_mul,hk'] at hder
    have h := he (t 0)
    rw [hz,eval_zero,zero_mul] at h
    exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hder.ne') h
  have hn : ∃ x, u x≠0 := ⟨0,h₀.trans_ne one_ne_zero⟩
  have hl := distinct_roots_of_polyharmonic_coefficient P hP hm hp hu ⟨1,hb⟩ hpos hn he
  have hd : P.natDegree=k := le_antisymm
    ((natDegree_C_mul_le _ _).trans (degree_quadraticPowerFactor a d k))
    (hl.trans ((Multiset.toFinset_card_le _).trans P.card_roots'))
  exact ⟨hP,hd,hu,⟨1,hb⟩,hpos,hn,he⟩

/-- Every prescribed positive nonlinear exponent attains the same minimal
degree 2m. The compact sublinear profile and the positive superlinear
profile both attain the lower bound, including simplicity of all roots. -/
theorem least_coefficient_degree_at_each_power {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0 < p) :
    IsLeast (polyharmonicCoefficientDegrees m p) (2*m) := by
  by_cases hp₁ : p=1
  · subst p
    exact least_polyharmonic_coefficient_degree hm
  constructor
  · exact ⟨_,_,quadratic_profile_at_nonlinear_power hm hp hp₁⟩
  · rintro d ⟨P,u,hP,rfl,hu,hb,hpos,hne,he⟩
    exact (distinct_roots_of_polyharmonic_coefficient P hP hm hp hu hb hpos hne he).trans
      ((Multiset.toFinset_card_le _).trans P.card_roots')

/-- Degrees realized with a smooth positive multiplier bounded by one.
Both the solution and the multiplier are allowed to vary. -/
def weightedPolyharmonicDegrees (m : ℕ) (p : ℝ) : Set ℕ :=
  {d | ∃ (P : ℝ[X]) (v u : ℝ → ℝ), P ≠ 0 ∧ P.natDegree=d ∧
    ContDiff ℝ (⊤:ℕ∞) v ∧ (∀ x, 0<v x ∧ v x≤1) ∧
    ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u ∧ (∃ M : ℝ, ∀ x, |u x|≤M) ∧
    (∀ x, 0 ≤ u x) ∧ (∃ x, u x≠0) ∧
    ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=(P.eval x*v x)*(u x)^p}

/-- Allowing even a smooth, strictly positive bounded multiplier lowers
the least degree by exactly one. A shifted arctangent attains it:
its first derivative is the reciprocal quadratic weight. -/
theorem least_weighted_coefficient_degree {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0<p) :
    IsLeast (weightedPolyharmonicDegrees m p) (2*m-1) := by
  have lower (P : ℝ[X]) (hP : P≠0) (v u : ℝ → ℝ) (hv : ∀ x, 0<v x)
      (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u) (hb : ∃ M : ℝ, ∀ x, |u x|≤M)
      (hpos : ∀ x, 0≤u x) (hne : ∃ x, u x≠0)
      (he : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=(P.eval x*v x)*(u x)^p) :
      2*m-1 ≤ P.natDegree := by
    obtain ⟨z,hz⟩ : ∃ z : ℝ, P.eval z≠0 := by
      by_contra! h
      exact hP (Polynomial.funext fun x => (h x).trans eval_zero.symm)
    obtain h | h := roots_or_zero_polyharmonic_profile P (fun x => (hv x).le)
      ⟨z,mul_ne_zero hz (hv z).ne'⟩ hm hp hu hb hpos he
    · exact h.trans ((Multiset.toFinset_card_le _).trans P.card_roots')
    · obtain ⟨x,hx⟩ := hne
      exact (hx (h x)).elim
  constructor
  · let j := 2*m-1
    have hj : j+1=2*m := by dsimp only [j]; omega
    let u := fun x : ℝ => (2+Real.pi/2)+Real.arctan x
    let Q := quadraticPowerFactor (-1) 1 j
    let P := C ((-1:ℝ)^m)*Q
    let v := fun x : ℝ => (1+x^2)^((-1:ℝ)-j)/(u x)^p
    have hu {n : ℕ∞ω} : ContDiff ℝ n u := contDiff_const.add Real.contDiff_arctan
    have hu₁ (x : ℝ) : 1≤u x := by
      dsimp only [u]
      linarith only [Real.neg_pi_div_two_lt_arctan x]
    have hu₀ (x : ℝ) : 0<u x := zero_lt_one.trans_le (hu₁ x)
    have hb : ∃ M : ℝ, ∀ x, |u x|≤M := ⟨2+Real.pi,fun x => by
      rw [abs_of_pos (hu₀ x)]
      dsimp only [u]
      linarith only [Real.arctan_lt_pi_div_two x]⟩
    have hv (x : ℝ) : 0<v x ∧ v x≤1 := by
      have hq : 1 ≤ 1+x^2 := le_add_of_nonneg_right (sq_nonneg x)
      have hpow := Real.rpow_pos_of_pos (hu₀ x) p
      exact ⟨div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hq) _) hpow,
        (div_le_one hpow).mpr ((Real.rpow_le_one_of_one_le_of_nonpos hq
          (by linarith only [Nat.cast_nonneg (α:=ℝ) j])).trans (Real.one_le_rpow (hu₁ x) hp.le))⟩
    have hvC : ContDiff ℝ (⊤:ℕ∞) v := by
      have hq : ContDiff ℝ (⊤:ℕ∞) (fun x : ℝ => 1+x^2) := by fun_prop
      exact (hq.rpow_const_of_ne (fun x => (by positivity : 0<1+x^2).ne')).div
        (hu.rpow_const_of_ne (fun x => (hu₀ x).ne')) (fun x => (Real.rpow_pos_of_pos (hu₀ x) p).ne')
    have hq (x : ℝ) : 0<quadraticWeight 1 x := by dsimp only [quadraticWeight]; positivity
    have hdu : deriv u=fun x => positivePartPower (-1) (quadraticWeight 1 x) := by
      funext x
      rw [show deriv u x=(1+x^2)⁻¹ from ((Real.hasDerivAt_arctan' x).const_add (2+Real.pi/2)).deriv]
      simp only [positivePartPower,Real.rpow_neg_one,quadraticWeight,one_mul,max_eq_left (by positivity : 0≤1+x^2)]
    have he (x : ℝ) : (-1:ℝ)^m*iteratedDeriv (2*m) u x=(P.eval x*v x)*(u x)^p := by
      rw [←hj,iteratedDeriv_succ',hdu,weight_jet (-1) 1 j (Or.inl hq) j le_rfl]
      simp only [P,Q,v,eval_mul,eval_C,positivePartPower,quadraticWeight,one_mul,max_eq_left (by positivity : 0≤1+x^2),
        mul_assoc,div_mul_cancel₀ _ (Real.rpow_pos_of_pos (hu₀ x) p).ne']
    have hP : P≠0 := by
      intro hz
      have hr : u 0<u 1 := by
        dsimp only [u]
        linarith only [Real.arctan_strictMono (show (0:ℝ)<1 by norm_num)]
      obtain ⟨t,_,ht⟩ := ordered_derivative_signs_of_rising_secant zero_lt_one hr hb j hu
      have hd := ht 0 (Nat.zero_le _)
      simp only [pow_zero,one_mul,hj] at hd
      have hh := he (t 0)
      rw [hz,eval_zero,zero_mul,zero_mul] at hh
      exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hd.ne') hh
    have hn : ∃ x, u x≠0 := ⟨0,(hu₀ 0).ne'⟩
    have hd : P.natDegree=j := le_antisymm
      ((natDegree_C_mul_le _ _).trans (degree_quadraticPowerFactor (-1) 1 j))
      (lower P hP v u (fun x => (hv x).1) hu hb (fun x => (hu₀ x).le) hn he)
    exact ⟨P,v,u,hP,hd,hvC,hv,hu,hb,fun x => (hu₀ x).le,hn,he⟩
  · rintro d ⟨P,v,u,hP,rfl,_,hv,hu,hb,hpos,hne,he⟩
    exact lower P hP v u (fun x => (hv x).1) hu hb hpos hne he

end GaloisForLFunctions.ArithmeticPositiveDuality
