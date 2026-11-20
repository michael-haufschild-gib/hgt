import GaloisForLFunctions.ArithmeticPositiveDuality.ExtremalPolynomialCoefficientsAtEachNonlinearPower

/-!
# Every coefficient degree above the polyharmonic order at sublinear powers

On the interval (−1,1) take the product of the two endpoint distances
raised to different powers, and set it equal to zero outside. Its k-th
derivative contains a Jacobi polynomial of exact degree k. Increasing
one endpoint exponent makes the coefficient acquire any prescribed extra
multiplicity there, including odd multiplicities.
-/

noncomputable section
open Polynomial Set
open scoped ContDiff
namespace GaloisForLFunctions.ArithmeticPositiveDuality

private def jacobiSlope (a b : ℝ) (j : ℕ) : ℝ[X] :=
  C (a-b)+C (2*j-a-b)*X

/-- Polynomial left by j derivatives of the two endpoint powers after
lowering both exponents by j. -/
def intervalJacobiFactor (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | j+1 => (1-X^2)*(intervalJacobiFactor a b j).derivative+jacobiSlope a b j*intervalJacobiFactor a b j

private theorem jacobi_degree_le (a b : ℝ) (j : ℕ) : (intervalJacobiFactor a b j).natDegree≤j := by
  have hs (r : ℕ) : (jacobiSlope a b r).natDegree≤1 := (natDegree_add_le _ _).trans
    (max_le (by simp) ((natDegree_C_mul_le _ (X:ℝ[X])).trans_eq natDegree_X))
  induction j with
  | zero => simp [intervalJacobiFactor]
  | succ j ih =>
    cases j with
    | zero => simpa only [intervalJacobiFactor,derivative_one,mul_zero,mul_one,zero_add] using hs 0
    | succ j =>
      rw [intervalJacobiFactor]
      apply (natDegree_add_le _ _).trans
      have hd := (natDegree_derivative_le (intervalJacobiFactor a b (j+1))).trans (Nat.sub_le_sub_right ih 1)
      have hq : (1-X^2 : ℝ[X]).natDegree≤2 := (natDegree_sub_le _ _).trans
        (max_le (by simp) (natDegree_X_pow 2).le)
      exact max_le (natDegree_mul_le.trans (by omega)) (natDegree_mul_le.trans (by have := hs (j+1); omega))

private def endpointWeight (a b x : ℝ) :=
  positivePartPower a (1+x)*positivePartPower b (1-x)

private theorem endpoint_jet_step (a b : ℝ) (j : ℕ) (ha : 1<a-j) (hb : 1<b-j) (x : ℝ) :
    HasDerivAt (fun y => (intervalJacobiFactor a b j).eval y*endpointWeight (a-j) (b-j) y)
      ((intervalJacobiFactor a b (j+1)).eval x*endpointWeight (a-(j+1:ℕ)) (b-(j+1:ℕ)) x) x := by
  let L := fun t : ℝ => 1+t
  let R := fun t : ℝ => 1-t
  have hL : HasDerivAt L 1 x := by simpa only [L,id_eq] using (hasDerivAt_id x).const_add 1
  have hR : HasDerivAt R (-1) x := by simpa only [R,id_eq] using (hasDerivAt_id x).const_sub 1
  have hl := (hasDerivAt_positivePartPower (a-j) (L x) (Or.inr ha)).comp x hL
  have hr := (hasDerivAt_positivePartPower (b-j) (R x) (Or.inr hb)).comp x hR
  apply (((intervalJacobiFactor a b j).hasDerivAt x).mul (hl.mul hr)).congr_deriv
  simp only [endpointWeight,intervalJacobiFactor,jacobiSlope,eval_add,eval_sub,eval_mul,eval_pow,eval_one,eval_C,eval_X,
    Pi.mul_apply,Function.comp_apply,Nat.cast_succ,show a-((j:ℝ)+1)=a-j-1 by ring,show b-((j:ℝ)+1)=b-j-1 by ring,L,R]
  rw [lower_positivePartPower (a-j) (1+x) (Or.inr ha),lower_positivePartPower (b-j) (1-x) (Or.inr hb)]
  ring

private theorem endpoint_jet {a b : ℝ} {k : ℕ} (ha : (k:ℝ)<a) (hb : (k:ℝ)<b) {j : ℕ} (hj : j≤k) :
    iteratedDeriv j (endpointWeight a b)=fun x => (intervalJacobiFactor a b j).eval x*endpointWeight (a-j) (b-j) x := by
  induction j with
  | zero => simp only [iteratedDeriv_zero,intervalJacobiFactor,eval_one,Nat.cast_zero,sub_zero,one_mul]
  | succ j ih =>
    rw [iteratedDeriv_succ,ih (by omega)]
    have h : (j:ℝ)+1≤k := by exact_mod_cast hj
    exact funext fun x => (endpoint_jet_step a b j (by linarith only [ha,h]) (by linarith only [hb,h]) x).deriv

private theorem smooth_endpoint_weight {a b : ℝ} {k : ℕ} (ha : (k:ℝ)<a) (hb : (k:ℝ)<b) :
    ContDiff ℝ (k:ℕ∞ω) (endpointWeight a b) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro j hj
    rw [endpoint_jet ha hb hj]
    apply (intervalJacobiFactor a b j).continuous.mul
    have h : (j:ℝ)≤k := by exact_mod_cast hj
    have left : Continuous (fun x : ℝ => max (1+x) 0) := by fun_prop
    have right : Continuous (fun x : ℝ => max (1-x) 0) := by fun_prop
    apply Continuous.mul
    · exact left.rpow_const fun _ => Or.inr (by linarith only [h,ha])
    · exact right.rpow_const fun _ => Or.inr (by linarith only [h,hb])
  · intro j hj
    rw [endpoint_jet ha hb hj.le]
    have h : (j:ℝ)+1≤k := by exact_mod_cast hj
    exact fun x => (endpoint_jet_step a b j (by linarith only [h,ha]) (by linarith only [h,hb]) x).differentiableAt

private theorem endpoint_nonneg (a b x : ℝ) : 0≤endpointWeight a b x :=
  mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (Real.rpow_nonneg (le_max_right _ _) _)

private theorem endpoint_support {a b : ℝ} (ha : 0<a) (hb : 0<b) {x : ℝ} (hx : x≤ -1 ∨ 1≤x) :
    endpointWeight a b x=0 := by
  rcases hx with h | h
  · simp only [endpointWeight,positivePartPower,max_eq_right (by linarith only [h] : 1+x≤0),
      Real.zero_rpow ha.ne',zero_mul]
  · simp only [endpointWeight,positivePartPower,max_eq_right (sub_nonpos.mpr h),
      Real.zero_rpow hb.ne',mul_zero]

private theorem endpoint_one (a b : ℝ) : endpointWeight a b 0=1 := by
  simp [endpointWeight,positivePartPower]

/-- At derivative order k the Jacobi factor has k distinct simple
real roots. This follows from the alternating derivative readings of the
compactly supported positive profile, independently of orthogonality. -/
theorem endpoint_polynomial_exact_degree {k : ℕ} {a b : ℝ} (ha : (k:ℝ)<a) (hb : (k:ℝ)<b) :
    (intervalJacobiFactor a b k).natDegree=k ∧ (intervalJacobiFactor a b k).Splits ∧ (intervalJacobiFactor a b k).roots.Nodup := by
  have ha' := (Nat.cast_nonneg k).trans_lt ha
  have hb' := (Nat.cast_nonneg k).trans_lt hb
  have hu := smooth_endpoint_weight ha hb
  have hbound : ∃ M : ℝ, ∀ x, |endpointWeight a b x|≤M := by
    obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hu.continuous.continuousOn (s:=Icc (-1:ℝ) 1))
    refine ⟨max B 0,fun x => ?_⟩
    by_cases hx : x∈Icc (-1:ℝ) 1
    · exact (hB x hx).trans (le_max_left _ _)
    · rw [endpoint_support ha' hb' (by simp only [mem_Icc,not_and_or,not_le] at hx; exact hx.imp le_of_lt le_of_lt),abs_zero]
      exact le_max_right _ _
  have hsmall (A ε : ℝ) (hε : 0<ε) :
      (∃ x<A, |endpointWeight a b x|<ε) ∧ ∃ x>A, |endpointWeight a b x|<ε := by
    refine ⟨⟨min A (-1)-1,by linarith only [min_le_left A (-1)],?_⟩,
      ⟨max A 1+1,by linarith only [le_max_left A 1],?_⟩⟩
    · rw [endpoint_support ha' hb' (Or.inl (by linarith only [min_le_right A (-1)])),abs_zero]; exact hε
    · rw [endpoint_support ha' hb' (Or.inr (by linarith only [le_max_right A 1])),abs_zero]; exact hε
  obtain ⟨t,ht,hs⟩ := ordered_derivative_signs_of_two_small_tails hbound
    ⟨0,by rw [endpoint_one]; exact zero_lt_one⟩ hsmall k hu
  have alternating (j : ℕ) (hj : j≤k) : 0<(-1:ℝ)^j*(intervalJacobiFactor a b k).eval (t j) := by
    have h := hs j hj
    rw [endpoint_jet ha hb (le_refl k)] at h
    change 0<(-1:ℝ)^j*((intervalJacobiFactor a b k).eval _*endpointWeight _ _ _) at h
    rw [←mul_assoc] at h
    exact ((mul_pos_iff.mp h).resolve_right (fun h' => (endpoint_nonneg _ _ _).not_gt h'.2)).1
  have h := SignAlternation.card_roots_toFinset_ge_of_alternating ht alternating
  have h₁ := Multiset.toFinset_card_le (intervalJacobiFactor a b k).roots
  have h₂ := (intervalJacobiFactor a b k).card_roots'
  have h₃ := jacobi_degree_le a b k
  exact ⟨by omega,splits_iff_card_roots.mpr (by omega),Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega)⟩

/-- Each differentiation at the left endpoint introduces the factor
2(a−j); none vanishes before derivative order k. -/
private theorem left_endpoint_jacobi_pos {a b : ℝ} {k : ℕ} (ha : (k:ℝ)<a) :
    0<(intervalJacobiFactor a b k).eval (-1) := by
  induction k with
  | zero => simp [intervalJacobiFactor]
  | succ j ih =>
    have hj : (j:ℝ)<a := lt_trans (by exact_mod_cast Nat.lt_succ_self j) ha
    have h := mul_pos (mul_pos (by norm_num : (0:ℝ)<2) (sub_pos.mpr hj)) (ih hj)
    simp only [intervalJacobiFactor,jacobiSlope,eval_add,eval_sub,eval_mul,eval_pow,eval_one,eval_C,eval_X]
    linarith only [h]

private theorem absorb_endpoint_power {a p : ℝ} {k j : ℕ} (ha : (k:ℝ)<a) (hp : 0<p)
    (he : a-k=a*p+j) (x : ℝ) :
    positivePartPower (a-k) x=x^j*(positivePartPower a x)^p := by
  by_cases hx : 0<x
  · simp only [positivePartPower,max_eq_left hx.le,←Real.rpow_mul hx.le,he,Real.rpow_add hx,
      Real.rpow_natCast,mul_comm]
  · simp only [positivePartPower,max_eq_right (le_of_not_gt hx),Real.zero_rpow (sub_pos.mpr ha).ne',
      Real.zero_rpow ((Nat.cast_nonneg k).trans_lt ha).ne',Real.zero_rpow hp.ne',mul_zero]

/-- A compactly supported solution realizes any prescribed degree k+j.
Its coefficient has an explicit factor (1+X)^j at the left endpoint. -/
theorem sublinear_degree_with_endpoint_factor {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : p∈Ioo (0:ℝ) 1) (j : ℕ) :
    ∃ (P : ℝ[X]) (u : ℝ → ℝ), P≠0 ∧ P.natDegree=2*m+j ∧ P.rootMultiplicity (-1)=j ∧
      ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u ∧ (∀ x, 0≤u x) ∧ u 0=1 ∧
      (∀ x, x≤ -1 ∨ 1≤x → u x=0) ∧
      ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=P.eval x*(u x)^p := by
  let k := 2*m
  let a := ((k:ℝ)+j)/(1-p)
  let b := (k:ℝ)/(1-p)
  have hk : 0<(k:ℝ) := by exact_mod_cast (show 0<k by dsimp only [k]; omega)
  have hden := sub_pos.mpr hp.2
  have ha : (k:ℝ)<a := (lt_div_iff₀ hden).mpr (by linarith only [mul_pos hk hp.1,Nat.cast_nonneg (α:=ℝ) j])
  have hb : (k:ℝ)<b := (lt_div_iff₀ hden).mpr (by linarith only [mul_pos hk hp.1])
  let Q := intervalJacobiFactor a b k
  let S := C ((-1:ℝ)^m)*Q
  have hd : Q.natDegree=k := (endpoint_polynomial_exact_degree ha hb).1
  have hQ : Q≠0 := by intro hz; rw [hz,natDegree_zero] at hd; dsimp only [k] at hd; omega
  have hs : (-1:ℝ)^m≠0 := pow_ne_zero _ (by norm_num)
  have hS : S≠0 := mul_ne_zero (C_ne_zero.mpr hs) hQ
  have hX : (X+1 : ℝ[X]).natDegree=1 := by simpa only [map_one] using natDegree_X_add_C (1:ℝ)
  have hX₀ : (X+1 : ℝ[X]) ≠ 0 := by intro hz; rw [hz,natDegree_zero] at hX; contradiction
  have hprod := mul_ne_zero hS (pow_ne_zero j hX₀)
  have hroot : ¬S.IsRoot (-1) := by
    change (C ((-1:ℝ)^m)*Q).eval (-1)≠0
    rw [eval_mul,eval_C]
    exact mul_ne_zero hs (left_endpoint_jacobi_pos (b:=b) ha).ne'
  have hlinear : (X+1 : ℝ[X])=X-C (-1:ℝ) := by simp
  refine ⟨S*(X+1)^j,endpointWeight a b,hprod,?_,?_,
    smooth_endpoint_weight ha hb,endpoint_nonneg a b,endpoint_one a b,fun _ => endpoint_support (hk.trans ha) (hk.trans hb),?_⟩
  · rw [natDegree_mul hS (pow_ne_zero _ hX₀),natDegree_pow,hX,Nat.mul_one]
    exact congrArg (·+j) ((natDegree_C_mul_of_isUnit hs.isUnit Q).trans hd)
  · rw [rootMultiplicity_mul hprod,rootMultiplicity_eq_zero hroot,hlinear,rootMultiplicity_X_sub_C_pow,zero_add]
  · intro x
    have hleft : a-k=a*p+j := by
      have hh : a*(1-p)=(k:ℝ)+j := div_mul_cancel₀ _ hden.ne'
      linarith only [hh]
    have hright : b-k=b*p+(0:ℕ) := by
      have hh : b*(1-p)=(k:ℝ) := div_mul_cancel₀ _ hden.ne'
      push_cast
      linarith only [hh]
    rw [endpoint_jet ha hb (le_refl k)]
    have hn (v y : ℝ) : 0 ≤ positivePartPower v y := Real.rpow_nonneg (le_max_right _ _) v
    simp only [endpointWeight,S,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one,
      absorb_endpoint_power ha hp.1 hleft,absorb_endpoint_power hb hp.1 (j:=0) hright,pow_zero,one_mul,
      Real.mul_rpow (hn a (1+x)) (hn b (1-x))]
    dsimp only [Q]
    rw [add_comm x 1]
    ring

/-- At every strictly sublinear power the realized degrees constitute the
whole interval from 2m onwards. All witnesses may be supported on [−1,1]. -/
theorem sublinear_polynomial_degrees {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : p∈Ioo (0:ℝ) 1) :
    polyharmonicCoefficientDegrees m p=Ici (2*m) := by
  ext d
  constructor
  · exact fun hd => (least_coefficient_degree_at_each_power hm hp.1).2 hd
  · intro hd
    change 2*m≤d at hd
    obtain ⟨P,u,hP,hdeg,_,hu,hpos,h0,hs,he⟩ := sublinear_degree_with_endpoint_factor hm hp (d-2*m)
    obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hu.continuous.continuousOn (s:=Icc (-1:ℝ) 1))
    refine ⟨P,u,hP,by omega,hu,⟨max B 0,?_⟩,hpos,⟨0,h0.trans_ne one_ne_zero⟩,he⟩
    intro x
    by_cases hx : x∈Icc (-1:ℝ) 1
    · exact (hB x hx).trans (le_max_left _ _)
    · simp only [mem_Icc,not_and_or,not_le] at hx
      rw [hs x (hx.imp le_of_lt le_of_lt),abs_zero]
      exact le_max_right _ _

end GaloisForLFunctions.ArithmeticPositiveDuality
