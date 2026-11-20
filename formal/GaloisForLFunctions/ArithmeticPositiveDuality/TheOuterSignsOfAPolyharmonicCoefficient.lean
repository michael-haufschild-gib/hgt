import GaloisForLFunctions.ArithmeticPositiveDuality.DistinctRootsForcedByABoundedPolyharmonicProfile
import GaloisForLFunctions.HTGeometry.GronwallUniqueness
import GaloisForLFunctions.HTGeometry.AccumulationZeros

/-!
# The signs of a polynomial coefficient at both infinities

A bounded nonnegative solution approaches zero along both rays. Starting
at any positive value, successive mean-value arguments give positive
even derivatives on either side. At powers p ≥ 1, uniqueness of a flat
Cauchy jet forbids an interval of zeros. Thus the polynomial multiplying
the even derivative has positive leading sign at both ends.
-/

noncomputable section
open Polynomial Finset Set Filter
open scoped ContDiff Topology
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- A zero jet annihilates the whole solution when the last derivative
is bounded on compact intervals by a multiple of the solution itself. -/
theorem bounded_coefficient_zero_jet {u : ℝ → ℝ} {N : ℕ} (hN : 0<N)
    (hu : ContDiff ℝ (N:ℕ∞ω) u)
    (hcoef : ∀ a b : ℝ, a≤b → ∃ B : ℝ, 0≤B ∧ ∀ x∈Icc a b, |iteratedDeriv N u x|≤B*|u x|)
    {c : ℝ} (hc : ∀ j<N, iteratedDeriv j u c=0) : ∀ x, u x=0 := by
  let Y := fun j => iteratedDeriv j u
  let E := fun x => ∑ j ∈ range N, (Y j x)^2
  let V := fun x => ∑ j ∈ range N, 2*Y j x*Y (j+1) x
  have hE (x : ℝ) : 0≤E x := sum_nonneg fun _ _ => sq_nonneg _
  have component (x : ℝ) (j : ℕ) (hj : j<N) : (Y j x)^2 ≤ E x :=
    single_le_sum (fun i _ => sq_nonneg (Y i x)) (mem_range.mpr hj)
  have dE (x : ℝ) : HasDerivAt E (V x) x := by
    apply HasDerivAt.fun_sum
    intro j hj
    have h := (hu.differentiable_iteratedDeriv j (Nat.cast_lt.mpr (mem_range.mp hj)) x).hasDerivAt
    simpa only [Y,iteratedDeriv_succ (n:=j),Nat.cast_ofNat,show 2-1=1 by decide,pow_one] using h.pow 2
  have hc' : E c=0 := sum_eq_zero fun j hj => by
    rw [show Y j c=0 from hc j (mem_range.mp hj),zero_pow (by decide : 2≠0)]
  have bound (a b : ℝ) (hab : a≤b) : ∃ K : ℝ, ∀ x ∈ Icc a b, |V x|≤K*E x := by
    obtain ⟨B,hB,hb⟩ := hcoef a b hab
    refine ⟨(N:ℝ)*(2*(1+B^2)),?_⟩
    intro x hx
    have hextra := mul_nonneg (sq_nonneg B) (hE x)
    have hi (j : ℕ) (hj : j≤N) : (Y j x)^2 ≤ (1+B^2)*E x := by
      rcases hj.lt_or_eq with h | h
      · linarith only [component x j h,hextra]
      · subst j
        have hs := (sq_le_sq₀ (abs_nonneg (Y N x)) (mul_nonneg hB (abs_nonneg (u x)))).mpr (hb x hx)
        simp only [sq_abs,mul_pow] at hs
        have h0 : (u x)^2≤E x := by simpa only [Y,iteratedDeriv_zero] using component x 0 hN
        linarith only [hs,mul_le_mul_of_nonneg_left h0 (sq_nonneg B),hE x]
    have ht (j : ℕ) (hj : j<N) : |2*Y j x*Y (j+1) x| ≤ 2*(1+B^2)*E x := by
      rw [abs_le]
      constructor
      · nlinarith only [sq_nonneg (Y j x+Y (j+1) x),hi j hj.le,hi (j+1) hj]
      · nlinarith only [sq_nonneg (Y j x-Y (j+1) x),hi j hj.le,hi (j+1) hj]
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum (s:=range N) (fun j hj => ht j (mem_range.mp hj))).trans_eq
    simp only [sum_const,card_range,nsmul_eq_mul,mul_assoc]
  intro x
  have hx : E x=0 := by
    rcases le_total c x with h | h
    · obtain ⟨K,hK⟩ := bound c x h
      exact _root_.HTGeometry.eq_zero_of_nonneg_of_deriv_le_mul h (fun y _ => dE y) (fun y _ => hE y)
        (fun y hy => (abs_le.mp (hK y hy)).2) hc' x (right_mem_Icc.mpr h)
    · obtain ⟨K,hK⟩ := bound x c h
      exact _root_.HTGeometry.eq_zero_of_nonneg_of_neg_mul_le_deriv h (fun y _ => dE y) (fun y _ => hE y)
        (fun y hy => (abs_le.mp (hK y hy)).1) hc' x (left_mem_Icc.mpr h)
  have h : (u x)^2≤0 := by simpa only [Y,iteratedDeriv_zero] using (component x 0 hN).trans_eq hx
  exact sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))

/-- At powers at least one the p-th power of a nonnegative bounded
value is bounded by a constant times that value on each compact interval. -/
theorem nonlinear_polynomial_zero_jet {P : ℝ[X]} {u : ℝ → ℝ} {N : ℕ} (hN : 0<N)
    {p : ℝ} (hp : 1≤p) (hu : ContDiff ℝ (N:ℕ∞ω) u) (hpos : ∀ x, 0≤u x)
    (he : ∀ x, iteratedDeriv N u x=P.eval x*(u x)^p)
    {c : ℝ} (hc : ∀ j<N, iteratedDeriv j u c=0) : ∀ x, u x=0 := by
  apply bounded_coefficient_zero_jet hN hu _ hc
  intro a b _
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (P.continuous.continuousOn (s:=Icc a b))
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hu.continuous.continuousOn (s:=Icc a b))
  refine ⟨|K| * (|M| ^ (p-1)),mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _),?_⟩
  intro x hx
  have hM' : u x≤|M| := (le_abs_self _).trans ((hM x hx).trans (le_abs_self _))
  have hK' : |P.eval x|≤|K| := (hK x hx).trans (le_abs_self _)
  have hr := Real.rpow_le_rpow (hpos x) hM' (sub_nonneg.mpr hp)
  have he' : (u x)^p=(u x)^(p-1)*u x := by
    simpa only [sub_add_cancel,Real.rpow_one] using
      Real.rpow_add_of_nonneg (hpos x) (sub_nonneg.mpr hp) zero_le_one
  rw [he,abs_mul,abs_of_nonneg (Real.rpow_nonneg (hpos _) _),abs_of_nonneg (hpos x),he',←mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hK' hr (Real.rpow_nonneg (hpos x) _) (abs_nonneg _)) (hpos x)

/-- A nontrivial nonnegative profile at p ≥ 1 has a positive value in
every nonempty open interval, even when the coefficient changes sign. -/
theorem nonlinear_polynomial_positive_on_each_interval {P : ℝ[X]} {u : ℝ → ℝ} {N : ℕ}
    (hN : 0<N) {p : ℝ} (hp : 1≤p) (hu : ContDiff ℝ (N:ℕ∞ω) u) (hpos : ∀ x, 0≤u x)
    (hne : ∃ x, u x≠0) (he : ∀ x, iteratedDeriv N u x=P.eval x*(u x)^p)
    {a b : ℝ} (hab : a<b) : ∃ x∈Ioo a b, 0<u x := by
  by_contra! h
  obtain ⟨c,hac,hcb⟩ := exists_between hab
  have hz : u =ᶠ[𝓝 c] (0:ℝ→ℝ) := by
    filter_upwards [Ioo_mem_nhds hac hcb] with y hy
    exact le_antisymm (h y hy) (hpos y)
  have heq := nonlinear_polynomial_zero_jet hN hp hu hpos he (c:=c) fun j _ =>
    (hz.iteratedDeriv_eq j).trans iteratedDeriv_const_zero
  obtain ⟨y,hy⟩ := hne
  exact hy (heq y)

#print axioms bounded_coefficient_zero_jet
#print axioms nonlinear_polynomial_positive_on_each_interval

/-- A nonzero solution has finitely many zeros on every compact set.
Rolle propagation only uses the N derivatives in the equation. -/
theorem nonlinear_polynomial_finite_zeros {P : ℝ[X]} {u : ℝ → ℝ} {N : ℕ}
    (hN : 0<N) {p : ℝ} (hp : 1≤p) (hu : ContDiff ℝ (N:ℕ∞ω) u) (hpos : ∀ x, 0≤u x)
    (hne : ∃ x, u x≠0) (he : ∀ x, iteratedDeriv N u x=P.eval x*(u x)^p)
    {K : Set ℝ} (hK : IsCompact K) : (K ∩ u ⁻¹' {0}).Finite := by
  apply _root_.HTGeometry.finite_of_isolated_in_compact (hK.inter_right (isClosed_singleton.preimage hu.continuous))
  intro c _
  have hn : ¬HTGeometry.AccumZero u c := by
    intro ha
    have hz (j : ℕ) (hj : j≤N) : HTGeometry.AccumZero (iteratedDeriv j u) c := by
      induction j with
      | zero => simpa only [iteratedDeriv_zero] using ha
      | succ j ih =>
        have hprev := ih (by omega)
        have hd := hu.differentiable_iteratedDeriv j (Nat.cast_lt.mpr (show j<N by omega))
        rw [iteratedDeriv_succ]
        exact HTGeometry.accumZero_deriv hd hprev (HTGeometry.eq_zero_of_accumZero hd.continuous hprev)
    obtain ⟨x,hx⟩ := hne
    apply hx
    apply nonlinear_polynomial_zero_jet hN hp hu hpos he (c:=c) _ x
    intro j hj
    exact HTGeometry.eq_zero_of_accumZero (hu.differentiable_iteratedDeriv _ (Nat.cast_lt.mpr hj)).continuous
      (hz j hj.le)
  unfold HTGeometry.AccumZero at hn
  push Not at hn
  obtain ⟨ε,hε,h⟩ := hn
  exact ⟨ε,hε,fun z hz hd => by
    by_contra hne'
    exact h z hne' hd hz.2⟩

/-- At order two a nonnegative solution with any zero already has a
zero Cauchy jet, by the first derivative test at its minimum. -/
theorem second_order_nonlinear_profile_positive {P : ℝ[X]} {u : ℝ → ℝ} {p : ℝ} (hp : 1≤p)
    (hu : ContDiff ℝ 2 u) (hpos : ∀ x, 0≤u x) (hne : ∃ x, u x≠0)
    (he : ∀ x, iteratedDeriv 2 u x=P.eval x*(u x)^p) : ∀ x, 0<u x := by
  intro x
  by_contra! h
  have hx := le_antisymm h (hpos x)
  have hmin : IsLocalMin u x := Eventually.of_forall fun y => hx.le.trans (hpos y)
  obtain ⟨y,hy⟩ := hne
  apply hy
  apply nonlinear_polynomial_zero_jet (N:=2) (by decide) hp hu hpos he (c:=x) _ y
  intro j hj
  rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
  · simpa only [iteratedDeriv_zero] using hx
  · simpa only [iteratedDeriv_one] using hmin.deriv_eq_zero

#print axioms nonlinear_polynomial_finite_zeros
#print axioms second_order_nonlinear_profile_positive

/-- From any positive reading, an even derivative has a positive reading
on both sides. On the right the orientation reverses at each successive
derivative, whereas moving left preserves it. -/
theorem exterior_derivative_readings {u : ℝ → ℝ} {N : ℕ} (hu : ContDiff ℝ (N:ℕ∞ω) u)
    (hb : ∃ M : ℝ, ∀ x, |u x|≤M)
    (hsmall : ∀ A ε : ℝ, 0<ε → (∃ l<A, |u l|<ε) ∧ ∃ r>A, |u r|<ε)
    {c : ℝ} (hc : 0<u c) (k : ℕ) (hk : k≤N) :
    (∃ l≤c, 0 < iteratedDeriv k u l) ∧ ∃ r≥c, 0<(-1:ℝ)^k*iteratedDeriv k u r := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero,pow_zero,one_mul] using
      And.intro (show ∃ l≤c, 0<u l from ⟨c,le_rfl,hc⟩) (show ∃ r≥c, 0<u r from ⟨c,le_rfl,hc⟩)
  | succ k ih =>
    let g := iteratedDeriv k u
    obtain ⟨⟨l,hl,hgl⟩,⟨r,hr,hgr⟩⟩ := ih (by omega)
    have hroot (A ε : ℝ) (hε : 0<ε) : (∃ a<A, |g a|<ε) ∧ ∃ b>A, |g b|<ε := by
      cases k with
      | zero => simpa only [g,iteratedDeriv_zero] using hsmall A ε hε
      | succ j => exact bounded_profile_derivatives_approach_zero hu hb j (by omega) A hε
    have dg := hu.differentiable_iteratedDeriv k (Nat.cast_lt.mpr (show k<N by omega))
    obtain ⟨a,ha,ha'⟩ := (hroot l _ hgl).1
    obtain ⟨b,hb',hb''⟩ := (hroot r _ hgr).2
    obtain ⟨z,hz,hdz⟩ := exists_deriv_eq_slope g ha dg.continuous.continuousOn dg.differentiableOn
    obtain ⟨w,hw,hdw⟩ := exists_deriv_eq_slope g hb' dg.continuous.continuousOn dg.differentiableOn
    refine ⟨⟨z,hz.2.le.trans hl,?_⟩,⟨w,hr.trans hw.1.le,?_⟩⟩
    · rw [iteratedDeriv_succ (n:=k)]
      change 0<deriv g z
      rw [hdz]
      exact div_pos (sub_pos.mpr ((le_abs_self _).trans_lt ha')) (sub_pos.mpr ha)
    · rw [iteratedDeriv_succ (n:=k)]
      change 0<(-1:ℝ)^(k+1)*deriv g w
      rw [hdw,←mul_div_assoc,pow_succ,mul_neg_one]
      apply div_pos _ (sub_pos.mpr hb')
      have hh : (-1:ℝ)^k*g b < (-1:ℝ)^k*g r := by
        apply (le_abs_self _).trans_lt
        simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hb''
      linarith only [hh]

/-- Strictly positive polynomial values arbitrarily far in both
directions force positive leading coefficient and even degree. -/
private theorem polynomial_outer_sign {P : ℝ[X]} (hd : 0<P.degree)
    (hs : ∀ A : ℝ, (∃ x<A, 0<P.eval x) ∧ ∃ x>A, 0<P.eval x) :
    0<P.leadingCoeff ∧ Even P.natDegree := by
  have positive_lead (Q : ℝ[X]) (hdeg : 0<Q.degree) (ht : ∀ A : ℝ, ∃ x>A, 0<Q.eval x) :
      0<Q.leadingCoeff := by
    by_contra! h
    obtain ⟨A,hA⟩ := eventually_atTop.mp ((Q.tendsto_atBot_of_leadingCoeff_nonpos hdeg h).eventually_le_atBot 0)
    obtain ⟨x,hx,hq⟩ := ht A
    exact hq.not_ge (hA x hx.le)
  have h₁ := positive_lead P hd (fun A => (hs A).2)
  have h₂ := positive_lead (P.comp (-X)) (by simpa using hd) (fun A => by
    obtain ⟨x,hx,hp⟩ := (hs (-A)).1
    exact ⟨-x,by linarith only [hx],by simpa using hp⟩)
  rw [comp_neg_X_leadingCoeff_eq] at h₂
  rcases Nat.even_or_odd P.natDegree with he | ho
  · exact ⟨h₁,he⟩
  · rw [ho.neg_one_pow,neg_one_mul] at h₂
    linarith only [h₁,h₂]

private theorem remove_polyharmonic_sign {P : ℝ[X]} {m : ℕ} {u : ℝ → ℝ} {p : ℝ}
    (he : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=P.eval x*(u x)^p) (x : ℝ) :
    iteratedDeriv (2*m) u x=(C ((-1:ℝ)^m)*P).eval x*(u x)^p := by
  have hs : (-1:ℝ)^m*(-1)^m=1 := by rw [←mul_pow]; norm_num
  simp only [eval_mul,eval_C]
  rw [mul_assoc,←he,←mul_assoc,hs,one_mul]

/-- A nontrivial tail on each side forces the sign and parity of the
leading coefficient at every positive power, including sublinear ones. -/
theorem outer_signs_of_persistent_profile {P : ℝ[X]} (hP : P≠0) {u : ℝ → ℝ}
    {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0<p) (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u)
    (hb : ∃ M : ℝ, ∀ x, |u x|≤M) (hpos : ∀ x, 0≤u x)
    (htail : ∀ A : ℝ, (∃ x<A, 0<u x) ∧ ∃ x>A, 0<u x)
    (he : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=P.eval x*(u x)^p) :
    0<(-1:ℝ)^m*P.leadingCoeff ∧ Even P.natDegree := by
  obtain ⟨v,_,hv⟩ := (htail 0).2
  have hne : ∃ x, u x≠0 := ⟨v,hv.ne'⟩
  let s := (-1:ℝ)^m
  let Q := C s*P
  have hs : s≠0 := pow_ne_zero _ (by norm_num)
  have hQ : Q≠0 := mul_ne_zero (C_ne_zero.mpr hs) hP
  have hN : 0<2*m := by omega
  have hNj : 2*m-1+1=2*m := by omega
  have hq := remove_polyharmonic_sign he
  have hsmall := polynomial_ode_small_values_on_both_rays Q hQ (2*m-1) hp
    (by simpa only [hNj] using hu) hb hpos (by simpa only [hNj] using hq)
  have hdegree := polynomial_ode_forces_full_root_count Q hQ (2*m-1) hp
    (by simpa only [hNj] using hu) hb hpos hne (by simpa only [hNj] using hq)
  have hdeg : 0<Q.degree := natDegree_pos_iff_degree_pos.mp (by
    have h := hdegree.trans ((Multiset.toFinset_card_le _).trans Q.card_roots')
    omega)
  have hr (A : ℝ) : (∃ x<A, 0<Q.eval x) ∧ ∃ x>A, 0<Q.eval x := by
    obtain ⟨⟨a,ha,ha'⟩,⟨b,hb',hb''⟩⟩ := htail A
    obtain ⟨l,hl,hl'⟩ := (exterior_derivative_readings hu hb hsmall ha' (2*m) le_rfl).1
    obtain ⟨r,hr,hr'⟩ := (exterior_derivative_readings hu hb hsmall hb'' (2*m) le_rfl).2
    simp only [show (-1:ℝ)^(2*m)=1 by simp,one_mul] at hr'
    have transfer (x : ℝ) (h : 0 < iteratedDeriv (2*m) u x) : 0<Q.eval x := by
      rw [hq] at h
      exact ((mul_pos_iff.mp h).resolve_right (fun h' => (Real.rpow_nonneg (hpos x) p).not_gt h'.2)).1
    exact ⟨⟨l,hl.trans_lt ha,transfer _ hl'⟩,⟨r,hb'.trans_le hr,transfer _ hr'⟩⟩
  simpa only [Q,natDegree_C_mul_of_isUnit hs.isUnit,leadingCoeff_C_mul_of_isUnit hs.isUnit,s] using
    polynomial_outer_sign hdeg hr

/-- An odd degree or a wrong leading sign forces exact extinction on
one ray, even below the uniqueness threshold p = 1. -/
theorem polynomial_wrong_outer_sign_forces_dead_tail {P : ℝ[X]} (hP : P≠0) {u : ℝ → ℝ}
    {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0<p) (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u)
    (hb : ∃ M : ℝ, ∀ x, |u x|≤M) (hpos : ∀ x, 0≤u x)
    (he : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=P.eval x*(u x)^p)
    (hw : ¬(0<(-1:ℝ)^m*P.leadingCoeff ∧ Even P.natDegree)) :
    (∃ A : ℝ, ∀ x<A, u x=0) ∨ ∃ A : ℝ, ∀ x>A, u x=0 := by
  by_cases hl : ∀ A : ℝ, ∃ x<A, 0<u x
  · by_cases hr : ∀ A : ℝ, ∃ x>A, 0<u x
    · exact (hw (outer_signs_of_persistent_profile hP hm hp hu hb hpos (fun A => ⟨hl A,hr A⟩) he)).elim
    · push Not at hr
      obtain ⟨A,hA⟩ := hr
      exact Or.inr ⟨A,fun x hx => le_antisymm (hA x hx) (hpos x)⟩
  · push Not at hl
    obtain ⟨A,hA⟩ := hl
    exact Or.inl ⟨A,fun x hx => le_antisymm (hA x hx) (hpos x)⟩

/-- At powers at least one every bounded nonnegative nonzero profile
requires an even-degree polynomial with the indicated leading sign. -/
theorem superlinear_coefficient_has_even_degree {P : ℝ[X]} (hP : P≠0) {u : ℝ → ℝ}
    {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 1≤p) (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u)
    (hb : ∃ M : ℝ, ∀ x, |u x|≤M) (hpos : ∀ x, 0≤u x) (hne : ∃ x, u x≠0)
    (he : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=P.eval x*(u x)^p) :
    0<(-1:ℝ)^m*P.leadingCoeff ∧ Even P.natDegree := by
  apply outer_signs_of_persistent_profile hP hm (zero_lt_one.trans_le hp) hu hb hpos _ he
  intro A
  have hv {a b : ℝ} (hab : a<b) := nonlinear_polynomial_positive_on_each_interval
    (by omega : 0<2*m) hp hu hpos hne (remove_polyharmonic_sign he) hab
  obtain ⟨a,ha,ha'⟩ := hv (show A-1<A by linarith only)
  obtain ⟨b,hb',hb''⟩ := hv (show A<A+1 by linarith only)
  exact ⟨⟨a,ha.2,ha'⟩,⟨b,hb'.1,hb''⟩⟩

theorem realized_superlinear_degrees_are_even {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 1≤p)
    {d : ℕ} (hd : d ∈ polyharmonicCoefficientDegrees m p) : Even d := by
  obtain ⟨P,u,hP,rfl,hu,hb,hpos,hne,he⟩ := hd
  exact (superlinear_coefficient_has_even_degree hP hm hp hu hb hpos hne he).2

#print axioms exterior_derivative_readings
#print axioms polynomial_wrong_outer_sign_forces_dead_tail
#print axioms superlinear_coefficient_has_even_degree
#print axioms realized_superlinear_degrees_are_even

end GaloisForLFunctions.ArithmeticPositiveDuality
