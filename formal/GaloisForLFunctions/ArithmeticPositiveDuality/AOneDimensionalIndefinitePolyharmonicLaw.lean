import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# A single sign change of a high derivative

Every successive derivative of a bounded profile comes arbitrarily close
to zero on both rays. Consequently a derivative of order at least three
cannot have the sign of a single affine factor unless the profile is
constant. This yields the one-dimensional case of Wei, Xu and Yang,
Theorem 1.1 (arXiv:2611.20600), for general sign-changing coefficients.
-/

noncomputable section
open Set
open scoped ContDiff
namespace GaloisForLFunctions.ArithmeticPositiveDuality

private theorem small_slopes_on_both_rays {g : ℝ → ℝ} (hd : Differentiable ℝ g) {M : ℝ}
    (h : ∀ A : ℝ, (∃ x < A, |g x| ≤ M) ∧ ∃ x > A, |g x| ≤ M)
    (A : ℝ) {ε : ℝ} (hε : 0<ε) :
    (∃ x < A, |deriv g x| < ε) ∧ ∃ x > A, |deriv g x| < ε := by
  let L := (2*|M|+1)/ε
  have hL : 0<L := div_pos (by positivity) hε
  have slope {a b : ℝ} (hab : L<b-a) (ha : |g a| ≤ M) (hb : |g b| ≤ M) :
      ∃ x ∈ Ioo a b, |deriv g x| < ε := by
    have hl : 0<b-a := hL.trans hab
    obtain ⟨x,hx,he⟩ := exists_deriv_eq_slope g (sub_pos.mp hl) hd.continuous.continuousOn hd.differentiableOn
    refine ⟨x,hx,?_⟩
    rw [he,abs_div,abs_of_pos hl,div_lt_iff₀ hl]
    have ht := (div_lt_iff₀ hε).mp hab
    linarith only [abs_sub (g b) (g a),ha,hb,le_abs_self M,ht]
  constructor
  · obtain ⟨b,hb,hgb⟩ := (h A).1
    obtain ⟨a,ha,hga⟩ := (h (b-L)).1
    obtain ⟨x,hx,hv⟩ := slope (show L<b-a by linarith only [ha]) hga hgb
    exact ⟨x,hx.2.trans hb,hv⟩
  · obtain ⟨a,ha,hga⟩ := (h A).2
    obtain ⟨b,hb,hgb⟩ := (h (a+L)).2
    obtain ⟨x,hx,hv⟩ := slope (show L<b-a by linarith only [hb]) hga hgb
    exact ⟨x,ha.trans hx.1,hv⟩

/-- Each positive-order derivative takes arbitrarily small absolute values
on each ray. No bound on any derivative is assumed. -/
theorem bounded_profile_derivatives_approach_zero {f : ℝ → ℝ} {N : ℕ}
    (hf : ContDiff ℝ (N:ℕ∞ω) f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (n : ℕ) (hn : n<N) (A : ℝ) {ε : ℝ} (hε : 0<ε) :
    (∃ x < A, |iteratedDeriv (n+1) f x| < ε) ∧
      ∃ x > A, |iteratedDeriv (n+1) f x| < ε := by
  induction n generalizing A ε with
  | zero =>
    obtain ⟨M,hM⟩ := hb
    rw [iteratedDeriv_one]
    exact small_slopes_on_both_rays (hf.differentiable (by exact_mod_cast hn.ne'))
      (M:=M) (fun B => ⟨⟨B-1,by linarith only,hM _⟩,⟨B+1,by linarith only,hM _⟩⟩) A hε
  | succ k ih =>
    rw [iteratedDeriv_succ]
    apply small_slopes_on_both_rays (hf.differentiable_iteratedDeriv _ (Nat.cast_lt.mpr hn)) (M:=1) _ A hε
    intro B
    obtain ⟨⟨u,hu,hu'⟩,⟨v,hv,hv'⟩⟩ := ih (by omega) B zero_lt_one
    exact ⟨⟨u,hu,hu'.le⟩,⟨v,hv,hv'.le⟩⟩

private theorem constant_of_zero_iterate {f : ℝ → ℝ} {N : ℕ}
    (hf : ContDiff ℝ (N:ℕ∞ω) f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (n : ℕ) (hn : n<N) (hz : ∀ x, iteratedDeriv (n+1) f x=0) : ∀ x, f x=f 0 := by
  induction n with
  | zero =>
    exact fun x => is_const_of_deriv_eq_zero (hf.differentiable (by exact_mod_cast hn.ne'))
      (by simpa only [Nat.zero_add,iteratedDeriv_one] using hz) x 0
  | succ k ih =>
    have hc := is_const_of_deriv_eq_zero (hf.differentiable_iteratedDeriv _ (Nat.cast_lt.mpr hn))
      (by simpa only [iteratedDeriv_succ (n:=k+1)] using hz)
    apply ih (by omega)
    intro x
    by_contra h
    obtain ⟨y,_,hy⟩ := (bounded_profile_derivatives_approach_zero hf hb k (by omega) x (abs_pos.mpr h)).2
    exact hy.ne (congrArg abs (hc y x))

private theorem extend_alternating_readings (g : ℝ → ℝ) (hd : Differentiable ℝ g)
    (n : ℕ) (t : ℕ → ℝ) (ht : ∀ j<n, t j<t (j+1))
    (hs : ∀ j≤n, 0<(-1:ℝ)^j*g (t j))
    (hsmall : ∀ A ε : ℝ, 0<ε → (∃ x<A, |g x|<ε) ∧ ∃ x>A, |g x|<ε) :
    ∃ u : ℕ → ℝ, (∀ j<n+1, u j<u (j+1)) ∧ ∀ j≤n+1, 0<(-1:ℝ)^j*deriv g (u j) := by
  have hstart : 0<g (t 0) := by simpa using hs 0 (Nat.zero_le _)
  have hend : 0 < |g (t n)| := abs_pos.mpr (right_ne_zero_of_mul (hs n le_rfl).ne')
  obtain ⟨l,hl,hgl⟩ := (hsmall (t 0) _ hstart).1
  obtain ⟨r,hr,hgr⟩ := (hsmall (t n) _ hend).2
  let a := fun j : ℕ => if j=0 then l else t (j-1)
  let b := fun j : ℕ => if j≤n then t j else r
  have gap (j : ℕ) (hj : j≤n+1) :
      a j<b j ∧ 0<(-1:ℝ)^j*(g (b j)-g (a j)) := by
    cases j with
    | zero =>
      simp only [a,b,if_pos rfl,if_pos (Nat.zero_le n),pow_zero,one_mul,sub_pos]
      exact ⟨hl,(le_abs_self _).trans_lt hgl⟩
    | succ j =>
      by_cases h : j+1≤n
      · simp only [a,b,if_neg (Nat.succ_ne_zero j),Nat.succ_sub_one,if_pos h]
        refine ⟨ht j (by omega),?_⟩
        have h₁ := hs (j+1) h
        rw [pow_succ] at h₁ ⊢
        linarith only [h₁,hs j (by omega)]
      · have he : j=n := by omega
        subst j
        simp only [a,b,if_neg (Nat.succ_ne_zero n),Nat.succ_sub_one,if_neg h]
        refine ⟨hr,?_⟩
        have habs (z : ℝ) : |(-1:ℝ)^n*z|=|z| := by simp [abs_mul]
        have heq := habs (g (t n))
        rw [abs_of_pos (hs n le_rfl)] at heq
        have hx := (le_abs_self ((-1:ℝ)^n*g r)).trans_lt ((habs (g r)).trans_lt hgr)
        rw [pow_succ]
        linarith only [hx,heq]
  have points (j : ℕ) : ∃ z : ℝ, j≤n+1 →
      z ∈ Ioo (a j) (b j) ∧ 0<(-1:ℝ)^j*deriv g z := by
    by_cases hj : j≤n+1
    · obtain ⟨hab,hv⟩ := gap j hj
      obtain ⟨z,hz,he⟩ := exists_deriv_eq_slope g hab hd.continuous.continuousOn hd.differentiableOn
      refine ⟨z,fun _ => ⟨hz,?_⟩⟩
      rw [he,←mul_div_assoc]
      exact div_pos hv (sub_pos.mpr hab)
    · exact ⟨0,fun h => (hj h).elim⟩
  choose u hu using points
  refine ⟨u,?_,fun j hj => (hu j hj).2⟩
  intro j hj
  have he : b j=a (j+1) := by simp [a,b,show j≤n by omega]
  exact ((hu j hj.le).1.2.trans_eq he).trans (hu (j+1) (by omega)).1.1

/-- One rising secant of a bounded profile forces n+1 ordered, strictly
alternating readings of its (n+1)-st derivative, starting positive. A falling
secant gives the opposite orientation by applying the result to the negative
profile. Only the stated finite number of derivatives is used. -/
theorem ordered_derivative_signs_of_rising_secant {f : ℝ → ℝ} {a b : ℝ}
    (hab : a<b) (hrise : f a<f b) (hb : ∃ M : ℝ, ∀ x, |f x|≤M)
    (n : ℕ) (hf : ContDiff ℝ ((n+1:ℕ):ℕ∞ω) f) :
    ∃ t : ℕ → ℝ, (∀ j<n, t j<t (j+1)) ∧ ∀ j≤n, 0<(-1:ℝ)^j*iteratedDeriv (n+1) f (t j) := by
  induction n with
  | zero =>
    have hd := hf.differentiable (by norm_num)
    obtain ⟨z,_,he⟩ := exists_deriv_eq_slope f hab hd.continuous.continuousOn hd.differentiableOn
    refine ⟨fun _ => z,fun _ h => (Nat.not_lt_zero _ h).elim,?_⟩
    intro j hj
    obtain rfl := Nat.eq_zero_of_le_zero hj
    simpa only [pow_zero,one_mul,Nat.zero_add,iteratedDeriv_one,he] using
      (div_pos (sub_pos.mpr hrise) (sub_pos.mpr hab))
  | succ k ih =>
    obtain ⟨t,ht,hs⟩ := ih (hf.of_le (Nat.cast_le.mpr (Nat.le_succ _)))
    have hd := hf.differentiable_iteratedDeriv (k+1) (Nat.cast_lt.mpr (Nat.lt_succ_self _))
    have h := extend_alternating_readings _ hd k t ht hs (fun A _ hε =>
      bounded_profile_derivatives_approach_zero hf hb k (by omega) A hε)
    simpa only [iteratedDeriv_succ (n:=k+1)] using h

/-- A positive reading bracketed on both rays by arbitrarily small values
forces one more sign than a rising secant alone. The n-th derivative
takes n+1 strictly alternating readings, so it has at least n real zeros. -/
theorem ordered_derivative_signs_of_two_small_tails {f : ℝ → ℝ}
    (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hpos : ∃ x, 0 < f x)
    (hsmall : ∀ A ε : ℝ, 0 < ε → (∃ x < A, |f x| < ε) ∧ ∃ x > A, |f x| < ε)
    (n : ℕ) (hf : ContDiff ℝ (n:ℕ∞ω) f) :
    ∃ t : ℕ → ℝ, (∀ j<n, t j<t (j+1)) ∧ ∀ j≤n, 0<(-1:ℝ)^j*iteratedDeriv n f (t j) := by
  induction n with
  | zero =>
    obtain ⟨x,hx⟩ := hpos
    refine ⟨fun _ => x,fun j h => (Nat.not_lt_zero j h).elim,?_⟩
    intro j hj
    obtain rfl := Nat.eq_zero_of_le_zero hj
    simpa only [iteratedDeriv_zero,pow_zero,one_mul] using hx
  | succ n ih =>
    obtain ⟨t,ht,hs⟩ := ih (hf.of_le (Nat.cast_le.mpr (Nat.le_succ _)))
    have hd := hf.differentiable_iteratedDeriv n (Nat.cast_lt.mpr (Nat.lt_succ_self n))
    have htail (A ε : ℝ) (hε : 0 < ε) :
        (∃ x < A, |iteratedDeriv n f x| < ε) ∧ ∃ x > A, |iteratedDeriv n f x| < ε := by
      cases n with
      | zero => simpa only [iteratedDeriv_zero] using hsmall A ε hε
      | succ k => exact bounded_profile_derivatives_approach_zero hf hb k (by omega) A hε
    simpa only [iteratedDeriv_succ (n:=n)] using
      extend_alternating_readings _ hd n t ht hs htail

/-- If the highest derivative has at most one prescribed switch from
negative to positive, its primitive two orders down is monotone with zero
in the closure of its values at both ends. Bounded profiles are constant. -/
theorem bounded_profile_single_crossing {f : ℝ → ℝ} (n : ℕ) (c : ℝ)
    (hf : ContDiff ℝ ((n+3:ℕ):ℕ∞ω) f) (hb : ∃ M : ℝ, ∀ x, |f x|≤M)
    (hs : ∀ x, 0≤(x-c)*iteratedDeriv (n+3) f x) : ∀ x, f x=f 0 := by
  let g := iteratedDeriv (n+2) f
  let v := iteratedDeriv (n+1) f
  have dg : Differentiable ℝ g := hf.differentiable_iteratedDeriv _ (Nat.cast_lt.mpr (by omega))
  have dv : Differentiable ℝ v := hf.differentiable_iteratedDeriv _ (Nat.cast_lt.mpr (by omega))
  have hleft : AntitoneOn g (Iic c) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic _) dg.continuous.continuousOn dg.differentiableOn
    intro x hx
    rw [interior_Iic] at hx
    change deriv (iteratedDeriv (n+2) f) x ≤ 0
    rw [← iteratedDeriv_succ]
    by_contra! hp
    exact (mul_neg_of_neg_of_pos (sub_neg.mpr hx) hp).not_ge (hs x)
  have hright : MonotoneOn g (Ici c) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) dg.continuous.continuousOn dg.differentiableOn
    intro x hx
    rw [interior_Ici] at hx
    change 0 ≤ deriv (iteratedDeriv (n+2) f) x
    rw [← iteratedDeriv_succ]
    by_contra! hp
    exact (mul_neg_of_pos_of_neg (sub_pos.mpr hx) hp).not_ge (hs x)
  have hnonpos (x : ℝ) : g x≤0 := by
    by_contra! hp
    obtain ⟨⟨l,hl,hgl⟩,⟨r,hr,hgr⟩⟩ :=
      bounded_profile_derivatives_approach_zero hf hb (n+1) (by omega) x hp
    rcases le_total x c with hx | hx
    · exact hgl.not_ge ((hleft (hl.le.trans hx) hx hl.le).trans (le_abs_self _))
    · exact hgr.not_ge ((hright hx (hx.trans hr.le) hr.le).trans (le_abs_self _))
  have hv : Antitone v := antitone_of_deriv_nonpos dv (by
    intro x
    simpa only [v,← iteratedDeriv_succ] using hnonpos x)
  apply constant_of_zero_iterate hf hb n (by omega)
  intro x
  change v x=0
  by_contra he
  obtain ⟨⟨l,hl,hvl⟩,⟨r,hr,hvr⟩⟩ :=
    bounded_profile_derivatives_approach_zero hf hb n (by omega) x (abs_pos.mpr he)
  rcases lt_or_gt_of_ne he with hx | hx
  · have hh : v r ≤ v x := hv hr.le
    change |v r| < |v x| at hvr
    rw [abs_of_neg hx,abs_of_neg (hh.trans_lt hx)] at hvr
    linarith only [hh,hvr]
  · have hh : v x ≤ v l := hv hl.le
    change |v l| < |v x| at hvl
    rw [abs_of_pos hx] at hvl
    exact hvl.not_ge (hh.trans (le_abs_self _))

/-- The one-dimensional indefinite polyharmonic equation has only the
zero bounded nonnegative solution. The coefficient may have any shape
with the same sign crossing, and every positive exponent is allowed. -/
theorem indefinite_polyharmonic_line {u K : ℝ → ℝ} {m : ℕ} (hm : 2 ≤ m) {p c : ℝ} (hp : 0<p)
    (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u) (hb : ∃ M : ℝ, ∀ x, |u x|≤M)
    (hpos : ∀ x, 0≤u x) (hK : ∀ x, 0≤(x-c)*K x) (hne : ∃ x, K x≠0)
    (heq : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=K x*(u x)^p) : ∀ x, u x=0 := by
  let s := (-1:ℝ)^m
  let g := fun x => s*u x
  have hs : |s|=1 := by simp [s]
  have hsn : s≠0 := pow_ne_zero _ (by norm_num)
  let n := 2*m-3
  have hN : n+3=2*m := by dsimp only [n]; omega
  have hg : ContDiff ℝ ((n+3:ℕ):ℕ∞ω) g := by
    rw [hN]
    exact contDiff_const.mul hu
  have hbg : ∃ M : ℝ, ∀ x, |g x|≤M := by
    obtain ⟨M,h⟩ := hb
    exact ⟨M,fun x => by simpa only [g,abs_mul,hs,one_mul] using h x⟩
  have hc := bounded_profile_single_crossing n c hg hbg (fun x => by
    rw [hN,show iteratedDeriv (2*m) g x = s*iteratedDeriv (2*m) u x
      from iteratedDeriv_const_mul_field s u,heq x,←mul_assoc]
    exact mul_nonneg (hK x) (Real.rpow_nonneg (hpos x) p))
  have hu₀ : u = fun _ => u 0 := funext fun x => mul_left_cancel₀ hsn (hc x)
  obtain ⟨x,hx⟩ := hne
  have hz := heq x
  conv_lhs at hz => rw [hu₀]
  rw [iteratedDeriv_const,if_neg (by omega : 2*m≠0),mul_zero] at hz
  have hx₀ := (Real.rpow_eq_zero (hpos x) hp.ne').mp ((mul_eq_zero.mp hz.symm).resolve_left hx)
  exact fun y => (congrFun hu₀ y).trans ((congrFun hu₀ x).symm.trans hx₀)

/-- In particular the coefficient x of Wei, Xu and Yang requires no
boundary data at the origin. -/
theorem linear_weight_polyharmonic_line {u : ℝ → ℝ} {m : ℕ} (hm : 2 ≤ m) {p : ℝ} (hp : 0<p)
    (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u) (hb : ∃ M : ℝ, ∀ x, |u x|≤M)
    (hpos : ∀ x, 0≤u x)
    (heq : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=x*(u x)^p) : ∀ x, u x=0 :=
  indefinite_polyharmonic_line (K:=id) hm hp hu hb hpos (c:=0)
    (fun x => by simpa only [sub_zero,id_eq,←sq] using sq_nonneg x) ⟨1,one_ne_zero⟩ heq

/-- The order restriction for arbitrary sign-changing coefficients is sharp.
The bounded positive profile π + arctan x gives a second-order example at
every real exponent, with a smooth coefficient of strict sign x. -/
theorem second_order_crossing_example (p : ℝ) :
    ∃ u K : ℝ → ℝ, ContDiff ℝ ∞ u ∧ StrictMono u ∧
      (∀ x, 0<u x ∧ u x<2*Real.pi) ∧ ContDiff ℝ ∞ K ∧ K 0=0 ∧
      (∀ x, x≠0 → 0<x*K x) ∧ ∀ x, -iteratedDeriv 2 u x=K x*(u x)^p := by
  let u := fun x => Real.pi+Real.arctan x
  let K := fun x : ℝ => 2*x/((1+x^2)^2*(u x)^p)
  have hu : ContDiff ℝ ∞ u := contDiff_const.add Real.contDiff_arctan
  have hbounds (x : ℝ) : 0<u x ∧ u x<2*Real.pi := by
    dsimp only [u]
    constructor <;> linarith only [Real.pi_pos,Real.neg_pi_div_two_lt_arctan x,Real.arctan_lt_pi_div_two x]
  have hd (x : ℝ) : 0 < (1+x^2)^2*(u x)^p :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos (hbounds x).1 _)
  have h₁ : deriv u=fun x => (1+x^2)⁻¹ :=
    funext fun x => ((Real.hasDerivAt_arctan' x).const_add Real.pi).deriv
  refine ⟨u,K,hu,(fun _ _ h => add_lt_add_of_le_of_lt (le_refl Real.pi) (Real.arctan_strictMono h)),
    hbounds,?_,by simp [K],?_,?_⟩
  · exact (contDiff_const.mul contDiff_id).div
      (((contDiff_const.add (contDiff_id.pow 2)).pow 2).mul
        (hu.rpow_const_of_ne (fun x => (hbounds x).1.ne'))) (fun x => (hd x).ne')
  · intro x hx
    change 0<x*(2*x/((1+x^2)^2*(u x)^p))
    rw [←mul_div_assoc,show x*(2*x)=2*x^2 by ring]
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hx)) (hd x)
  · intro x
    have hj : HasDerivAt (fun y : ℝ => 1+y^2) (2*x) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_add (1:ℝ)
    have hv : deriv (fun y : ℝ => (1+y^2)⁻¹) x=-(2*x)/(1+x^2)^2 :=
      (hj.inv (show 1+x^2≠0 by positivity)).deriv
    rw [iteratedDeriv_succ,iteratedDeriv_one,h₁,hv]
    dsimp only [K]
    field_simp [(Real.rpow_pos_of_pos (hbounds x).1 p).ne']

#print axioms bounded_profile_derivatives_approach_zero
#print axioms ordered_derivative_signs_of_rising_secant
#print axioms ordered_derivative_signs_of_two_small_tails
#print axioms bounded_profile_single_crossing
#print axioms indefinite_polyharmonic_line
#print axioms linear_weight_polyharmonic_line
#print axioms second_order_crossing_example

end GaloisForLFunctions.ArithmeticPositiveDuality
