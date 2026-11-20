import GaloisForLFunctions.ArithmeticPositiveDuality.AOneDimensionalIndefinitePolyharmonicLaw
import GaloisForLFunctions.HTGeometry.SignAlternationHyperbolicity
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# Polynomial coefficients of a bounded polyharmonic profile

A nonzero bounded nonnegative solution of order 2m needs at least 2m
real roots of odd multiplicity in its nonzero polynomial coefficient.
With a nonnegative multiplier, losing one sign change requires the
full coefficient to approach zero along a sequence on one ray.
A Gaussian realizes the polynomial bound at every order.
-/

noncomputable section
open Polynomial Filter
open scoped ContDiff
namespace GaloisForLFunctions.ArithmeticPositiveDuality

private theorem roots_of_rising_profile (P : ℝ[X]) {w f : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    {a b : ℝ} (hab : a < b) (hr : f a < f b) {n : ℕ}
    (hf : ContDiff ℝ ((n+1:ℕ):ℕ∞ω) f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (he : ∀ x, iteratedDeriv (n+1) f x = P.eval x*w x) : n ≤ P.roots.toFinset.card := by
  obtain ⟨t,ht,hs⟩ := ordered_derivative_signs_of_rising_secant hab hr hb n hf
  refine SignAlternation.card_roots_toFinset_ge_of_alternating ht fun j hj => ?_
  have h := hs j hj
  rw [he,←mul_assoc] at h
  exact ((mul_pos_iff.mp h).resolve_right (fun hneg => (hw _).not_gt hneg.2)).1

/-- A nonnegative factor can vanish or vary arbitrarily. Strict readings
of the highest derivative force distinct roots of the polynomial factor. -/
theorem polynomial_roots_or_constant_profile (P : ℝ[X]) {w f : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    {n : ℕ} (hf : ContDiff ℝ ((n+1:ℕ):ℕ∞ω) f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (he : ∀ x, iteratedDeriv (n+1) f x = P.eval x*w x) :
    n ≤ P.roots.toFinset.card ∨ ∀ x, f x=f 0 := by
  by_cases hd : n ≤ P.roots.toFinset.card
  · exact Or.inl hd
  right
  have on_interval {a b : ℝ} (hab : a < b) : f a=f b := by
    rcases lt_trichotomy (f a) (f b) with hr | h | hr
    · exact (hd (roots_of_rising_profile P hw hab hr hf hb he)).elim
    · exact h
    · have hn : ∀ x, iteratedDeriv (n+1) (-f) x=(-P).eval x*w x := by
        intro x
        rw [iteratedDeriv_neg,he,eval_neg,neg_mul]
      have hb' : ∃ M : ℝ, ∀ x, |(-f) x| ≤ M := by simpa only [Pi.neg_apply,abs_neg] using hb
      have hc := roots_of_rising_profile (-P) hw hab (show (-f) a<(-f) b from neg_lt_neg hr)
        hf.neg hb' hn
      exact (hd (by simpa only [roots_neg] using hc)).elim
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · exact on_interval hx
  · rfl
  · exact (on_interval hx).symm

/-- A coefficient with fewer than 2m−1 distinct real roots cannot support
a nonzero bounded nonnegative profile. An extra nonnegative multiplier is
allowed wherever the full coefficient remains nonzero somewhere. -/
theorem roots_or_zero_polyharmonic_profile (P : ℝ[X]) {v u : ℝ → ℝ} (hv : ∀ x, 0 ≤ v x)
    (hcoef : ∃ x, P.eval x*v x ≠ 0) {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0 < p)
    (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u) (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M)
    (hpos : ∀ x, 0 ≤ u x)
    (he : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=(P.eval x*v x)*(u x)^p) :
    2*m-1 ≤ P.roots.toFinset.card ∨ ∀ x, u x=0 := by
  let n := 2*m-1
  have hN : n+1=2*m := by dsimp only [n]; omega
  let s := (-1:ℝ)^m
  let g := fun x => s*u x
  have hs : |s|=1 := by simp [s]
  have hsn : s≠0 := pow_ne_zero _ (by norm_num)
  have hg : ContDiff ℝ ((n+1:ℕ):ℕ∞ω) g := by rw [hN]; exact contDiff_const.mul hu
  have hbg : ∃ M : ℝ, ∀ x, |g x| ≤ M := by
    obtain ⟨M,hM⟩ := hb
    exact ⟨M,fun x => by simpa only [g,abs_mul,hs,one_mul] using hM x⟩
  have hgder (x : ℝ) : iteratedDeriv (n+1) g x=P.eval x*(v x*(u x)^p) := by
    rw [hN,show iteratedDeriv (2*m) g x=s*iteratedDeriv (2*m) u x
      from iteratedDeriv_const_mul_field s u,he,mul_assoc]
  rcases polynomial_roots_or_constant_profile P (fun x => mul_nonneg (hv x) (Real.rpow_nonneg (hpos x) p))
    hg hbg hgder with h | hc
  · exact Or.inl h
  right
  have hu₀ : u=fun _ => u 0 := funext fun x => mul_left_cancel₀ hsn (hc x)
  obtain ⟨x,hx⟩ := hcoef
  have hz := he x
  conv_lhs at hz => rw [hu₀]
  rw [iteratedDeriv_const,if_neg (by omega : 2*m≠0),mul_zero] at hz
  have hux := (Real.rpow_eq_zero (hpos x) hp.ne').mp ((mul_eq_zero.mp hz.symm).resolve_left hx)
  exact fun y => (congrFun hu₀ y).trans ((congrFun hu₀ x).symm.trans hux)

private theorem polynomial_lower_bound_on_rays (P : ℝ[X]) (hP : P ≠ 0) :
    ∃ c > (0:ℝ), ∃ L R : ℝ, (∀ x ≤ L, c ≤ |P.eval x|) ∧ ∀ x ≥ R, c ≤ |P.eval x| := by
  by_cases hd : 0 < P.degree
  · obtain ⟨L,hL⟩ := eventually_atBot.mp ((P.abs_tendsto_atBot hd).eventually (eventually_ge_atTop 1))
    obtain ⟨R,hR⟩ := eventually_atTop.mp ((P.abs_tendsto_atTop hd).eventually (eventually_ge_atTop 1))
    exact ⟨1,zero_lt_one,L,R,hL,hR⟩
  · have hc := eq_C_of_degree_le_zero (le_of_not_gt hd)
    have hn : P.coeff 0 ≠ 0 := fun h => hP (hc.trans (by rw [h,C_0]))
    have he (x : ℝ) : P.eval x=P.coeff 0 := (congrArg (eval x) hc).trans eval_C
    exact ⟨_,abs_pos.mpr hn,0,0,fun x _ => (congrArg abs (he x)).symm.le,
      fun x _ => (congrArg abs (he x)).symm.le⟩

private theorem small_values_of_nondegenerate_tails {K u : ℝ → ℝ} {c L R : ℝ}
    (hc : 0<c) (hL : ∀ x≤L, c≤|K x|) (hR : ∀ x≥R, c≤|K x|)
    (n : ℕ) {p : ℝ} (hp : 0 < p) (hu : ContDiff ℝ ((n+1:ℕ):ℕ∞ω) u)
    (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M) (hpos : ∀ x, 0 ≤ u x)
    (he : ∀ x, iteratedDeriv (n+1) u x=K x*(u x)^p) :
    ∀ A ε : ℝ, 0 < ε → (∃ x < A, |u x| < ε) ∧ ∃ x > A, |u x| < ε := by
  intro A ε hε
  have hd : 0 < c*ε^p := mul_pos hc (Real.rpow_pos_of_pos hε _)
  have transfer {x : ℝ} (hx : c ≤ |K x|) (ht : |iteratedDeriv (n+1) u x| < c*ε^p) :
      |u x| < ε := by
    rw [abs_of_nonneg (hpos x)]
    rw [he,abs_mul,abs_of_nonneg (Real.rpow_nonneg (hpos x) p)] at ht
    by_contra! h
    exact ht.not_ge (mul_le_mul hx (Real.rpow_le_rpow hε.le h hp.le)
      (Real.rpow_nonneg hε.le p) (abs_nonneg _))
  obtain ⟨x,hx,hx'⟩ := (bounded_profile_derivatives_approach_zero hu hb n (by omega) (min A L) hd).1
  obtain ⟨y,hy,hy'⟩ := (bounded_profile_derivatives_approach_zero hu hb n (by omega) (max A R) hd).2
  exact ⟨⟨x,hx.trans_le (min_le_left _ _),transfer (hL x (hx.le.trans (min_le_right _ _))) hx'⟩,
    ⟨y,(le_max_left _ _).trans_lt hy,transfer (hR y ((le_max_right _ _).trans hy.le)) hy'⟩⟩

/-- A nonzero polynomial stays bounded away from zero on both rays.
Small high derivatives therefore force small solution values there. -/
theorem polynomial_ode_small_values_on_both_rays (P : ℝ[X]) (hP : P ≠ 0) {u : ℝ → ℝ}
    (n : ℕ) {p : ℝ} (hp : 0 < p) (hu : ContDiff ℝ ((n+1:ℕ):ℕ∞ω) u)
    (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M) (hpos : ∀ x, 0 ≤ u x)
    (he : ∀ x, iteratedDeriv (n+1) u x=P.eval x*(u x)^p) :
    ∀ A ε : ℝ, 0 < ε → (∃ x < A, |u x| < ε) ∧ ∃ x > A, |u x| < ε := by
  obtain ⟨c,hc,L,R,hL,hR⟩ := polynomial_lower_bound_on_rays P hP
  exact small_values_of_nondegenerate_tails hc hL hR n hp hu hb hpos he

/-- On both rays the polynomial stays away from zero. Small values of the
highest derivative force small values of the solution itself. A positive
reading then gives n+2 ordered alternating readings of its coefficient. -/
theorem polynomial_ode_alternating_coefficient (P : ℝ[X]) (hP : P ≠ 0) {u : ℝ → ℝ}
    (n : ℕ) {p : ℝ} (hp : 0 < p) (hu : ContDiff ℝ ((n+1:ℕ):ℕ∞ω) u)
    (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M) (hpos : ∀ x, 0 ≤ u x) (hne : ∃ x, u x≠0)
    (he : ∀ x, iteratedDeriv (n+1) u x=P.eval x*(u x)^p) :
    ∃ t : ℕ → ℝ, (∀ j<n+1, t j<t (j+1)) ∧ ∀ j≤n+1, 0<(-1:ℝ)^j*P.eval (t j) := by
  have hsmall := polynomial_ode_small_values_on_both_rays P hP n hp hu hb hpos he
  obtain ⟨x,hx⟩ := hne
  obtain ⟨t,ht,hs⟩ := ordered_derivative_signs_of_two_small_tails hb
    ⟨x,lt_of_le_of_ne (hpos x) hx.symm⟩ hsmall (n+1) hu
  refine ⟨t,ht,fun j hj => ?_⟩
  have h := hs j hj
  rw [he,←mul_assoc] at h
  exact ((mul_pos_iff.mp h).resolve_right
    (fun hneg => (Real.rpow_nonneg (hpos _) p).not_gt hneg.2)).1

/-- Each pair of successive alternating readings brackets a distinct root. -/
theorem polynomial_ode_forces_full_root_count (P : ℝ[X]) (hP : P ≠ 0) {u : ℝ → ℝ}
    (n : ℕ) {p : ℝ} (hp : 0 < p) (hu : ContDiff ℝ ((n+1:ℕ):ℕ∞ω) u)
    (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M) (hpos : ∀ x, 0 ≤ u x) (hne : ∃ x, u x≠0)
    (he : ∀ x, iteratedDeriv (n+1) u x=P.eval x*(u x)^p) :
    n+1 ≤ P.roots.toFinset.card := by
  obtain ⟨t,ht,hs⟩ := polynomial_ode_alternating_coefficient P hP n hp hu hb hpos hne he
  exact SignAlternation.card_roots_toFinset_ge_of_alternating ht hs

/-- Only these real roots reverse the sign of the polynomial. -/
def oddRealRoots (P : ℝ[X]) : Finset ℝ :=
  P.roots.toFinset.filter fun x => Odd (P.roots.count x)

private theorem remove_real_square_factors (P : ℝ[X]) (hP : P ≠ 0) :
    ∃ Q S : ℝ[X], P=Q*S^2 ∧ Q.roots.Nodup := by
  generalize he : P.natDegree=k
  induction k using Nat.strong_induction_on generalizing P with
  | h k ih =>
    by_cases hn : P.roots.Nodup
    · exact ⟨P,1,by simp,hn⟩
    rw [Multiset.nodup_iff_count_le_one] at hn
    push Not at hn
    obtain ⟨x,hx⟩ := hn
    obtain ⟨T,hT⟩ := (le_rootMultiplicity_iff hP).mp
      (show 2 ≤ P.rootMultiplicity x by rwa [←P.count_roots])
    have hlin : (X-C x : ℝ[X]) ≠ 0 := X_sub_C_ne_zero x
    have hT₀ : T ≠ 0 := fun hz => hP (hT.trans (by rw [hz,mul_zero]))
    have hd := congrArg natDegree hT
    rw [natDegree_mul (pow_ne_zero _ hlin) hT₀,natDegree_pow,natDegree_X_sub_C,he] at hd
    obtain ⟨Q,S,hqs,hq⟩ := ih T.natDegree (by omega) T hT₀ rfl
    refine ⟨Q,(X-C x)*S,?_,hq⟩
    rw [hT,hqs]
    ring

private theorem factor_with_odd_real_roots (P : ℝ[X]) (hP : P≠0) :
    ∃ Q S : ℝ[X], P=Q*S^2 ∧ Q.roots.toFinset=oddRealRoots P := by
  obtain ⟨Q,S,he,hn⟩ := remove_real_square_factors P hP
  have hQS : Q*S^2 ≠ 0 := he ▸ hP
  have hS : S ≠ 0 := fun h => hQS (by simp [h])
  have hcount (x : ℝ) : P.roots.count x=Q.roots.count x+2*S.roots.count x := by
    rw [he,roots_mul hQS,pow_two,roots_mul (mul_ne_zero hS hS),Multiset.count_add,Multiset.count_add]
    omega
  refine ⟨Q,S,he,?_⟩
  ext x
  simp only [oddRealRoots,Finset.mem_filter,Multiset.mem_toFinset,←Multiset.count_pos,Nat.odd_iff]
  rw [hcount]
  have h := Multiset.nodup_iff_count_le_one.mp hn x
  omega

/-- Opposite strict readings force odd-multiplicity roots. Removing
pairs of equal linear factors preserves all the signs at those readings. -/
theorem odd_real_roots_of_alternating_readings (P : ℝ[X]) (hP : P≠0) {k : ℕ} {t : ℕ → ℝ}
    (ht : ∀ j<k, t j<t (j+1)) (hs : ∀ j≤k, 0 < (-1:ℝ)^j*P.eval (t j)) :
    k ≤ (oddRealRoots P).card := by
  obtain ⟨Q,S,he,hset⟩ := factor_with_odd_real_roots P hP
  rw [←hset]
  refine SignAlternation.card_roots_toFinset_ge_of_alternating ht fun j hj => ?_
  have h := hs j hj
  rw [he,eval_mul,eval_pow,←mul_assoc] at h
  exact ((mul_pos_iff.mp h).resolve_right (fun hz => (sq_nonneg _).not_gt hz.2)).1

/-- In the presence of an arbitrary nonnegative multiplier, a bounded
nonzero profile still requires 2m−1 sign-changing polynomial roots. -/
theorem weighted_odd_roots_or_zero_profile (P : ℝ[X]) {v u : ℝ → ℝ} (hv : ∀ x, 0≤v x)
    (hcoef : ∃ x, P.eval x*v x≠0) {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0<p)
    (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u) (hb : ∃ M : ℝ, ∀ x, |u x|≤M) (hpos : ∀ x, 0≤u x)
    (he : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=(P.eval x*v x)*(u x)^p) :
    2*m-1 ≤ (oddRealRoots P).card ∨ ∀ x, u x=0 := by
  obtain ⟨z,hz⟩ := hcoef
  have hP : P≠0 := fun h => hz (by rw [h,eval_zero,zero_mul])
  obtain ⟨Q,S,hQS,hroots⟩ := factor_with_odd_real_roots P hP
  have hv' (x : ℝ) : 0≤(S.eval x)^2*v x := mul_nonneg (sq_nonneg _) (hv x)
  have hfactor (x : ℝ) : P.eval x*v x=Q.eval x*((S.eval x)^2*v x) := by
    rw [hQS,eval_mul,eval_pow,mul_assoc]
  rw [hfactor] at hz
  rw [←hroots]
  exact roots_or_zero_polyharmonic_profile Q hv' ⟨z,hz⟩ hm hp hu hb hpos
    (fun x => (he x).trans (congrArg (·*(u x)^p) (hfactor x)))

/-- Losing one sign change requires the full coefficient to have arbitrarily
small magnitude arbitrarily far along one fixed ray. This applies even to
discontinuous nonnegative multipliers. -/
theorem deficient_odd_roots_force_small_tail (P : ℝ[X]) (hP : P≠0) {v u : ℝ → ℝ}
    (hv : ∀ x, 0≤v x) (n : ℕ) {p : ℝ} (hp : 0<p) (hu : ContDiff ℝ ((n+1:ℕ):ℕ∞ω) u)
    (hb : ∃ M : ℝ, ∀ x, |u x|≤M) (hpos : ∀ x, 0≤u x) (hne : ∃ x, u x≠0)
    (he : ∀ x, iteratedDeriv (n+1) u x=(P.eval x*v x)*(u x)^p)
    (hr : (oddRealRoots P).card≤n) :
    (∀ A ε : ℝ, 0<ε → ∃ x<A, |P.eval x*v x|<ε) ∨
      ∀ A ε : ℝ, 0<ε → ∃ x>A, |P.eval x*v x|<ε := by
  by_contra! bad
  obtain ⟨⟨L,a,ha,hl⟩,⟨R,b,hb',hr'⟩⟩ := bad
  have hsmall := small_values_of_nondegenerate_tails (lt_min ha hb')
    (L:=L-1) (fun x hx => (min_le_left a b).trans (hl x (by linarith only [hx])))
    (R:=R+1) (fun x hx => (min_le_right a b).trans (hr' x (by linarith only [hx])))
    n hp hu hb hpos he
  obtain ⟨x,hx⟩ := hne
  obtain ⟨t,ht,hs⟩ := ordered_derivative_signs_of_two_small_tails hb
    ⟨x,lt_of_le_of_ne (hpos x) hx.symm⟩ hsmall (n+1) hu
  have hcoeff (j : ℕ) (hj : j≤n+1) : 0<(-1:ℝ)^j*P.eval (t j) := by
    have h := hs j hj
    rw [he,mul_assoc (P.eval _),←mul_assoc] at h
    exact ((mul_pos_iff.mp h).resolve_right (fun hneg =>
      (mul_nonneg (hv _) (Real.rpow_nonneg (hpos _) _)).not_gt hneg.2)).1
  exact (Nat.not_succ_le_self n) ((odd_real_roots_of_alternating_readings P hP ht hcoeff).trans hr)

/-- A bounded nonzero profile requires 2m different sign-changing
real roots, regardless of the number of tangencies of its coefficient. -/
theorem odd_roots_of_polyharmonic_coefficient (P : ℝ[X]) (hP : P ≠ 0) {u : ℝ → ℝ}
    {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0 < p)
    (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u) (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M)
    (hpos : ∀ x, 0 ≤ u x) (hne : ∃ x, u x≠0)
    (he : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=P.eval x*(u x)^p) :
    2*m ≤ (oddRealRoots P).card := by
  have hN : 2*m-1+1=2*m := by omega
  have lift (Q : ℝ[X]) (hQ : Q ≠ 0) (hd : ∀ x, iteratedDeriv (2*m) u x=Q.eval x*(u x)^p) :
      2*m ≤ (oddRealRoots Q).card := by
    obtain ⟨t,ht,hs⟩ := polynomial_ode_alternating_coefficient Q hQ (2*m-1) hp
      (by simpa only [hN] using hu) hb hpos hne (by simpa only [hN] using hd)
    simpa only [hN] using odd_real_roots_of_alternating_readings Q hQ ht hs
  rcases Nat.even_or_odd m with h | h
  · exact lift P hP (by simpa only [h.neg_one_pow,one_mul] using he)
  · have hc := lift (-P) (neg_ne_zero.mpr hP) fun x => by
      simpa only [h.neg_one_pow,neg_one_mul,neg_neg,eval_neg,neg_mul,one_mul] using congrArg Neg.neg (he x)
    simpa only [oddRealRoots,roots_neg] using hc

theorem distinct_roots_of_polyharmonic_coefficient (P : ℝ[X]) (hP : P ≠ 0) {u : ℝ → ℝ}
    {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0 < p)
    (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u) (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M)
    (hpos : ∀ x, 0 ≤ u x) (hne : ∃ x, u x≠0)
    (he : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=P.eval x*(u x)^p) :
    2*m ≤ P.roots.toFinset.card := by
  exact (odd_roots_of_polyharmonic_coefficient P hP hm hp hu hb hpos hne he).trans
    (Finset.card_le_card (Finset.filter_subset _ _))

/-- At degree at most 2m a nonzero solution forces the degree to be
exactly 2m, and every complex root of the coefficient is real and simple. -/
theorem minimal_polyharmonic_coefficient_splits (P : ℝ[X]) (hP : P ≠ 0) {u : ℝ → ℝ}
    {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0 < p)
    (hu : ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u) (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M)
    (hpos : ∀ x, 0 ≤ u x) (hne : ∃ x, u x≠0)
    (he : ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=P.eval x*(u x)^p)
    (hd : P.natDegree ≤ 2*m) :
    P.natDegree=2*m ∧ P.Splits ∧ P.roots.Nodup := by
  have h := distinct_roots_of_polyharmonic_coefficient P hP hm hp hu hb hpos hne he
  have ha := Multiset.toFinset_card_le P.roots
  have hb' := P.card_roots'
  exact ⟨by omega,Polynomial.splits_iff_card_roots.mpr (by omega),
    Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega)⟩

/-- Degrees of nonzero polynomial coefficients realized by a nontrivial
bounded nonnegative solution at the specified order and exponent. -/
def polyharmonicCoefficientDegrees (m : ℕ) (p : ℝ) : Set ℕ :=
  {d | ∃ (P : ℝ[X]) (u : ℝ → ℝ), P ≠ 0 ∧ P.natDegree=d ∧
    ContDiff ℝ ((2*m:ℕ):ℕ∞ω) u ∧ (∃ M : ℝ, ∀ x, |u x| ≤ M) ∧
    (∀ x, 0 ≤ u x) ∧ (∃ x, u x ≠ 0) ∧
    ∀ x, (-1:ℝ)^m*iteratedDeriv (2*m) u x=P.eval x*(u x)^p}

/-- At exponent one the Gaussian attains the minimal degree, with
coefficient equal to the signed 2m-th Hermite polynomial. -/
theorem least_polyharmonic_coefficient_degree {m : ℕ} (hm : 0 < m) :
    IsLeast (polyharmonicCoefficientDegrees m 1) (2*m) := by
  constructor
  · let u := fun x : ℝ => Real.exp (-(x^2/2))
    let P := C ((-1:ℝ)^m)*(hermite (2*m)).map (algebraMap ℤ ℝ)
    have hs : (-1:ℝ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
    have hd : P.natDegree=2*m := by
      dsimp only [P]
      rw [natDegree_C_mul_of_isUnit hs.isUnit,natDegree_map_eq_of_injective
        (FaithfulSMul.algebraMap_injective ℤ ℝ),natDegree_hermite]
    have hP : P ≠ 0 := fun h => (show 2*m≠0 by omega) (by simpa only [h,natDegree_zero] using hd.symm)
    refine ⟨P,u,hP,hd,?_,⟨1,?_⟩,fun x => (Real.exp_pos _).le,
      ⟨0,(Real.exp_pos _).ne'⟩,?_⟩
    · dsimp only [u]
      fun_prop
    · intro x
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    · intro x
      simp only [P,u,iteratedDeriv_eq_iterate,deriv_gaussian_eq_hermite_mul_gaussian,
        eval_mul,eval_C,eval_map_algebraMap,Real.rpow_one,show (-1:ℝ)^(2*m)=1 by simp,one_mul,mul_assoc]
  · rintro d ⟨P,u,hP,rfl,hu,hb,hpos,hne,he⟩
    exact (distinct_roots_of_polyharmonic_coefficient P hP hm zero_lt_one hu hb hpos hne he).trans
      ((Multiset.toFinset_card_le _).trans P.card_roots')

#print axioms polynomial_roots_or_constant_profile
#print axioms roots_or_zero_polyharmonic_profile
#print axioms polynomial_ode_forces_full_root_count
#print axioms distinct_roots_of_polyharmonic_coefficient
#print axioms minimal_polyharmonic_coefficient_splits
#print axioms odd_roots_of_polyharmonic_coefficient
#print axioms weighted_odd_roots_or_zero_profile
#print axioms deficient_odd_roots_force_small_tail
#print axioms least_polyharmonic_coefficient_degree

end GaloisForLFunctions.ArithmeticPositiveDuality
