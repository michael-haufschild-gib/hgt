import GaloisForLFunctions.ArithmeticPositiveDuality.ExtremalPolynomialCoefficientsAtEachNonlinearPower
import GaloisForLFunctions.ArithmeticPositiveDuality.TheOuterSignsOfAPolyharmonicCoefficient

/-!
# Realized degrees above the polyharmonic threshold

For every superlinear power, the coefficient degrees are exactly the even
integers at least the order of the equation. A quadratic profile at a
different exponent absorbs any prescribed number of positive quadratic
factors. With a smooth positive bounded multiplier every degree from one
below the order onward occurs, including at the linear exponent.
-/

noncomputable section
open Polynomial Set
open scoped ContDiff
namespace GaloisForLFunctions.ArithmeticPositiveDuality

private theorem positive_quadratic_degree {b : ℝ} (hb : b≠0) :
    (1+C b*X^2 : ℝ[X]).natDegree=2 := by
  have h : (C b*X^2 : ℝ[X]).natDegree=2 := by
    rw [natDegree_C_mul_of_isUnit hb.isUnit,natDegree_X_pow]
  exact (natDegree_add_eq_right_of_natDegree_lt (by rw [natDegree_one,h]; decide)).trans h

/-- Change the exponent of the explicit quadratic profile. Its price
acquires exactly j positive quadratic factors, without introducing a
single new real root at those factors. -/
theorem realize_every_even_superlinear_degree {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 1<p) (j : ℕ) :
    2*m+2*j ∈ polyharmonicCoefficientDegrees m p := by
  let k := 2*m
  have hk : 0<(k:ℝ) := by exact_mod_cast (show 0<k by dsimp only [k]; omega)
  have hk' : 0<(k:ℝ)+j := add_pos_of_pos_of_nonneg hk (Nat.cast_nonneg _)
  let q := 1+(p-1)*(k:ℝ)/((k:ℝ)+j)
  have hq : 1<q := lt_add_of_pos_right _ (div_pos (mul_pos (sub_pos.mpr hp) hk) hk')
  let a := (k:ℝ)/(1-q)
  let u := fun x : ℝ => (max (1+(q-1)*x^2) 0)^a
  let Q := C ((-1:ℝ)^m)*quadraticPowerFactor a (q-1) k
  let B : ℝ[X] := 1+C (q-1)*X^2
  obtain ⟨hQ,hd,hu,hb,hpos,hn,he⟩ := quadratic_profile_at_nonlinear_power hm (zero_lt_one.trans hq) hq.ne'
  change Q≠0 at hQ
  change Q.natDegree=k at hd
  have hB : B.natDegree=2 := positive_quadratic_degree (sub_ne_zero.mpr hq.ne')
  have hB₀ : B≠0 := by intro h; rw [h,natDegree_zero] at hB; contradiction
  have heq : a*q=a*p+j := by
    have hq' : 1-q= -((p-1)*(k:ℝ)/((k:ℝ)+j)) := by dsimp only [q]; ring
    dsimp only [a]
    rw [hq']
    dsimp only [q]
    field_simp [hk.ne',hk'.ne',(sub_pos.mpr hp).ne'] <;> ring
  refine ⟨Q*B^j,u,mul_ne_zero hQ (pow_ne_zero _ hB₀),?_,hu,hb,hpos,hn,?_⟩
  · rw [natDegree_mul hQ (pow_ne_zero _ hB₀),hd,natDegree_pow,hB,Nat.mul_comm j 2]
  · intro x
    let y := 1+(q-1)*x^2
    have hy : 0<y := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (sub_pos.mpr hq).le (sq_nonneg x))
    have hprice : (u x)^q=(u x)^p*(B.eval x)^j := by
      have hval : B.eval x=y := by simp only [B,eval_add,eval_one,eval_mul,eval_C,eval_pow,eval_X,y]
      rw [hval,show u x=y^a by exact congrArg (fun z : ℝ => z^a) (max_eq_left hy.le),
        ←Real.rpow_mul hy.le,heq,Real.rpow_add hy,Real.rpow_natCast,Real.rpow_mul hy.le]
    change (-1:ℝ)^m*iteratedDeriv k u x=_
    rw [show (-1:ℝ)^m*iteratedDeriv k u x=Q.eval x*(u x)^q from he x,hprice,eval_mul,eval_pow]
    ring

theorem superlinear_polynomial_degrees {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 1<p) :
    polyharmonicCoefficientDegrees m p={d | 2*m≤d ∧ Even d} := by
  ext d
  constructor
  · intro hd
    exact ⟨(least_coefficient_degree_at_each_power hm (zero_lt_one.trans hp)).2 hd,
      realized_superlinear_degrees_are_even hm hp.le hd⟩
  · rintro ⟨h,⟨q,hq⟩⟩
    have he : d=2*m+2*(q-m) := by omega
    rw [he]
    exact realize_every_even_superlinear_degree hm hp (q-m)

/-- Dividing the multiplier by a positive quadratic preserves the same
profile and realizes a coefficient two degrees higher. -/
theorem weighted_degree_add_two {m d : ℕ} {p : ℝ} (hd : d ∈ weightedPolyharmonicDegrees m p) :
    d+2 ∈ weightedPolyharmonicDegrees m p := by
  obtain ⟨P,v,u,hP,rfl,hv,hv₁,hu,hb,hpos,hn,he⟩ := hd
  let B : ℝ[X] := 1+C 1*X^2
  have hB : B.natDegree=2 := positive_quadratic_degree one_ne_zero
  have hB₀ : B≠0 := by intro h; rw [h,natDegree_zero] at hB; contradiction
  have hval (x : ℝ) : B.eval x=1+x^2 := by simp [B]
  have h1 (x : ℝ) : 1≤B.eval x := hval x ▸ le_add_of_nonneg_right (sq_nonneg _)
  have h0 (x : ℝ) : 0<B.eval x := zero_lt_one.trans_le (h1 x)
  refine ⟨P*B,fun x => v x/B.eval x,u,mul_ne_zero hP hB₀,by rw [natDegree_mul hP hB₀,hB],
    hv.div (by simp_rw [hval]; fun_prop) (fun x => (h0 x).ne'),?_,hu,hb,hpos,hn,?_⟩
  · intro x
    exact ⟨div_pos (hv₁ x).1 (h0 x),(div_le_one (h0 x)).mpr ((hv₁ x).2.trans (h1 x))⟩
  · intro x
    rw [he,eval_mul]
    field_simp [(h0 x).ne']

/-- Complete weighted classification at all positive powers. The two
starting parities are supplied by the bounded arctangent profile and
the unweighted minimal-degree profile. -/
theorem weighted_polynomial_degrees {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0<p) :
    weightedPolyharmonicDegrees m p=Ici (2*m-1) := by
  have hodd := (least_weighted_coefficient_degree hm hp).1
  have heven : 2*m ∈ weightedPolyharmonicDegrees m p := by
    obtain ⟨P,u,hP,hd,hu,hb,hpos,hn,he⟩ := (least_coefficient_degree_at_each_power hm hp).1
    exact ⟨P,fun _ => 1,u,hP,hd,contDiff_const,fun _ => ⟨zero_lt_one,le_rfl⟩,hu,hb,hpos,hn,
      fun x => by simpa only [mul_one] using he x⟩
  have stride {b : ℕ} (hb : b ∈ weightedPolyharmonicDegrees m p) (j : ℕ) :
      b+2*j ∈ weightedPolyharmonicDegrees m p := by
    induction j with
    | zero => simpa only [Nat.mul_zero,Nat.add_zero] using hb
    | succ j ih => simpa only [Nat.mul_succ,Nat.add_assoc] using weighted_degree_add_two ih
  ext d
  constructor
  · exact fun hd => (least_weighted_coefficient_degree hm hp).2 hd
  · intro hd
    change 2*m-1≤d at hd
    rcases Nat.even_or_odd d with ⟨q,hq⟩ | ⟨q,hq⟩
    · rw [show d=2*m+2*(q-m) by omega]
      exact stride heven _
    · rw [show d=(2*m-1)+2*(q+1-m) by omega]
      exact stride hodd _

#print axioms superlinear_polynomial_degrees
#print axioms weighted_polynomial_degrees

end GaloisForLFunctions.ArithmeticPositiveDuality
