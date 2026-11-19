import GaloisForLFunctions.SignedArithmeticCorrespondences.ThePoleDefectOfFullIntegralPrefixes

/-!
# The common logarithmic curvature of strided prefixes

After adding half the logarithm to the pole defect, its negative second
difference is a positive moment. Dilation transports its measure beneath
the beta density with a factor equal to the reciprocal stride.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset MeasureTheory _root_.RHTower

private def trap (x : ℝ) : ℝ := (1+x)/2*logMean x-x

private theorem trap_bounds {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ trap x ∧ trap x ≤ (1-x)^2/4 := by
  have ha := mul_le_mul_of_nonneg_left (logMean_le_midpoint hx)
    (show 0 ≤ (1+x)/2 by linarith only [hx.1])
  refine ⟨?_, by dsimp only [trap]; linarith only [ha]⟩
  rcases hx.1.eq_or_lt with h | hp
  · subst x; norm_num [trap,logMean]
  rcases hx.2.eq_or_lt with h | hl
  · subst x; norm_num [trap,logMean]
  have hn := neg_pos.mpr (Real.log_neg hp hl)
  have hs := Real.self_le_sinh_iff.mpr hn.le
  rw [Real.sinh_eq,neg_neg,Real.exp_neg,Real.exp_log hp] at hs
  have hs' := mul_le_mul_of_nonneg_left hs hp.le
  rw [trap,logMean,if_neg hl.ne]
  apply sub_nonneg.mpr
  rw [← mul_div_assoc,le_div_iff₀ hn]
  field_simp [hp.ne'] at hs'
  linarith only [hs']

private theorem trap_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun x => f x * trap x) volume 0 1 := by
  simp only [trap,mul_sub,← mul_assoc]
  exact (integrable_logMean_product (f := fun x => f x*((1+x)/2)) (by fun_prop)).sub
    ((hf.mul continuous_id).intervalIntegrable _ _)

private theorem mean_moment (k : ℕ) :
    (∫ x in (0:ℝ)..1, x^k*logMean x) = Real.log ((k:ℝ)+2)-Real.log ((k:ℝ)+1) := by
  have h := prefixDefectCurvature_moment k
  simp only [mul_sub,mul_one] at h
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x^k) (g := fun x : ℝ => x^k*logMean x)
    (Continuous.intervalIntegrable (by fun_prop) _ _) (integrable_logMean_product (by fun_prop)),
    hilbertMoment_eq_integral_pow,prefix_curvature_entry] at h
  linarith only [h]

private def corrected (k : ℕ) : ℝ := prefixPoleDefect k + Real.log k/2

private theorem corrected_entry (k : ℕ) :
    -(corrected (k+3)-2*corrected (k+2)+corrected (k+1)) = ∫ x in (0:ℝ)..1, x^k*trap x := by
  have he (x : ℝ) : x^k*trap x = (x^k*logMean x+x^(k+1)*logMean x)*(1/2)-x^(k+1) := by
    rw [trap,pow_succ]; ring
  have hi (j : ℕ) := integrable_logMean_product (f := fun x : ℝ => x^j) (by fun_prop)
  simp only [he]
  rw [intervalIntegral.integral_sub (((hi k).add (hi (k+1))).mul_const _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add (hi k) (hi (k+1)),mean_moment,mean_moment,hilbertMoment_eq_integral_pow]
  have h := prefix_curvature_entry (k+1)
  simp only [prefixDefectCurvature,Nat.cast_add,Nat.cast_one] at h
  simp only [corrected,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  rw [show (k:ℝ)+1+1=k+2 by ring,show (k:ℝ)+1+2=k+3 by ring] at *
  linarith only [h]

private theorem telescope (f : ℕ → ℝ) (m r : ℕ) :
    ∑ a ∈ range r, (f (m+a+1)-f (m+a)) = f (m+r)-f m := by
  simpa only [← Nat.add_assoc,Nat.add_zero] using sum_range_sub (fun a => f (m+a)) r

private theorem double_telescope (f : ℕ → ℝ) (m r : ℕ) :
    ∑ a ∈ range r, ∑ b ∈ range r,
      (f (m+a+b+2)-2*f (m+a+b+1)+f (m+a+b)) = f (m+r+r)-2*f (m+r)+f m := by
  let g (j : ℕ) := f (j+1)-f j
  have h (a b : ℕ) : f (m+a+b+2)-2*f (m+a+b+1)+f (m+a+b) =
      g (m+a+b+1)-g (m+a+b) := by dsimp only [g]; ring
  simp only [h]
  rw [sum_congr rfl (fun a _ => telescope g (m+a) r),sum_sub_distrib]
  rw [show (∑ a ∈ range r, g (m+a+r)) = ∑ a ∈ range r, g ((m+r)+a) by
    exact sum_congr rfl fun a _ => by rw [Nat.add_right_comm]]
  change (∑ a ∈ range r, (f (m+r+a+1)-f (m+r+a))) - (∑ a ∈ range r, (f (m+a+1)-f (m+a))) = _
  rw [telescope,telescope]
  ring

private def strideWeight (r : ℕ+) (n : ℕ) (x : ℝ) : ℝ :=
  x^((r:ℕ)*n+((r:ℕ)-1))*(∑ a ∈ range (r:ℕ), x^a)^2

/-- Remainder integrated against a section in the aligned endpoint coordinate. -/
def strideRemainder (r : ℕ+) (n : ℕ) (P : ℝ → ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, (strideWeight r n x * P (x^(r:ℕ))) * trap x

private theorem stride_moment (r : ℕ+) (n : ℕ) :
    -(corrected ((r:ℕ)*(n+3))-2*corrected ((r:ℕ)*(n+2))+corrected ((r:ℕ)*(n+1))) =
      strideRemainder r n (fun _ => 1) := by
  let m := (r:ℕ)*n+((r:ℕ)-1)
  have hm : m+1 = (r:ℕ)*(n+1) := by dsimp only [m]; rw [Nat.mul_succ]; have := r.pos; omega
  have h (a b : ℕ) := corrected_entry (m+a+b)
  have ht := double_telescope (fun j => -corrected (j+1)) m (r:ℕ)
  have he (a b : ℕ) :
      -corrected (m+a+b+2+1)-2*(-corrected (m+a+b+1+1))+(-corrected (m+a+b+1)) =
        ∫ x in (0:ℝ)..1, x^(m+a+b)*trap x := by linarith only [h a b]
  simp only [he] at ht
  have h₂ : m+(r:ℕ)+1 = (r:ℕ)*(n+2) := by rw [Nat.mul_succ,← hm]; omega
  have h₃ : m+(r:ℕ)+(r:ℕ)+1 = (r:ℕ)*(n+3) := by rw [Nat.mul_succ,← h₂]; omega
  rw [hm,h₂,h₃] at ht
  rw [show -(corrected ((r:ℕ)*(n+3))-2*corrected ((r:ℕ)*(n+2))+corrected ((r:ℕ)*(n+1))) =
    -corrected ((r:ℕ)*(n+3))-2*(-corrected ((r:ℕ)*(n+2)))+-corrected ((r:ℕ)*(n+1)) by ring,← ht]
  symm
  have hp (x : ℝ) : (strideWeight r n x*1)*trap x =
      ∑ a ∈ range (r:ℕ), ∑ b ∈ range (r:ℕ), x^(m+a+b)*trap x := by
    rw [strideWeight,sq,sum_mul_sum]
    simp only [mul_sum,sum_mul,pow_add,mul_one]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by dsimp only [m]; rw [pow_add]; ring
  simp only [strideRemainder,hp]
  have hi (a b : ℕ) := trap_integrable (f := fun x : ℝ => x^(m+a+b)) (by fun_prop)
  have hr (a : ℕ) : IntervalIntegrable (fun x : ℝ => ∑ b ∈ range (r:ℕ), x^(m+a+b)*trap x) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact integrable_finsetSum _ fun b _ => (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hi a b)
  rw [intervalIntegral.integral_finsetSum (fun a _ => hr a)]
  exact sum_congr rfl fun a _ => intervalIntegral.integral_finsetSum (fun b _ => hi a b)

/-- Every stride has the same logarithmic term in its second difference. -/
theorem strided_prefix_curvature (r : ℕ+) (n : ℕ) :
    prefixPoleDefect ((r:ℕ)*(n+3))-2*prefixPoleDefect ((r:ℕ)*(n+2))+prefixPoleDefect ((r:ℕ)*(n+1)) =
    -(Real.log ((n:ℝ)+3)-2*Real.log ((n:ℝ)+2)+Real.log ((n:ℝ)+1))/2 -
      strideRemainder r n (fun _ => 1) := by
  have h := stride_moment r n
  have hr : (r:ℝ) ≠ 0 := (Nat.cast_pos.mpr r.pos).ne'
  simp only [corrected,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at h
  rw [Real.log_mul hr (by positivity),Real.log_mul hr (by positivity),Real.log_mul hr (by positivity)] at h
  linarith only [h]

/-- The beta moment on the endpoint coordinate, with two vanishing factors at one. -/
def betaMoment (n : ℕ) (P : ℝ → ℝ) : ℝ := ∫ x in (0:ℝ)..1, x^n*(1-x)^2*P x

private theorem stride_integrable (r : ℕ+) (n : ℕ) {P : ℝ → ℝ} (hP : Continuous P) :
    IntervalIntegrable (fun x => (strideWeight r n x*P (x^(r:ℕ)))*trap x) volume 0 1 :=
  trap_integrable (by unfold strideWeight; fun_prop)

/-- Every nonnegative continuous section pays at most one quarter of its beta
moment divided by the stride. The geometric sum cancels both endpoint factors. -/
theorem strideRemainder_bounds (r : ℕ+) (n : ℕ) {P : ℝ → ℝ} (hP : Continuous P)
    (hp : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ P x) :
    0 ≤ strideRemainder r n P ∧ 4*(r:ℝ)*strideRemainder r n P ≤ betaMoment n P := by
  let F (y : ℝ) := y^n*(1-y)^2*P y
  have hp' (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ P (x^(r:ℕ)) :=
    hp _ ⟨pow_nonneg hx.1 _,pow_le_one₀ hx.1 hx.2⟩
  constructor
  · apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hx.1 _) (sq_nonneg _)) (hp' x hx))
      (trap_bounds hx).1
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := (0:ℝ)) (b := 1)
    (fun x _ => hasDerivAt_pow (r:ℕ) x)
    (show ContinuousOn (fun x : ℝ => (r:ℝ)*x^((r:ℕ)-1)) _ from (by fun_prop : Continuous _).continuousOn)
    (show Continuous F by dsimp [F]; fun_prop)
  simp only [Function.comp_apply,zero_pow r.pos.ne',one_pow] at hsub
  change _ ≤ ∫ x in (0:ℝ)..1, F x
  rw [← hsub,strideRemainder,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one ((stride_integrable r n hP).const_mul _)
    (Continuous.intervalIntegrable (by dsimp [F,Function.comp_def]; fun_prop) _ _)
  intro x hx
  let S := ∑ a ∈ range (r:ℕ), x^a
  have hg : S*(1-x) = 1-x^(r:ℕ) := geom_sum_mul_neg x (r:ℕ)
  have h := mul_le_mul_of_nonneg_left (trap_bounds hx).2 (sq_nonneg S)
  have hz : 4*(S^2*trap x) ≤ (1-x^(r:ℕ))^2 := by rw [← hg]; linarith only [h]
  have ht := mul_le_mul_of_nonneg_left hz (mul_nonneg (mul_nonneg (Nat.cast_nonneg (r:ℕ))
    (pow_nonneg hx.1 ((r:ℕ)*n+((r:ℕ)-1)))) (hp' x hx))
  dsimp only [F,Function.comp_apply,strideWeight]
  dsimp only [S] at ht
  simp only [pow_add,pow_mul] at ht ⊢
  linarith only [ht]

private theorem positive_stride_difference (r s : ℕ+) (n : ℕ) {P : ℝ → ℝ}
    (hP : Continuous P) (hp : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ P x) :
    |4*(strideRemainder r n P-strideRemainder s n P)| ≤ betaMoment n P := by
  have h (d : ℕ+) := strideRemainder_bounds d n hP hp
  have hb (d : ℕ+) : 4*strideRemainder d n P ≤ betaMoment n P := by
    have hd : (1:ℝ) ≤ d := by exact_mod_cast d.pos
    have hm := mul_le_mul_of_nonneg_right hd (h d).1
    linarith only [hm,(h d).2]
  exact abs_le.mpr ⟨by linarith only [(h r).1,hb s],by linarith only [(h s).1,hb r]⟩

/-- Polarizing the difference of two positive remainders gives a uniform
mixed bound by two individually measured beta energies. -/
theorem stride_difference_mixed (r s : ℕ+) (n : ℕ) {U V : ℝ → ℝ}
    (hu : Continuous U) (hv : Continuous V) :
    |strideRemainder r n (fun x => U x*V x)-strideRemainder s n (fun x => U x*V x)| ≤
      (betaMoment n (fun x => U x^2)+betaMoment n (fun x => V x^2))/8 := by
  let P (x : ℝ) := (U x+V x)^2
  let M (x : ℝ) := (U x-V x)^2
  have hp : Continuous P := (hu.add hv).pow 2
  have hm : Continuous M := (hu.sub hv).pow 2
  have pol (d : ℕ+) : strideRemainder d n P-strideRemainder d n M =
      4*strideRemainder d n (fun x => U x*V x) := by
    rw [strideRemainder,strideRemainder,strideRemainder,
      ← intervalIntegral.integral_sub (stride_integrable d n hp) (stride_integrable d n hm),
      ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by dsimp only [P,M]; ring
  have bp : betaMoment n P+betaMoment n M =
      2*(betaMoment n (fun x => U x^2)+betaMoment n (fun x => V x^2)) := by
    have hi (f : ℝ → ℝ) (hf : Continuous f) :
        IntervalIntegrable (fun x : ℝ => x^n*(1-x)^2*f x) volume 0 1 :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    unfold betaMoment
    rw [← intervalIntegral.integral_add (hi P hp) (hi M hm),
      ← intervalIntegral.integral_add (hi (fun x => U x^2) (by fun_prop)) (hi (fun x => V x^2) (by fun_prop)),← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by dsimp only [P,M]; ring
  have h₁ := abs_le.mp (positive_stride_difference r s n hp (fun _ _ => sq_nonneg _))
  have h₂ := abs_le.mp (positive_stride_difference r s n hm (fun _ _ => sq_nonneg _))
  exact abs_le.mpr ⟨by linarith only [pol r,pol s,h₁.1,h₂.2,bp],
    by linarith only [pol r,pol s,h₁.2,h₂.1,bp]⟩

/-- Integer endpoint shifts become monomials in the aligned coordinate. -/
theorem strideRemainder_gluing (r : ℕ+) (n : ℕ) (S T : Finset ℕ) (u v : ℕ → ℝ) :
    ∑ i ∈ S, ∑ j ∈ T, u i*v j*strideRemainder r (n+i+j) (fun _ => 1) =
      strideRemainder r n (fun y => (∑ i ∈ S, u i*y^i)*(∑ j ∈ T, v j*y^j)) := by
  let w (m : ℕ) (x : ℝ) := strideWeight r m x*1*trap x
  have hi (i j : ℕ) : IntervalIntegrable (fun x => (u i*v j)*w (n+i+j) x) volume 0 1 :=
    (stride_integrable r _ continuous_const).const_mul _
  have hr (i : ℕ) : IntervalIntegrable (fun x => ∑ j ∈ T, (u i*v j)*w (n+i+j) x) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact integrable_finsetSum _ fun j _ => (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hi i j)
  have he (x : ℝ) : strideWeight r n x*((∑ i ∈ S, u i*(x^(r:ℕ))^i)*(∑ j ∈ T, v j*(x^(r:ℕ))^j))*trap x =
      ∑ i ∈ S, ∑ j ∈ T, (u i*v j)*w (n+i+j) x := by
    rw [sum_mul_sum]
    simp only [mul_sum,sum_mul]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [w,strideWeight,pow_add,pow_mul,mul_one]
    ring
  unfold strideRemainder
  simp only [he]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hr i)]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => hi i j)]
  exact sum_congr rfl fun j _ => (intervalIntegral.integral_const_mul _ _).symm

#print axioms strided_prefix_curvature
#print axioms strideRemainder_bounds
#print axioms stride_difference_mixed
#print axioms strideRemainder_gluing
end GaloisForLFunctions.SignedArithmeticCorrespondences
