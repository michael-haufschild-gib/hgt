import GaloisForLFunctions.SignedArithmeticCorrespondences.ThePoleDefectOfFullIntegralPrefixes

/-!
# Comparison of the ordinary-prime curvature with the centered real metric

Moving a complete block one step changes its positive intersection measure.
The resulting density lies between two adjacent real-place densities, in the
sense of quadratic forms on signed endpoint sections. Their common residue
polynomial comes from reflecting the two integer indices of a block.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset MeasureTheory _root_.RHTower Set

private def geometric (d : ℕ+) (x : ℝ) : ℝ := ∑ r ∈ range (d:ℕ), x^r

private theorem geometric_difference (d : ℕ+) (x : ℝ) :
    geometric d x*(1-x) = 1-x^(d:ℕ) := geom_sum_mul_neg x _

private theorem density_scaled (d : ℕ+) (n : ℕ) (v : ℝ) :
    let x := Real.exp (-v)
    blockDensity d n ((d:ℝ)*v) = 2*((1-x^(d:ℕ))/((d:ℝ)*v)) *
      x^((d:ℕ)*n+1)*centeredResiduePolynomial d x := by
  intro x
  let m := (d:ℕ)*n+1
  let T := range (d:ℕ)
  have hd : (d:ℝ) ≠ 0 := (Nat.cast_pos.mpr d.pos).ne'
  have ep (k : ℕ) : Real.exp (-(v*k)) = x^k := by
    rw [show -(v*k) = (k:ℝ)*(-v) by ring,Real.exp_nat_mul]
  have hplus (r j : ℕ) :
      Real.exp (-((((n:ℝ)+1)+offset d r j)*((d:ℝ)*v))) = x^m*x^(r+j) := by
    rw [← pow_add,← ep]
    congr 1
    dsimp only [m,offset]
    push_cast
    field_simp
    ring
  have hminus (r j : ℕ) (hr : r∈T) (hj : j∈T) :
      Real.exp (-((((n:ℝ)+1)-offset d r j)*((d:ℝ)*v))) = x^m*x^(((d:ℕ)-1-r)+((d:ℕ)-1-j)) := by
    have hr' : r<(d:ℕ) := mem_range.mp hr
    have hj' : j<(d:ℕ) := mem_range.mp hj
    rw [← pow_add,← ep]
    congr 1
    dsimp only [m,offset]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_sub (by omega : r ≤ (d:ℕ)-1),
      Nat.cast_sub (by omega : j ≤ (d:ℕ)-1),Nat.cast_sub d.pos]
    field_simp
    ring
  have hcenter : Real.exp (-(((n:ℝ)+1)*((d:ℝ)*v))) = x^m*x^((d:ℕ)-1) := by
    rw [← pow_add,← ep]
    congr 1
    simp only [m,Nat.cast_add,Nat.cast_mul,Nat.cast_sub d.pos,Nat.cast_one]
    ring
  have he : Real.exp (-((d:ℝ)*v))=x^(d:ℕ) := by simpa only [mul_comm] using ep (d:ℕ)
  have hun : (∑ r ∈ T, ∑ j ∈ T, x^(r+j)) = geometric d x^2 := by
    rw [sq,geometric,sum_mul_sum]
    simp only [T,pow_add]
  have href : (∑ r ∈ T, ∑ j ∈ T, x^(((d:ℕ)-1-r)+((d:ℕ)-1-j))) = geometric d x^2 := by
    calc _ = ∑ r ∈ T, ∑ j ∈ T, x^(((d:ℕ)-1-r)+j) :=
           sum_congr rfl fun r _ => sum_range_reflect (fun j => x^(((d:ℕ)-1-r)+j)) _
         _ = ∑ r ∈ T, ∑ j ∈ T, x^(r+j) :=
           sum_range_reflect (fun r => ∑ j ∈ T, x^(r+j)) _
         _ = _ := hun
  have hsum : (∑ r ∈ T, ∑ j ∈ T, (Real.exp (-((((n:ℝ)+1)+offset d r j)*((d:ℝ)*v)))+
      Real.exp (-((((n:ℝ)+1)-offset d r j)*((d:ℝ)*v)))-2*Real.exp (-(((n:ℝ)+1)*((d:ℝ)*v))))) =
      2*x^m*centeredResiduePolynomial d x := by
    calc _ = ∑ r ∈ T, ∑ j ∈ T, x^m*(x^(r+j)+x^(((d:ℕ)-1-r)+((d:ℕ)-1-j))-2*x^((d:ℕ)-1)) := by
             refine sum_congr rfl fun r hr => sum_congr rfl fun j hj => ?_
             rw [hplus,hminus r j hr hj,hcenter]
             ring
         _ = _ := by
             simp only [← mul_sum,sum_sub_distrib,sum_add_distrib]
             rw [hun,href]
             simp only [T,sum_const,card_range,nsmul_eq_mul,centeredResiduePolynomial,geometric]
             ring
  rw [blockDensity_offsets,he,hsum]
  ring

private def sectionAt (P : C(Set.Icc (0:ℝ) 1,ℝ)) (x : ℝ) : ℝ :=
  P (Set.projIcc 0 1 zero_le_one x)

private theorem trace_unit (d : ℕ+) (n : ℕ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) :
    sectionIntersection d n P = ∫ x in (0:ℝ)..1,
      (x^((d:ℕ)*n)*geometric d x*centeredResiduePolynomial d x*sectionAt P (x^(d:ℕ)))*logMean x := by
  let F (t : ℝ) := blockDensity d n t*
    P ⟨Real.exp (-|t|),(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))⟩
  have hd : 0<(d:ℝ) := Nat.cast_pos.mpr d.pos
  change (∫ t in Set.Ioi (0:ℝ), F t)/2 = _
  have hscale : (∫ t in Set.Ioi (0:ℝ),F t)/2 =
      ∫ v in Set.Ioi (0:ℝ), (d:ℝ)/2*F ((d:ℝ)*v) := by
    rw [integral_const_mul,integral_comp_mul_left_Ioi F 0 hd,mul_zero,smul_eq_mul]
    field_simp
  rw [hscale,intervalIntegral.integral_of_le zero_le_one,setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  let x := Real.exp (-v)
  have hx0 : 0<x := Real.exp_pos _
  have hx1 : x<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv)
  have hdv := mul_pos hd hv
  have he : Real.exp (-((d:ℝ)*v))=x^(d:ℕ) := by
    rw [show -((d:ℝ)*v)=(d:ℝ)*(-v) by ring,Real.exp_nat_mul]
  have hxpow : x^(d:ℕ)∈Set.Icc (0:ℝ) 1 := ⟨pow_nonneg hx0.le _,pow_le_one₀ hx0.le hx1.le⟩
  have hP : (P ⟨Real.exp (-|((d:ℝ)*v)|),(Real.exp_pos _).le,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))⟩) = sectionAt P (x^(d:ℕ)) := by
    rw [sectionAt,Set.projIcc_of_mem zero_le_one hxpow]
    congr 1
    exact Subtype.ext ((congrArg (fun t : ℝ => Real.exp (-t)) (abs_of_pos hdv)).trans he)
  have hmean : logMean x = (1-x)/v := by
    rw [logMean,if_neg hx1.ne]
    simp only [x,Real.log_exp,neg_neg]
  change (d:ℝ)/2*F ((d:ℝ)*v) =
    x*((x^((d:ℕ)*n)*geometric d x*centeredResiduePolynomial d x*sectionAt P (x^(d:ℕ)))*logMean x)
  dsimp only [F]
  rw [density_scaled,hP,hmean,← geometric_difference d x,pow_succ]
  field_simp
  ring

private def metricDensity (d : ℕ+) (n : ℕ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) (x : ℝ) : ℝ :=
  x^((d:ℕ)*n)*(1-x)*centeredResiduePolynomial d x*(geometric d x)^2*(sectionAt P (x^(d:ℕ)))^2

private theorem metricDensity_continuous (d : ℕ+) (n : ℕ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) :
    Continuous (metricDensity d n P) := by
  have hs : Continuous (sectionAt P) := P.continuous.comp continuous_projIcc
  unfold metricDensity centeredResiduePolynomial geometric
  fun_prop

/-- The real metric tested on one section at a displacement of h. The extra
squared geometric sum runs over both residues in the complete conductor block. -/
def centeredBlockMetric (d : ℕ+) (n h : ℕ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) : ℝ :=
  ∫ x in (0:ℝ)..1, x^h*metricDensity d n P x

/-- Moving the arithmetic block by one step costs between the centered
real-place metrics at two consecutive cuts. Both sides test the full square
of the signed section, so the comparison holds in quadratic-form order. -/
theorem prime_curvature_change_between_real_metrics (d : ℕ+) (n : ℕ) (P : C(Set.Icc (0:ℝ) 1,ℝ)) :
    let K := fun m => sectionIntersection d m (P*P)
    centeredBlockMetric d n 1 P ≤ K n-K (n+1) ∧ K n-K (n+1) ≤ centeredBlockMetric d n 0 P := by
  intro K
  let U (m : ℕ) (x : ℝ) := x^((d:ℕ)*m)*geometric d x*centeredResiduePolynomial d x*
    sectionAt (P*P) (x^(d:ℕ))
  have hu (m : ℕ) : Continuous (U m) := by
    have hs : Continuous (sectionAt (P*P)) := (P*P).continuous.comp continuous_projIcc
    dsimp only [U,geometric,centeredResiduePolynomial]
    fun_prop
  have diff : K n-K (n+1) = ∫ x in (0:ℝ)..1, metricDensity d n P x*logMean x := by
    change sectionIntersection d n (P*P)-sectionIntersection d (n+1) (P*P) = _
    rw [trace_unit,trace_unit]
    rw [← intervalIntegral.integral_sub (f := fun x => U n x*logMean x) (g := fun x => U (n+1) x*logMean x)
      (integrable_logMean_product (hu n)) (integrable_logMean_product (hu (n+1)))]
    apply intervalIntegral.integral_congr
    intro x _
    have hg := geometric_difference d x
    dsimp only [U,metricDensity,sectionAt,ContinuousMap.mul_apply]
    simp only [Nat.mul_add,Nat.mul_one,pow_add]
    calc _ = x^((d:ℕ)*n)*geometric d x*centeredResiduePolynomial d x*
               (P (Set.projIcc 0 1 zero_le_one (x^(d:ℕ))))^2*(1-x^(d:ℕ))*logMean x := by ring
         _ = _ := by rw [← hg]; ring
  have hn (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) : 0 ≤ metricDensity d n P x :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hx.1 _) (sub_nonneg.mpr hx.2))
      (centeredResiduePolynomial_nonneg d hx.1)) (sq_nonneg _)) (sq_nonneg _)
  have hc := metricDensity_continuous d n P
  have hm := integrable_logMean_product hc
  rw [diff]
  constructor
  · unfold centeredBlockMetric
    simp only [pow_one]
    apply intervalIntegral.integral_mono_on zero_le_one ((continuous_id.mul hc).intervalIntegrable _ _) hm
    intro x hx
    change x*metricDensity d n P x ≤ metricDensity d n P x*logMean x
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (logMean_bounds hx).1 (hn x hx)
  · unfold centeredBlockMetric
    simp only [pow_zero,one_mul]
    apply intervalIntegral.integral_mono_on zero_le_one hm (hc.intervalIntegrable _ _)
    exact fun x hx => mul_le_of_le_one_right (hn x hx) (logMean_bounds hx).2

private theorem metric_monomial (d : ℕ+) (m : ℕ) :
    (∫ x in (0:ℝ)..1, x^m*(1-x)*centeredResiduePolynomial d x*(geometric d x)^2) =
      ∑ r ∈ range (d:ℕ), ∑ j ∈ range (d:ℕ), centeredRealEndpoint d (m+r+j) := by
  have he (x : ℝ) : x^m*(1-x)*centeredResiduePolynomial d x*(geometric d x)^2 =
      ∑ r ∈ range (d:ℕ), ∑ j ∈ range (d:ℕ), x^(m+r+j)*(1-x)*centeredResiduePolynomial d x := by
    rw [sq,geometric,sum_mul_sum]
    simp only [mul_sum,pow_add]
    exact sum_congr rfl fun r _ => sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (fun x _ => he x)]
  rw [intervalIntegral.integral_finsetSum (fun r _ => Continuous.intervalIntegrable
    (by unfold centeredResiduePolynomial; fun_prop) _ _)]
  refine sum_congr rfl fun r _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => Continuous.intervalIntegrable
    (by unfold centeredResiduePolynomial; fun_prop) _ _)]
  exact sum_congr rfl fun j _ => (centeredRealEndpoint_moment d (m+r+j)).symm

/-- On genuine endpoint jumps the metric is exactly the sum of the centered
Weil entries, evaluated after all four residue and shift indices are added. -/
theorem centeredBlockMetric_glued (d : ℕ+) (n h : ℕ) (S : Finset ℕ) (u : ℕ → ℝ) :
    centeredBlockMetric d n h (endpointPolynomial S u) =
      ∑ i ∈ S, ∑ j ∈ S, (u i*u j)*∑ r ∈ range (d:ℕ), ∑ s ∈ range (d:ℕ),
        centeredRealEndpoint d ((d:ℕ)*(n+i+j)+h+r+s) := by
  let F (m : ℕ) (x : ℝ) := x^m*(1-x)*centeredResiduePolynomial d x*(geometric d x)^2
  have hF (m : ℕ) : Continuous (F m) := by dsimp [F,geometric,centeredResiduePolynomial]; fun_prop
  unfold centeredBlockMetric
  have he (x : ℝ) (hx : x∈Set.uIcc (0:ℝ) 1) :
      x^h*metricDensity d n (endpointPolynomial S u) x =
      ∑ i ∈ S, ∑ j ∈ S, (u i*u j)*F ((d:ℕ)*(n+i+j)+h) x := by
    rw [Set.uIcc_of_le zero_le_one] at hx
    have hp : x^(d:ℕ)∈Set.Icc (0:ℝ) 1 := ⟨pow_nonneg hx.1 _,pow_le_one₀ hx.1 hx.2⟩
    rw [metricDensity,sectionAt,Set.projIcc_of_mem zero_le_one hp]
    change x^h*(_*(∑ i ∈ S,u i*(x^(d:ℕ))^i)^2) = _
    rw [sq (∑ i ∈ S, _),sum_mul_sum]
    simp only [mul_sum,F,Nat.mul_add,pow_add,pow_mul]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr he]
  rw [intervalIntegral.integral_finsetSum (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul,metric_monomial]

#print axioms prime_curvature_change_between_real_metrics
#print axioms centeredBlockMetric_glued
end GaloisForLFunctions.SignedArithmeticCorrespondences
