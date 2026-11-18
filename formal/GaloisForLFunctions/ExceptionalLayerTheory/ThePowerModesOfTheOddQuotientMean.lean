import GaloisForLFunctions.ExceptionalLayerTheory.TheFiniteOddQuotientMeanOfProperPrimePowers
import GaloisForLFunctions.ExceptionalLayerTheory.TwoProperPowerWavesCharacterizeASingleQuartet
import GaloisForLFunctions.ExceptionalLayerTheory.TheAlternatingPrimeSymbolsAtARightZero
import GaloisForLFunctions.ExceptionalLayerTheory.UniformTailsOfShortDirichletPolynomials

/-!
# Sampling power modes in the odd-quotient first mean

The odd-quotient kernel is a finite sum of triangular weights. Its integral
against a power is the corresponding finite alternating Dirichlet polynomial.
Replacing the continuous power measure by its unit-cell masses costs a
bounded amount throughout the open critical strip.
-/

noncomputable section
open Finset Complex Filter MeasureTheory Topology
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev alt := alternatingDivisorCoeff
private abbrev parity (n : ℕ) : ℝ := (n%2:ℕ)

private theorem parity_bounds (n : ℕ) : 0 ≤ parity n ∧ parity n ≤ 1 :=
  ⟨Nat.cast_nonneg _,by exact_mod_cast (show n%2 ≤ 1 by omega)⟩

private theorem alternating_weight (N : ℕ) (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hdec : ∀ j, w (j+1) ≤ w j) :
    0 ≤ ∑ j ∈ Finset.Icc 1 N, alt j*w j ∧ (∑ j ∈ Finset.Icc 1 N, alt j*w j) ≤ w 1 := by
  have ht : (∑ j ∈ Finset.Icc 1 N, (w j-w (j+1))) = w 1-w (N+1) := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ n+1),ih]
      ring
  have hs := sum_smul_eq_prefix_differences alt w N
  simp only [smul_eq_mul,prefix_alternatingDivisorCoeff] at hs
  have hlast := mul_nonneg (parity_bounds N).1 (hw (N+1))
  have hsum := sum_nonneg (s := Finset.Icc 1 N)
    (fun j _ => mul_nonneg (parity_bounds j).1 (sub_nonneg.mpr (hdec j)))
  have hlast' := mul_le_of_le_one_left (hw (N+1)) (parity_bounds N).2
  have hsum' := sum_le_sum (s := Finset.Icc 1 N)
    (fun j _ => mul_le_of_le_one_left (sub_nonneg.mpr (hdec j)) (parity_bounds j).2)
  rw [ht] at hsum'
  change _ = parity N*w (N+1)+∑ j ∈ Finset.Icc 1 N, parity j*(w j-w (j+1)) at hs
  rw [hs]
  exact ⟨add_nonneg hlast hsum,by linarith only [hlast',hsum']⟩

private def ramp (N : ℕ) (x : ℝ) := ∑ j ∈ Finset.Icc 1 N, alt j*max (x-j) 0

private theorem ramp_incr (N : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ ramp N y-ramp N x ∧ ramp N y-ramp N x ≤ y-x := by
  let w (j : ℕ) := min (y-x) (max (y-j) 0)
  have he (j : ℕ) : max (y-j) 0-max (x-j) 0 = w j := by
    dsimp only [w]
    rcases le_total (j:ℝ) x with h | h
    · rw [max_eq_left (sub_nonneg.mpr (h.trans hxy)),max_eq_left (sub_nonneg.mpr h),
        min_eq_left (by linarith only [h])]
      ring
    · rw [max_eq_right (sub_nonpos.mpr h),sub_zero,min_eq_right (max_le (by linarith only [h]) (sub_nonneg.mpr hxy))]
  have ht := alternating_weight N w (fun j => le_min (sub_nonneg.mpr hxy) (le_max_right _ _))
    (fun j => min_le_min_left _ (max_le_max_right 0 (by push_cast; linarith : y-(↑(j+1):ℝ) ≤ y-j)))
  simp only [ramp,← sum_sub_distrib,← mul_sub,he]
  exact ⟨ht.1,ht.2.trans (min_le_left _ _)⟩

private def tentSum (N : ℕ) (t : ℝ) :=
  ∑ j ∈ Finset.Icc 1 N, alt j*max (1-(j:ℝ)*t/N) 0

private theorem tent_eq_ramp {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    (N:ℝ)*tentSum N t = t*ramp N ((N:ℝ)/t) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  simp only [tentSum,ramp,mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have he : (N:ℝ)*max (1-(j:ℝ)*t/N) 0 = t*max ((N:ℝ)/t-j) 0 := by
    rw [mul_max_of_nonneg _ _ hN'.le,mul_max_of_nonneg _ _ ht.le,mul_zero,mul_zero]
    congr 1
    field_simp
  linear_combination alt j*he

/-- Unit-cell oscillation of the finite odd-quotient kernel. -/
private theorem tent_increment {N : ℕ} (hN : 0 < N) {t d : ℝ} (ht : 0 < t) (hd : t ≤ d) :
    |tentSum N t-tentSum N d| ≤ (d-t)/d := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hdp := ht.trans_le hd
  let x := (N:ℝ)/d
  let y := (N:ℝ)/t
  have hx : 0 ≤ x := div_nonneg hN'.le hdp.le
  have hxy : x ≤ y := div_le_div_of_nonneg_left hN'.le ht hd
  have hR := ramp_incr N hxy
  have hzero : ramp N 0 = 0 := by simp [ramp]
  have hbase := ramp_incr N hx
  rw [hzero,sub_zero,sub_zero] at hbase
  have hid : (N:ℝ)*(tentSum N t-tentSum N d) =
      t*(ramp N y-ramp N x)-(d-t)*ramp N x := by
    rw [mul_sub,tent_eq_ramp hN ht,tent_eq_ramp hN hdp]
    dsimp only [x,y]; ring
  have hstep : t*(y-x) = (d-t)*x := by dsimp only [x,y]; field_simp <;> ring
  have hu := mul_le_mul_of_nonneg_left hR.2 ht.le
  rw [hstep] at hu
  have hl := mul_nonneg ht.le hR.1
  have h₀ := mul_nonneg (sub_nonneg.mpr hd) hbase.1
  have h₁ := mul_le_mul_of_nonneg_left hbase.2 (sub_nonneg.mpr hd)
  have he : |(N:ℝ)*(tentSum N t-tentSum N d)| ≤ (d-t)*x := by
    rw [hid,abs_le]; constructor <;> linarith only [hu,hl,h₀,h₁]
  rw [abs_mul,abs_of_pos hN'] at he
  apply le_of_mul_le_mul_left _ hN'
  exact he.trans_eq (by dsimp only [x]; ring)

private theorem tent_sum_sample {d N : ℕ} (hd : 0 < d) (hn : 0 < N) :
    (N:ℝ)*tentSum N d = discreteQuotientMean parity d N := by
  have hn' : (0:ℝ) < N := by exact_mod_cast hn
  have hcard (j : ℕ) : (∑ k ∈ range N, if j ≤ k/d then (1:ℝ) else 0) =
      (N:ℝ)*max (1-(j:ℝ)*d/N) 0 := by
    have he : (range N).filter (fun k => j ≤ k/d) = Finset.Ico (j*d) N := by
      ext k
      simp only [mem_filter,mem_range,mem_Ico,Nat.le_div_iff_mul_le hd]
      tauto
    rw [← sum_filter,he,sum_const,nsmul_eq_mul,Nat.card_Ico,mul_one,
      mul_max_of_nonneg _ _ hn'.le,mul_zero]
    by_cases hj : j*d ≤ N
    · have hj' : (j:ℝ)*d ≤ N := by exact_mod_cast hj
      rw [Nat.cast_sub hj,Nat.cast_mul,max_eq_left (mul_nonneg hn'.le (sub_nonneg.mpr
        ((div_le_one hn').mpr hj')))]
      field_simp
    · rw [Nat.sub_eq_zero_of_le (lt_of_not_ge hj).le,Nat.cast_zero,max_eq_right]
      exact mul_nonpos_of_nonneg_of_nonpos hn'.le (sub_nonpos.mpr ((one_le_div hn').mpr
        (by exact_mod_cast (le_of_not_ge hj : N ≤ j*d))))
  have hrow (k : ℕ) (hk : k ∈ range N) :
      parity (k/d) = ∑ j ∈ Finset.Icc 1 N, if j ≤ k/d then alt j else 0 := by
    have hc : k/d ≤ N := (Nat.div_le_self ..).trans (mem_range.mp hk).le
    have he : (Finset.Icc 1 N).filter (· ≤ k/d) = Finset.Icc 1 (k/d) := by
      ext j; simp only [mem_filter,mem_Icc]; omega
    rw [← sum_filter,he]
    exact (prefix_alternatingDivisorCoeff (k/d)).symm
  rw [discreteQuotientMean,sum_congr rfl hrow,sum_comm,tentSum,mul_sum]
  apply sum_congr rfl
  intro j _
  have hm : (∑ k ∈ range N, if j ≤ k/d then alt j else 0) =
      alt j*(∑ k ∈ range N, if j ≤ k/d then (1:ℝ) else 0) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _; split <;> simp_all
  rw [hm,hcard]; ring

private def density (s : ℂ) (t : ℝ) : ℂ := s*(t:ℂ)^(s-1)

private theorem int_density {s : ℂ} (hs : 0 < s.re) (a b : ℝ) :
    (∫ t in a..b, density s t) = (b:ℂ)^s-(a:ℂ)^s := by
  have h : -1 < (s-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith only [hs]
  have hne : s ≠ 0 := fun h => by simp [h] at hs
  simp only [density]
  rw [intervalIntegral.integral_const_mul,integral_cpow (Or.inl h),sub_add_cancel]
  field_simp

private theorem integrable_density {s : ℂ} (hs : 0 < s.re) (a b : ℝ) :
    IntervalIntegrable (density s) volume a b :=
  (intervalIntegral.intervalIntegrable_cpow' (r := s-1) (by simp; linarith only [hs])).const_mul s

private theorem cont_tent (N : ℕ) : Continuous (tentSum N) := by
  unfold tentSum
  fun_prop

private def cellError (s : ℂ) (N k : ℕ) : ℂ :=
  ∫ t in (k:ℝ)..(k+1:ℕ), density s t*((tentSum N (k+1:ℕ):ℂ)-tentSum N t)

private theorem cell_error_eq {s : ℂ} (hs : 0 < s.re) (N k : ℕ) :
    cellError s N k = (((k+1:ℕ):ℂ)^s-(k:ℂ)^s)*tentSum N (k+1:ℕ)-
      ∫ t in (k:ℝ)..(k+1:ℕ), density s t*(tentSum N t:ℂ) := by
  have hi := integrable_density hs (k:ℝ) (k+1:ℕ)
  unfold cellError
  simp only [mul_sub]
  rw [intervalIntegral.integral_sub
    (f := fun t => density s t * (tentSum N (k+1:ℕ) : ℂ))
    (g := fun t => density s t * (tentSum N t : ℂ)) (hi.mul_const _)
    (hi.mul_continuousOn (Complex.continuous_ofReal.comp (cont_tent N)).continuousOn),
    intervalIntegral.integral_mul_const,int_density hs]
  simp only [ofReal_natCast]

private theorem point_bound {s : ℂ} {N : ℕ} (hN : 0 < N) {d t : ℝ}
    (ht : 0 < t) (hdt : t ≤ d) :
    ‖density s t*((tentSum N d:ℂ)-tentSum N t)‖ ≤ ‖s‖*t^(s.re-1)*((d-t)/d) := by
  rw [density,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.sub_re,one_re,
    ← ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  exact mul_le_mul_of_nonneg_left (tent_increment hN ht hdt) (by positivity)

private theorem first_cell {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 0 < N) :
    ‖cellError s N 0‖ ≤ ‖s‖/s.re := by
  simp only [cellError,Nat.zero_add,Nat.cast_zero,Nat.cast_one]
  have hh : -1 < s.re-1 := by linarith only [hs]
  apply (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (g := fun t => ‖s‖*t^(s.re-1)) (Eventually.of_forall fun t ht =>
      (point_bound hN ht.1 ht.2).trans (mul_le_of_le_one_right (by positivity)
        (by simpa using ht.1.le : (1-t)/1 ≤ 1))) ((intervalIntegral.intervalIntegrable_rpow' hh).const_mul _)).trans_eq
  rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl hh),sub_add_cancel,Real.one_rpow,
    Real.zero_rpow hs.ne',sub_zero,mul_one_div]

private theorem later_cell {s : ℂ} (hs : s.re < 1) {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k) :
    ‖cellError s N k‖ ≤ ‖s‖*(k:ℝ)^(s.re-2) := by
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hk1 : (k:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast Nat.le_succ k
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := ‖s‖*(k:ℝ)^(s.re-2))
      (fun t ht => ?_)).trans_eq (by push_cast; simp)
  rw [Set.uIoc_of_le hk1] at ht
  have hr := Real.rpow_le_rpow_of_nonpos hk' ht.1.le (sub_nonpos.mpr hs.le)
  have hd : (((k+1:ℕ):ℝ)-t)/((k+1:ℕ):ℝ) ≤ 1/(k:ℝ) := by
    apply (div_le_div_of_nonneg_right _ (hk'.trans_le hk1).le).trans
      (one_div_le_one_div_of_le hk' hk1)
    push_cast
    linarith only [ht.1]
  apply (point_bound hN (hk'.trans ht.1) ht.2).trans
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hr (norm_nonneg _)) hd
    (div_nonneg (sub_nonneg.mpr ht.2) (hk'.le.trans hk1)) (by positivity)).trans_eq
  rw [show s.re-2=(s.re-1)-1 by ring,Real.rpow_sub_one hk'.ne' (s.re-1)]
  ring

/-- Replacing a continuous power density by its exact unit-cell masses
in the normalized first mean costs a bounded amount for every cutoff. -/
private theorem sampled_integral_error {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1)
    {N : ℕ} (hN : 0 < N) :
    ‖(∑ k ∈ range N, (((k+1:ℕ):ℂ)^s-(k:ℂ)^s)*(tentSum N (k+1:ℕ):ℂ))-
      ∫ t in (0:ℝ)..N, density s t*(tentSum N t:ℂ)‖ ≤
      ‖s‖/s.re + ‖s‖*((2-s.re)/(1-s.re)) := by
  have hi := intervalIntegral.sum_integral_adjacent_intervals (n := N) (a := fun k : ℕ => (k:ℝ))
    (f := fun t => density s t*(tentSum N t:ℂ))
    (fun k _ => (integrable_density hs _ _).mul_continuousOn
      (Complex.continuous_ofReal.comp (cont_tent N)).continuousOn)
  simp only [Nat.cast_zero] at hi
  rw [← hi,← sum_sub_distrib]
  simp_rw [← cell_error_eq hs]
  apply (norm_sum_le _ _).trans
  rw [← Nat.Ico_zero_eq_range,← sum_Ico_consecutive _ (show 0 ≤ 1 by decide) hN]
  simp only [Nat.Ico_zero_eq_range,range_one,sum_singleton]
  apply add_le_add (first_cell hs hN)
  apply (sum_le_sum fun k (hk : k ∈ Finset.Ico 1 N) => later_cell hs' hN (mem_Ico.mp hk).1).trans
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have htail := Sieve.sum_rpow_neg_tail_le (c := 2-s.re) (N := N)
    (by linarith only [hs']) (R := 1) (by decide)
  simp only [Nat.cast_one,Real.one_rpow,mul_one,show -(2-s.re)=s.re-2 by ring,
    show 2-s.re-1=1-s.re by ring] at htail
  apply le_trans _ htail
  exact sum_le_sum_of_subset_of_nonneg (fun k hk => mem_Icc.mpr ⟨(mem_Ico.mp hk).1,(mem_Ico.mp hk).2.le⟩)
    (fun k _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

private def tent (j N : ℕ) (t : ℝ) : ℂ := (max (1-(j:ℝ)*t/N) 0 : ℝ)

private theorem int_tent {s : ℂ} (hs : 0 < s.re) {j N : ℕ} (hj : 1 ≤ j) (hN : 0 < N) :
    (∫ t in (0:ℝ)..N, density s t * tent j N t) =
      (N:ℂ)^s/((j:ℂ)^s*(s+1)) := by
  let x := (N:ℝ)/j
  have hp : (0:ℝ)<N := by exact_mod_cast hN
  have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hj0 := zero_lt_one.trans_le hj'
  have hxp : 0 < x := div_pos hp hj0
  have hxN : x ≤ N := div_le_self hp.le hj'
  have hxe : x*j=N := div_mul_cancel₀ _ hj0.ne'
  have hxC : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hxp.ne'
  have hsC : s ≠ 0 := fun h => by simp [h] at hs
  have hsp : s+1 ≠ 0 := by
    intro h
    have e := congrArg re h
    simp only [add_re,one_re,zero_re] at e
    linarith only [e,hs]
  have hcont : Continuous (tent j N) := by unfold tent; fun_prop
  have hi (a b : ℝ) := (integrable_density hs a b).mul_continuousOn hcont.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 x) (hi x N)]
  have hzero : (∫ t in x..N, density s t*tent j N t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with t ht
    rw [Set.uIoc_of_le hxN] at ht
    have hh : (N:ℝ) ≤ j*t := by
      rw [← hxe,mul_comm (j:ℝ)]
      exact mul_le_mul_of_nonneg_right ht.1.le hj0.le
    simp [tent,max_eq_right (sub_nonpos.mpr ((one_le_div hp).mpr hh))]
  rw [hzero,add_zero]
  have he : (∫ t in (0:ℝ)..x, density s t*tent j N t) =
      ∫ t in (0:ℝ)..x, density s t - (s/(x:ℂ))*(t:ℂ)^s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [Set.uIoc_of_le hxp.le] at ht
    have hh : (j:ℝ)*t ≤ N := by
      rw [← hxe,mul_comm (j:ℝ)]
      exact mul_le_mul_of_nonneg_right ht.2 hj0.le
    have htC : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have hpow : (t:ℂ)^s = (t:ℂ)^(s-1)*(t:ℂ) := by
      simpa only [sub_add_cancel,Complex.cpow_one] using Complex.cpow_add (s-1) 1 htC
    have hex : (j:ℝ)*t/N=t/x := by dsimp only [x]; field_simp
    rw [density,tent,max_eq_left (sub_nonneg.mpr ((div_le_one hp).mpr hh)),hex,ofReal_sub,
      ofReal_one,ofReal_div,hpow]
    ring
  have hr : -1<s.re := by linarith only [hs]
  rw [he,intervalIntegral.integral_sub (integrable_density hs _ _)
    ((intervalIntegral.intervalIntegrable_cpow' hr).const_mul _),int_density hs,
    intervalIntegral.integral_const_mul,integral_cpow (Or.inl hr)]
  simp only [ofReal_zero,Complex.zero_cpow hsC,Complex.zero_cpow hsp,sub_zero]
  rw [Complex.cpow_add s 1 hxC,Complex.cpow_one]
  have hnC : (N:ℂ)^s=(x:ℂ)^s*(j:ℂ)^s := by
    simpa only [← ofReal_mul,hxe,ofReal_natCast] using Complex.mul_cpow_ofReal_nonneg hxp.le hj0.le s
  rw [hnC]
  have hjC : (j:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (by omega)))
  field_simp
  <;> ring

private theorem integral_as_polynomial {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 0 < N) :
    (∫ t in (0:ℝ)..N, density s t*(tentSum N t:ℂ)) =
      (N:ℂ)^s*shortDirichletPrefix (alternatingRowCoeffs alt) N s/(s+1) := by
  let v (j : ℕ) (t : ℝ) := (alt j:ℂ)*(density s t*tent j N t)
  have he (t : ℝ) : density s t*(tentSum N t:ℂ)=∑ j ∈ Finset.Icc 1 N, v j t := by
    simp only [tentSum,ofReal_sum,ofReal_mul,mul_sum,v,tent]
    exact sum_congr rfl fun _ _ => by ring
  have hi (j : ℕ) : IntervalIntegrable (v j) volume 0 N := by
    have h : Continuous (tent j N) := by unfold tent; fun_prop
    exact ((integrable_density hs 0 N).mul_continuousOn h.continuousOn).const_mul _
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun j _ => hi j)]
  have hpre : shortDirichletPrefix (alternatingRowCoeffs alt) N s =
      ∑ j ∈ Finset.Icc 1 N, ((alt j:ℂ)/(j:ℂ)^s) := by
    rw [shortDirichletPrefix,← Nat.Ico_zero_eq_range,← sum_Ico_consecutive _ (by decide : 0 ≤ 1)
      (Nat.succ_pos N),Nat.Ico_zero_eq_range,range_one,sum_singleton,Ico_add_one_right_eq_Icc]
    simp only [LSeries.term_zero,zero_add]
    exact sum_congr rfl fun j hj => if_neg (Nat.ne_of_gt (mem_Icc.mp hj).1)
  rw [hpre,mul_sum,sum_div]
  refine sum_congr rfl fun j hj => ?_
  dsimp only [v]
  rw [intervalIntegral.integral_const_mul,int_tent hs (mem_Icc.mp hj).1 hN]
  ring

/-- The alternating symbol has its dyadic zeta expression throughout the open strip. -/
theorem paritySymbol_eq_dyadic_zeta {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    paritySymbol s=alternatingDivisorFactor s*riemannZeta s := by
  have ha := fun x hx => (alternatingRow_growth x hx).1
  have hc : alternatingRowCoeffs alt 0=0 := by simp [alternatingRowCoeffs]
  have hA := HeckeLFunctions.differentiableOn_growthCont hc (le_refl 0) ha
  apply HTGeometry.eq_of_eq_on_one_lt_re (c := 0) (by norm_num) _ _ _ hs
    (fun h => by simp [h] at hs')
  · intro z hz _
    exact hA.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds hz)
  · intro z _ hz
    have hp : Differentiable ℂ (fun w : ℂ => (2:ℂ)^(-w)) :=
      differentiable_neg.const_cpow (Or.inl (by norm_num))
    exact (differentiableAt_const.sub (differentiableAt_const.mul (hp z))).mul (differentiableAt_riemannZeta hz)
  · intro z hz
    exact (alternatingSymbols_eq (by linarith only [hz]) (fun h => by simpa [h] using hz)).1

/-- The unit-cell power masses acquire the triangular alternating multiplier
eta(s)/(s+1), with a bounded error uniform in the positive integer cutoff. -/
theorem oddQuotientMean_power_mode {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    ∃ C : ℝ, ∀ N : ℕ, 0 < N →
      ‖(∑ k ∈ range N, (((k+1:ℕ):ℂ)^s-(k:ℂ)^s)*
        (discreteQuotientMean parity (k+1) N:ℂ)/(N:ℂ))-
        (N:ℂ)^s*(alternatingDivisorFactor s*riemannZeta s)/(s+1)‖ ≤ C := by
  let B := 2^‖s‖*(2+‖s‖*(1+1/s.re))
  refine ⟨‖s‖/s.re + ‖s‖*((2-s.re)/(1-s.re)) + B/‖s+1‖,fun N hN => ?_⟩
  have hp : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsam (k : ℕ) : (((k+1:ℕ):ℂ)^s-(k:ℂ)^s)*(discreteQuotientMean parity (k+1) N:ℂ)/(N:ℂ) =
      (((k+1:ℕ):ℂ)^s-(k:ℂ)^s)*(tentSum N (k+1:ℕ):ℂ) := by
    rw [← tent_sum_sample (Nat.succ_pos k) hN,ofReal_mul,ofReal_natCast]
    field_simp
  simp_rw [hsam]
  let P := shortDirichletPrefix (alternatingRowCoeffs alt) N s
  have h := sampled_integral_error hs hs' hN
  rw [integral_as_polynomial hs hN] at h
  rw [← paritySymbol_eq_dyadic_zeta hs hs']
  have ht := norm_scaled_growthCont_sub_shortDirichletPrefix (c := alternatingRowCoeffs alt)
    (by simp [alternatingRowCoeffs]) (θ := 0) (K := 1) le_rfl zero_le_one
    (fun x hx => (alternatingRow_growth x hx).1) hs (by simpa : 0+s.re ≤ s.re) le_rfl hp
  have htail : ‖(N:ℂ)^s*(paritySymbol s-P)‖ ≤ B := by
    simpa only [Nat.floor_natCast,ofReal_natCast,Real.rpow_zero,mul_one,P,B,paritySymbol] using ht
  have he : ‖(N:ℂ)^s*P/(s+1)-(N:ℂ)^s*paritySymbol s/(s+1)‖ ≤ B/‖s+1‖ := by
    rw [norm_sub_rev,← sub_div,← mul_sub,norm_div]
    exact div_le_div_of_nonneg_right htail (norm_nonneg _)
  exact (norm_sub_le_norm_sub_add_norm_sub _ ((N:ℂ)^s*P/(s+1)) _).trans (add_le_add h he)

private abbrev quarterError (x : ℝ) := x^(1/4:ℝ)*(1+Real.log x)^2

private theorem one_le_quarterError {x : ℝ} (hx : 1 ≤ x) : 1 ≤ quarterError x :=
  one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hx (by norm_num))
    (one_le_pow₀ (le_add_of_nonneg_right (Real.log_nonneg hx)))

private theorem transfer_quarterError (c : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ n : ℕ, 1 ≤ n → |∑ d ∈ Finset.Icc 1 n, c d| ≤ K*quarterError n)
    {N : ℕ} (hN : 1 ≤ N) :
    |(∑ d ∈ Finset.Icc 1 N, c d * discreteQuotientMean parity d N)/(N:ℝ)| ≤ 4*K*quarterError N := by
  have hpos : (0:ℝ)<N := by exact_mod_cast hN
  rw [abs_div,abs_of_pos hpos,div_le_iff₀ hpos]
  apply (abs_discreteQuotientMean_weighted c parity (by norm_num [parity]) parity_bounds N).trans
  let L := (1+Real.log N)^2
  have hu (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      |∑ d ∈ Finset.Icc 1 n, c d|/((n:ℝ)+1) ≤ (K*L)*(n:ℝ)^(-(3/4:ℝ)) := by
    have hp : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnpos := zero_lt_one.trans_le hp
    have hh : (1+Real.log n)^2 ≤ L := by
      apply (sq_le_sq₀ (by linarith only [Real.log_nonneg hp])
        (by have := Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN); linarith)).mpr
      exact add_le_add (le_refl 1) (Real.log_le_log hnpos (by exact_mod_cast (mem_Icc.mp hn).2))
    have he := mul_le_mul_of_nonneg_left hh (mul_nonneg hK (Real.rpow_nonneg hnpos.le (1/4)))
    have hb := h n (mem_Icc.mp hn).1
    apply (div_le_div_of_nonneg_left (abs_nonneg _) hnpos (le_add_of_nonneg_right zero_le_one)).trans
    rw [show -(3/4:ℝ)=(1/4:ℝ)-1 by norm_num,Real.rpow_sub_one hnpos.ne',← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hnpos.le
    dsimp only [quarterError] at hb
    linarith only [he,hb]
  have hsum := Finset.sum_le_sum hu
  rw [← mul_sum] at hsum
  have hr : (∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(-(3/4:ℝ))) ≤ (N:ℝ)^(1/4:ℝ)/(1/4) := by
    rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
    have hh := _root_.RHTower.sum_range_rpow_neg_le (3/4) (by norm_num) (by norm_num) N
    simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ),
      show 1-(3/4:ℝ)=1/4 by norm_num] using hh
  have hl : 0 ≤ L := sq_nonneg _
  have hb := mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hr (mul_nonneg hK hl))) hpos.le
  exact hb.trans_eq (by dsimp only [L,quarterError]; ring)

private def modePrefix (ρ s : ℂ) (n : ℕ) := ((n:ℂ)^s/ρ).re
private def modeJump (ρ s : ℂ) (n : ℕ) := modePrefix ρ s n - modePrefix ρ s (n-1)

private theorem prefix_modeJump (ρ : ℂ) {s : ℂ} (hs : 0<s.re) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, modeJump ρ s k)=modePrefix ρ s n := by
  induction n with
  | zero =>
    have h : s ≠ 0 := fun e => by simpa [e] using hs
    simp [modePrefix,Complex.zero_cpow h]
  | succ n ih => rw [sum_Icc_succ_top (by omega : 1 ≤ n+1),ih,modeJump,Nat.add_sub_cancel]; ring

/-- Real power wave divided by ρ after the alternating triangular mean. -/
def oddQuotientEtaMode (ρ s : ℂ) (N : ℕ) : ℝ :=
  (((N:ℂ)^s*(alternatingDivisorFactor s*riemannZeta s)/(s+1))/ρ).re

private theorem modeJump_transfer (ρ : ℂ) {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ k ∈ Finset.Icc 1 N, modeJump ρ s k*discreteQuotientMean parity k N)/(N:ℝ)-
        oddQuotientEtaMode ρ s N| ≤ C := by
  obtain ⟨C,h⟩ := oddQuotientMean_power_mode hs hs'
  refine ⟨|C|/‖ρ‖,div_nonneg (abs_nonneg _) (norm_nonneg _),fun N hN => ?_⟩
  let S := ∑ k ∈ range N, (((k+1:ℕ):ℂ)^s-(k:ℂ)^s)*(discreteQuotientMean parity (k+1) N:ℂ)/(N:ℂ)
  let T := (N:ℂ)^s*(alternatingDivisorFactor s*riemannZeta s)/(s+1)
  have he : (∑ k ∈ Finset.Icc 1 N, modeJump ρ s k*discreteQuotientMean parity k N)/(N:ℝ)=(S/ρ).re := by
    rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range,Nat.add_sub_cancel,Finset.sum_div]
    dsimp only [S]
    rw [Finset.sum_div,Complex.re_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [add_comm 1 k,modeJump,Nat.add_sub_cancel,modePrefix,modePrefix,← Complex.sub_re,
      ← sub_div,← Complex.re_mul_ofReal,← Complex.div_ofReal_re]
    congr 1
    push_cast; ring
  rw [he,oddQuotientEtaMode,← Complex.sub_re,← sub_div]
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_div]
  exact div_le_div_of_nonneg_right ((h N hN).trans (le_abs_self _)) (norm_nonneg _)

/-- Both genuine power waves of a single quartet pass to the normalized
finite prime count, with the alternating zeta multiplier at each frequency. -/
theorem oddQuotientPowerTotal_singleQuartet_modes {ρ : ℂ} (hq : ExclusionOfTheCriticalState.HasSingleOffLineQuartet ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |oddQuotientPowerTotal N/(N:ℝ) + 2*(ExclusionOfTheCriticalState.quartetCopyMult ρ:ℝ)*
        (oddQuotientEtaMode ρ (ρ/2) N+oddQuotientEtaMode ρ (ρ/3) N)| ≤ C*quarterError N := by
  let s₂ := ρ/2
  let s₃ := ρ/3
  let m := 2*(ExclusionOfTheCriticalState.quartetCopyMult ρ:ℝ)
  have hm : 0 ≤ m := by dsimp only [m]; positivity
  have h₂ : 0<s₂.re ∧ s₂.re<1 := by dsimp only [s₂]; rw [Complex.div_ofNat_re]; constructor <;> linarith only [hq.1,hq.re_lt_one]
  have h₃ : 0<s₃.re ∧ s₃.re<1 := by dsimp only [s₃]; rw [Complex.div_ofNat_re]; constructor <;> linarith only [hq.1,hq.re_lt_one]
  let c (n : ℕ) := properPowerLatticeWeight n+m*(modeJump ρ s₂ n+modeJump ρ s₃ n)
  obtain ⟨K,hK,h⟩ := singleQuartet_properPower_modes hq
  have hp (n : ℕ) (hn : 1 ≤ n) : |∑ d ∈ Finset.Icc 1 n, c d| ≤ (K+2)*quarterError n := by
    have h₁ : (1:ℝ) ≤ n := by exact_mod_cast hn
    have he := h n h₁
    have hf := properPowerLatticeWeight_prefix n
    simp only [Complex.add_re,ofReal_natCast] at he
    simp only [c,sum_add_distrib,← mul_sum,prefix_modeJump ρ h₂.1,prefix_modeJump ρ h₃.1]
    obtain ⟨el,eu⟩ := abs_le.mp he
    have hqE := one_le_quarterError h₁
    dsimp only [modePrefix,s₂,s₃,m,quarterError] at *
    rw [abs_le]
    constructor <;> linarith only [el,eu,hf.1,hf.2,hqE]
  obtain ⟨C₂,hC₂,hmode₂⟩ := modeJump_transfer ρ h₂.1 h₂.2
  obtain ⟨C₃,hC₃,hmode₃⟩ := modeJump_transfer ρ h₃.1 h₃.2
  let A := 4*(K+2)+m*(C₂+C₃)
  refine ⟨A,by dsimp only [A]; positivity,fun N hN => ?_⟩
  have e := transfer_quarterError c (K := K+2) (by positivity) hp hN
  have hscale := mul_le_mul_of_nonneg_left (one_le_quarterError (show (1:ℝ) ≤ N by exact_mod_cast hN))
    (mul_nonneg hm (add_nonneg hC₂ hC₃))
  simp only [c,add_mul,mul_assoc,sum_add_distrib,← mul_sum,add_div,mul_div_assoc] at e
  have h2 := abs_le.mp (hmode₂ N hN)
  have h3 := abs_le.mp (hmode₃ N hN)
  have eu := mul_le_mul_of_nonneg_left (add_le_add h2.2 h3.2) hm
  have el := mul_le_mul_of_nonneg_left (add_le_add h2.1 h3.1) hm
  have hE := abs_le.mp e
  change |oddQuotientPowerTotal N/(N:ℝ)+m*(oddQuotientEtaMode ρ s₂ N+oddQuotientEtaMode ρ s₃ N)| ≤ A*quarterError N
  rw [abs_le]
  dsimp only [oddQuotientPowerTotal,parity,A] at *
  constructor <;> linarith only [el,eu,hE.1,hE.2,hscale]

/-- Removing the two unrestricted power lattices from the raw parity mean
removes real modes with the corresponding alternating zeta multipliers. -/
theorem oddQuotientPowerTotal_lattice_modes :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ d ∈ Finset.Icc 1 N, primePowerPart d*discreteQuotientMean parity d N)/(N:ℝ)-
        oddQuotientPowerTotal N/(N:ℝ)-oddQuotientEtaMode 1 (1/2) N-oddQuotientEtaMode 1 (1/3) N| ≤
      C*quarterError N := by
  have h₂ : 0 < (1/2:ℂ).re := by norm_num
  have h₃ : 0 < (1/3:ℂ).re := by norm_num
  let c (n : ℕ) := primePowerPart n-properPowerLatticeWeight n-modeJump 1 (1/2) n-modeJump 1 (1/3) n
  have hp (n : ℕ) (hn : 1 ≤ n) : |∑ d ∈ Finset.Icc 1 n, c d| ≤ 2*quarterError n := by
    have h₁ : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hprefix := properPowerLatticeWeight_prefix n
    have he : (∑ d ∈ Finset.Icc 1 n, primePowerPart d)=Chebyshev.psi n-Chebyshev.theta n := by
      have hi : Finset.Icc 1 n=Finset.Ioc 0 n := by ext k; simp only [mem_Icc,mem_Ioc]; omega
      rw [hi,Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,sum_filter]
      exact sum_congr rfl fun d _ => by by_cases h : d.Prime <;> simp [primePowerPart,h]
    have hm (r : ℕ) : modePrefix 1 (1/(r:ℂ)) n=(n:ℝ)^(1/(r:ℝ)) := by
      simp only [modePrefix,div_one]
      have hh := Complex.ofReal_cpow (Nat.cast_nonneg (α := ℝ) n) (1/(r:ℝ))
      push_cast at hh
      rw [← hh,ofReal_re]
    simp only [c,sum_sub_distrib,prefix_modeJump 1 h₂,prefix_modeJump 1 h₃,he,
      show modePrefix 1 (1/2) n=(n:ℝ)^(1/2:ℝ) from hm 2,
      show modePrefix 1 (1/3) n=(n:ℝ)^(1/3:ℝ) from hm 3]
    dsimp only [properPowerDiscrepancy] at hprefix
    rw [abs_le]
    have hq := one_le_quarterError h₁
    constructor <;> linarith only [hprefix.1,hprefix.2,hq]
  obtain ⟨A,hA,hA'⟩ := modeJump_transfer 1 h₂ (by norm_num : (1/2:ℂ).re < 1)
  obtain ⟨B,hB,hB'⟩ := modeJump_transfer 1 h₃ (by norm_num : (1/3:ℂ).re < 1)
  refine ⟨8+A+B,by positivity,fun N hn => ?_⟩
  have h := transfer_quarterError c (K := 2) (by norm_num) hp hn
  simp only [c,sub_mul,sum_sub_distrib,sub_div] at h
  obtain ⟨ll,lu⟩ := abs_le.mp h
  obtain ⟨al,au⟩ := abs_le.mp (hA' N hn)
  obtain ⟨bl,bu⟩ := abs_le.mp (hB' N hn)
  have hh := mul_le_mul_of_nonneg_left (one_le_quarterError (show (1:ℝ)≤N by exact_mod_cast hn))
    (add_nonneg hA hB)
  unfold oddQuotientPowerTotal
  dsimp only [parity] at *
  rw [abs_le]
  constructor <;> linarith only [ll,lu,al,au,bl,bu,hh]

end GaloisForLFunctions.ExceptionalLayerTheory
