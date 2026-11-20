import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheHodgeIndexHoldsAtEveryScaleOnShortWindows
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.SumsOverTheDegreePointsAreRiemannSums

/-!
# The finite part of a short flat Weil comb

For the flat profile on H consecutive sites above N, each positive separation
d occurs H-d times. This gives the whole singular jet exactly. In the range
H ≤ N there are no prime contacts, and the remaining three terms have error
at most 3H/N per site after the diagonal at N is subtracted.
-/

namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset Filter Topology AbsoluteGeometryOfSpecZ HodgeTheoryOfAFixedPart
noncomputable section
open scoped Classical

/-- Half the ordered singular pair sum on any interval of H consecutive
integers is H times its harmonic number minus H, independently of location. -/
theorem flat_interval_singular_jet (N H : ℕ) :
    (∑ n ∈ Ioc N (N+H), ∑ m ∈ (Ioc N (N+H)).erase n, 1/|(m:ℝ)-n|)/2 =
      (H:ℝ)*harm H-H := by
  let S := Ioc N (N+H)
  let u (m n : ℕ) : ℝ := if n < m then 1/((m:ℝ)-n) else 0
  have hsplit (m n : ℕ) : 1/|(m:ℝ)-n| = u m n+u n m := by
    rcases lt_trichotomy m n with h|rfl|h
    · rw [abs_sub_comm,abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr h))]
      simp only [u,if_neg h.not_gt,if_pos h,zero_add]
    · simp [u]
    · rw [abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr h))]
      simp only [u,if_pos h,if_neg h.not_gt,add_zero]
  have row (n : ℕ) (hn : n∈S) :
      ∑ m ∈ S.erase n, 1/|(m:ℝ)-n| = ∑ m ∈ S, (u m n+u n m) := by
    rw [sum_congr rfl (fun m _ => hsplit m n)]
    exact sum_subset (erase_subset _ _) fun m hm he => by
      have : m=n := by by_contra h; exact he (mem_erase.mpr ⟨h,hm⟩)
      simp [this,u]
  have triangle (n : ℕ) (hn : n∈S) : ∑ m ∈ S, u m n = harm (N+H-n) := by
    have hfilter : S.filter (n < ·) = Ioc n (N+H) := by
      ext m
      have hloc := mem_Ioc.mp hn
      simp only [S,mem_filter,mem_Ioc]
      omega
    simp only [u,← sum_filter,hfilter,sum_Ioc_inv_sub]
  have hsum : (∑ n ∈ S, ∑ m ∈ S, u m n) = (H:ℝ)*harm H-H := by
    rw [sum_congr rfl triangle]
    change (∑ n ∈ Ioc N (N+H), harm (N+H-n)) = _
    rw [sum_Ioc_add_eq_sum_range]
    calc
      _ = ∑ j ∈ range H, harm (H-1-j) := sum_congr rfl fun j _ => by congr 1; omega
      _ = ∑ j ∈ range H, harm j := sum_range_reflect harm H
      _ = _ := sum_range_harm H
  change (∑ n ∈ S, ∑ m ∈ S.erase n, 1/|(m:ℝ)-n|)/2=_
  rw [sum_congr rfl row]
  simp only [sum_add_distrib]
  rw [sum_comm (f:=fun n m => u n m),hsum]
  ring

/-- Uniform finite-scale error after removing the full discrete harmonic
self-energy. It tends to zero whenever the relative width tends to zero,
even along intervals whose width varies arbitrarily. -/
theorem short_flat_comb_finite_part {N H : ℕ} (hH : 0<H) (hHN : H≤N) :
    |combForm (Ioc N (N+H)) (fun _ => 1)/(H:ℝ) - (counterterm N-harm H+1)| ≤ 3*((H:ℝ)/N) := by
  let S := Ioc N (N+H)
  let D := ∑ n ∈ S, counterterm n
  let P := ∑ n ∈ S, 1/(n:ℝ)
  let R := (∑ n ∈ S, ∑ m ∈ S.erase n, 1/((m:ℝ)+n))/2
  have hhr : (0:ℝ)<H := Nat.cast_pos.mpr hH
  have hnr : (0:ℝ)<N := Nat.cast_pos.mpr (hH.trans_le hHN)
  have card : S.card=H := by simp [S,Nat.card_Ioc]
  have constsum (x : ℝ) : ∑ _n ∈ S, x = H*x := by rw [sum_const,card,nsmul_eq_mul]
  have low {n : ℕ} (hn : n∈S) : (N:ℝ)<n := Nat.cast_lt.mpr (mem_Ioc.mp hn).1
  have high {n : ℕ} (hn : n∈S) : (n:ℝ)≤N+(H:ℝ) := by exact_mod_cast (mem_Ioc.mp hn).2
  have logstep {n : ℕ} (hn : n∈S) : counterterm n-counterterm N = Real.log ((n:ℝ)/N) := by
    have np := hnr.trans (low hn)
    rw [counterterm,counterterm,Real.log_div np.ne' (by positivity),
      Real.log_div hnr.ne' (by positivity),Real.log_div np.ne' hnr.ne']
    ring
  have diag (n : ℕ) (hn : n∈S) : counterterm N ≤ counterterm n ∧
      counterterm n≤counterterm N+(H:ℝ)/N := by
    have hrat : 1 ≤ (n:ℝ)/N := (one_le_div hnr).mpr (low hn).le
    have ht := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hrat)
    have hbound : (n:ℝ)/N ≤ 1+(H:ℝ)/N := calc
      _ ≤ ((N:ℝ)+H)/N := div_le_div_of_nonneg_right (high hn) hnr.le
      _ = _ := by rw [add_div,div_self hnr.ne']
    constructor <;> linarith only [logstep hn,Real.log_nonneg hrat,ht,hbound]
  have dlow : (H:ℝ)*counterterm N≤D := by
    rw [← constsum]; exact sum_le_sum fun n hn => (diag n hn).1
  have dhigh : D≤(H:ℝ)*(counterterm N+(H:ℝ)/N) := by
    rw [← constsum]; exact sum_le_sum fun n hn => (diag n hn).2
  have pbound : P≤(H:ℝ)/N := calc
    _ ≤ ∑ _n ∈ S, 1/(N:ℝ) := sum_le_sum fun n hn => one_div_le_one_div_of_le hnr (low hn).le
    _ = _ := by rw [constsum]; ring
  have ppos : 0≤P := sum_nonneg fun n _ => by positivity
  have rpos : 0≤R := by dsimp only [R]; positivity
  have rbound : R≤(H:ℝ)*((H:ℝ)/N)/4 := by
    have each (n : ℕ) (hn : n∈S) :
        ∑ m ∈ S.erase n, 1/((m:ℝ)+n) ≤ H*(1/(2*(N:ℝ))) := calc
      _ ≤ ∑ m ∈ S, 1/((m:ℝ)+n) :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
      _ ≤ ∑ _m ∈ S, 1/(2*(N:ℝ)) := sum_le_sum fun m hm =>
        one_div_le_one_div_of_le (by positivity) (by linarith only [low hn,low hm])
      _ = _ := constsum _
    have hs := sum_le_sum each
    rw [constsum] at hs
    dsimp only [R]
    calc
      _ ≤ (H:ℝ)*(H*(1/(2*(N:ℝ))))/2 := div_le_div_of_nonneg_right hs (by norm_num)
      _ = _ := by ring
  have ident : combForm S (fun _ => 1) = 2*P*H+D-((H:ℝ)*harm H-H)-R := by
    have hp (n : ℕ) (hn : n∈S) (m : ℕ) (hm : m∈S.erase n) :
        pairKernel m n = (1/|(m:ℝ)-n|+1/((m:ℝ)+n))/2 := by
      rw [pairKernel,contact_eq_zero_of_window hHN (mem_of_mem_erase hm) hn (ne_of_mem_erase hm),add_zero]
      rfl
    have pairs : (∑ n ∈ S, ∑ m ∈ S.erase n, pairKernel m n) = (H:ℝ)*harm H-H+R := by
      have h := flat_interval_singular_jet N H
      change (∑ n ∈ S, ∑ m ∈ S.erase n, 1/|(m:ℝ)-n|)/2=_ at h
      rw [sum_congr rfl (fun n hn => sum_congr rfl (hp n hn))]
      simp only [← sum_div,sum_add_distrib,R,add_div,h]
    simp only [HodgeTheoryOfAFixedPart.combForm,degOne,degTwo,HodgeTheoryOfAFixedPart.combPairing,
      one_pow,one_mul, sum_const,card,nsmul_eq_mul,mul_one,pairs]
    change 2*(P*(H:ℝ))-(_-D)=_
    ring
  change |combForm S (fun _ => 1)/H-_|≤_
  rw [ident,abs_sub_le_iff]
  constructor
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ hhr).mpr
    nlinarith only [dhigh,mul_le_mul_of_nonneg_right pbound hhr.le,rpos]
  · have lower : counterterm N-harm H+1-3*((H:ℝ)/N) ≤
        (2*P*H+D-((H:ℝ)*harm H-H)-R)/H := (le_div_iff₀ hhr).mpr (by
      nlinarith only [dlow,mul_nonneg ppos hhr.le,rbound,
        mul_nonneg hhr.le (div_nonneg hhr.le hnr.le)])
    linarith only [lower]

/-- For every diverging width of vanishing relative size, the energy per
site minus the logarithm of the inverse relative width has the same limit. -/
theorem mesoscopic_flat_comb_limit (H : ℕ → ℕ) (hwidth : Tendsto H atTop atTop)
    (hrel : Tendsto (fun N => (H N:ℝ)/(N:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => combForm (Ioc N (N+H N)) (fun _ => 1)/(H N:ℝ) -
      Real.log ((N:ℝ)/(H N:ℝ))) atTop (𝓝 (1-Real.eulerMascheroniConstant-Real.log (2*Real.pi))) := by
  let W (N : ℕ) := combForm (Ioc N (N+H N)) (fun _ => 1)/(H N:ℝ)
  let ε (N : ℕ) := W N - (counterterm N-harm (H N)+1)
  have hdom : ∀ᶠ N : ℕ in atTop, 0<N ∧ 0<H N ∧ H N≤N := by
    filter_upwards [eventually_ge_atTop 1,hwidth.eventually_ge_atTop 1,
      hrel.eventually (Iio_mem_nhds zero_lt_one)] with N hn hh hr
    have hN : 0<N := hn
    have hrat : (H N:ℝ)/(N:ℝ)<1 := hr
    have hlt := (div_lt_one (Nat.cast_pos.mpr hN : (0:ℝ)<N)).mp hrat
    exact ⟨hN,hh, Nat.cast_le.mp hlt.le⟩
  have herr : Tendsto ε atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun N : ℕ => 3*((H N:ℝ)/(N:ℝ)))
    · filter_upwards [hdom] with N hn
      rw [Real.norm_eq_abs]
      exact short_flat_comb_finite_part hn.2.1 hn.2.2
    · simpa only [mul_zero] using hrel.const_mul 3
  have h := (herr.sub (tendsto_harm_sub_log.comp hwidth)).add_const (1-Real.log (2*Real.pi))
  rw [show (0:ℝ)-Real.eulerMascheroniConstant+(1-Real.log (2*Real.pi)) =
    1-Real.eulerMascheroniConstant-Real.log (2*Real.pi) by ring] at h
  apply h.congr'
  filter_upwards [hdom] with N hn
  have hN : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.1.ne'
  have hH : (H N:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.2.1.ne'
  change ε N - (harm (H N)-Real.log (H N))+(1-Real.log (2*Real.pi)) =
    W N-Real.log ((N:ℝ)/(H N:ℝ))
  rw [ε,counterterm,Real.log_div hN (by positivity),Real.log_div hN hH]
  ring

#print axioms mesoscopic_flat_comb_limit
#print axioms flat_interval_singular_jet
#print axioms short_flat_comb_finite_part

end
end GaloisForLFunctions.SignedArithmeticCorrespondences
