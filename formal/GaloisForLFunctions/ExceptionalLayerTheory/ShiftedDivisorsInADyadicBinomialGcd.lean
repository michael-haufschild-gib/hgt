import GaloisForLFunctions.ExceptionalLayerTheory.ThePrimeCountInADyadicBinomialGcd
import GaloisForLFunctions.ExceptionalLayerTheory.PrimeDivisorsAtTheFirstDyadicSquareCrossing
import GaloisForLFunctions.RHTower.Matveev.FeldmanCommonDivisor

/-!
# Shifted divisors in the binomial gcd count

Each selected divisor has a unique next multiple above the base cutoff.
Grouping by that multiple expresses the prime count through a short
interval of consecutive integers, with an increasing lower cutoff on
the divisors. A one-integer interval recovers precisely its Mangoldt weight.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev gap (N m : ℕ) := m - N%m

private theorem first_multiple {m : ℕ} (hm : 0 < m) (N : ℕ) :
    N+gap N m = (N/m+1)*m := by
  have he := Nat.mod_add_div N m
  have hr := Nat.mod_lt N hm
  rw [add_mul,one_mul,mul_comm (N/m) m]
  unfold gap
  omega

private theorem gap_unique {N m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hrm : r ≤ m)
    (hdiv : m ∣ N+r) : r = gap N m := by
  obtain ⟨k,hk⟩ := hdiv
  rw [mul_comm] at hk
  have h₁ := (Nat.div_lt_iff_lt_mul hm).mpr (show N < k*m by omega)
  have h₂ := (Nat.le_div_iff_mul_le hm).mpr (show k*m ≤ N+m by omega)
  rw [Nat.add_div_right _ hm] at h₂
  rw [show k=N/m+1 by omega,← first_multiple hm] at hk
  omega

private theorem carry_at_next_multiple {j N m : ℕ} (hm : 0 < m) :
    dyadicQuotientCarry j N m = 1 ↔ 2^(j+1)*gap N m ≤ m := by
  let q := 2^(j+1)
  rw [dyadicQuotientCarry_one_iff hm]
  constructor
  · rintro ⟨k,hl,hu⟩
    have hk := (Nat.div_lt_iff_lt_mul hm).mpr hl
    have hh := (Nat.mul_le_mul_left q (Nat.mul_le_mul_right m hk)).trans hu
    rw [← first_multiple hm,mul_add] at hh
    exact Nat.le_of_add_le_add_left hh
  · intro h
    have hg : 0 < gap N m := Nat.sub_pos_of_lt (Nat.mod_lt N hm)
    refine ⟨N/m+1,?_,?_⟩
    · rw [← first_multiple hm]; omega
    · rw [← first_multiple hm,mul_add]; exact Nat.add_le_add_left h _

private theorem shift_le_horizon {N m q r : ℕ} (hq : 2 ≤ q) (hmr : m ≤ N+r)
    (hqr : q*r ≤ m) : r ≤ N/(q-1) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < q-1)).mpr
  rw [mul_comm]
  have h := hqr.trans hmr
  nth_rw 1 [show q=(q-1)+1 by omega] at h
  rw [add_mul,one_mul] at h
  omega

/-- The selected prime powers are exactly the large divisors of the integers
from `N+1` through `N + floor(N/(q-1))`, with threshold `q*r` at shift `r`. -/
theorem dyadicCommonPrimeMass_eq_shifted_divisors (j N : ℕ) :
    dyadicCommonPrimeMass j N =
      ∑ r ∈ Icc 1 (N/(2^(j+1)-1)),
        ∑ m ∈ (N+r).divisors.filter (fun m => 2^(j+1)*r ≤ m), vonMangoldt m := by
  let q := 2^(j+1)
  let H := N/(q-1)
  let X := q*N
  have hq : 2 ≤ q := by have := Nat.lt_two_pow_self (n := j+1); dsimp only [q]; omega
  have he (m : ℕ) (hm : m ∈ Icc 1 X) :
      (dyadicQuotientCarry j N m : ℝ)*vonMangoldt m =
        ∑ r ∈ Icc 1 H, if m ∣ N+r ∧ q*r ≤ m then vonMangoldt m else 0 := by
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    let r := gap N m
    have hr : 0 < r := Nat.sub_pos_of_lt (Nat.mod_lt N hm0)
    have hdiv : m ∣ N+r := ⟨N/m+1,(first_multiple hm0 N).trans (mul_comm ..)⟩
    have hunique {s : ℕ} (hs : s ∈ Icc 1 H) (hmul : m ∣ N+s) (hqsm : q*s ≤ m) :
        s = r := gap_unique hm0 (mem_Icc.mp hs).1
          ((Nat.le_mul_of_pos_left s (by omega : 0 < q)).trans hqsm) hmul
    by_cases hy : q*r ≤ m
    · have hc := (carry_at_next_multiple (j := j) hm0).mpr hy
      have hrH := shift_le_horizon hq (Nat.le_of_dvd (by omega : 0 < N+r) hdiv) hy
      rw [hc,Nat.cast_one,one_mul,sum_eq_single r]
      · exact (if_pos ⟨hdiv,hy⟩).symm
      · intro s hs hn
        exact if_neg fun h => hn (hunique hs h.1 h.2)
      · exact fun hn => (hn (mem_Icc.mpr ⟨hr,hrH⟩)).elim
    · have hc : dyadicQuotientCarry j N m = 0 := by
        have hh := mt (carry_at_next_multiple (j := j) hm0).mp hy
        unfold dyadicQuotientCarry at *
        split <;> simp_all
      rw [hc,Nat.cast_zero,zero_mul]
      symm
      refine sum_eq_zero fun s hs => if_neg fun h => ?_
      exact hy ((hunique hs h.1 h.2) ▸ h.2)
  unfold dyadicCommonPrimeMass
  rw [sum_congr rfl he,sum_comm]
  refine sum_congr rfl fun r hr => ?_
  have hr0 := (mem_Icc.mp hr).1
  have hrN := (mem_Icc.mp hr).2.trans (Nat.div_le_self N (q-1))
  have hNX : N+r ≤ X := (by omega : N+r ≤ 2*N).trans (Nat.mul_le_mul_right N hq)
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext m
  simp only [mem_filter,mem_Icc,Nat.mem_divisors]
  constructor
  · rintro ⟨_,hm,hqr⟩
    exact ⟨⟨hm,by omega⟩,hqr⟩
  · rintro ⟨⟨hm,hnz⟩,hqr⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hm (by omega), (Nat.le_of_dvd (by omega) hm).trans hNX⟩,hm,hqr⟩

/-- The count is bounded by the logarithm of the product of the short interval. -/
theorem dyadicCommonPrimeMass_le_short_log_product (j N : ℕ) :
    dyadicCommonPrimeMass j N ≤ ∑ r ∈ Icc 1 (N/(2^(j+1)-1)), Real.log (N+r : ℕ) := by
  rw [dyadicCommonPrimeMass_eq_shifted_divisors]
  refine sum_le_sum fun r _ => ?_
  rw [← vonMangoldt_sum]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => vonMangoldt_nonneg)

/-- At depths where only the next integer survives, the quotient count is its Mangoldt weight. -/
theorem dyadicCommonPrimeMass_eq_next_vonMangoldt {j N : ℕ} (h : N/(2^(j+1)-1) = 1) :
    dyadicCommonPrimeMass j N = vonMangoldt (N+1) := by
  let q := 2^(j+1)
  have hq : 2 ≤ q := by have := Nat.lt_two_pow_self (n := j+1); dsimp only [q]; omega
  have hp : 0 < q-1 := by omega
  have hlow := (Nat.le_div_iff_mul_le hp).mp (show 1 ≤ N/(q-1) by rw [h])
  have hu := (Nat.div_lt_iff_lt_mul hp).mp (show N/(q-1) < 2 by rw [h]; omega)
  simp only [one_mul] at hlow
  have hs : (N+1).divisors.filter (fun m => q ≤ m) = {N+1} := by
    ext m
    simp only [mem_filter,Nat.mem_divisors,mem_singleton]
    constructor
    · rintro ⟨⟨hm,hn⟩,hmq⟩
      obtain ⟨k,hk⟩ := hm
      rcases (show k=1 ∨ 2 ≤ k by
        by_cases he : k=0
        · simp [he] at hk
        · omega) with rfl | hk2
      · simpa using hk.symm
      · have he := (Nat.mul_le_mul_left m hk2).trans_eq hk.symm
        omega
    · rintro rfl
      exact ⟨⟨dvd_refl _,by omega⟩,by omega⟩
  rw [dyadicCommonPrimeMass_eq_shifted_divisors,h]
  simpa only [Icc_self,sum_singleton,mul_one] using congrArg (fun S : Finset ℕ =>
    ∑ m ∈ S, vonMangoldt m) hs

/-- Every selected level carries when adding `floor(aN/d)` to `N` if
the positive numerator and denominator sum to at most the dyadic width. -/
theorem dyadicQuotientCarry_le_rational_binomial_carry {j N a d m : ℕ} (hm : 0 < m)
    (ha : 1 ≤ a) (hd : 1 ≤ d) (had : a+d ≤ 2^(j+1)) :
    dyadicQuotientCarry j N m + N/m + (a*N/d)/m ≤ (N+a*N/d)/m := by
  let q := 2^(j+1)
  let D := a*N/d
  let r := gap N m
  let t := (a*N)%d
  have hr : 0 < r := Nat.sub_pos_of_lt (Nat.mod_lt N hm)
  have ht : t < d := Nat.mod_lt (a*N) hd
  have hN : a*N = t+d*D := (Nat.mod_add_div (a*N) d).symm
  have hD : D = D%m+m*(D/m) := (Nat.mod_add_div D m).symm
  have hcarry (hy : dyadicQuotientCarry j N m = 1) : r ≤ D%m := by
    have hqr : q*r ≤ m := (carry_at_next_multiple hm).mp hy
    let e := d*(D%m)+t+a*r
    have heq : a*(N+r) = e+m*(d*(D/m)) := calc
      _ = t+d*D+a*r := by rw [mul_add,hN]
      _ = t+d*(D%m+m*(D/m))+a*r := congrArg (fun z => t+d*z+a*r) hD
      _ = _ := by dsimp only [e]; ring
    have hdiv : m ∣ e := by
      have hmadd : m ∣ N+r := ⟨N/m+1,(first_multiple hm N).trans (mul_comm ..)⟩
      have hmdiv : m ∣ a*(N+r) := dvd_mul_of_dvd_right hmadd a
      rw [heq] at hmdiv
      exact (Nat.dvd_add_left (Nat.dvd_mul_right m _)).mp hmdiv
    by_contra! hsmall
    have hprod := Nat.mul_le_mul_left d (show D%m+1 ≤ r from hsmall)
    rw [mul_add,mul_one] at hprod
    have hwidth := (Nat.mul_le_mul_right r had).trans hqr
    rw [add_mul] at hwidth
    have he0 : 0 < e := by dsimp only [e]; positivity
    have := Nat.le_of_dvd he0 hdiv
    dsimp only [e] at this
    omega
  change dyadicQuotientCarry j N m + N/m + D/m ≤ (N+D)/m
  rw [Nat.add_div hm]
  by_cases h : dyadicQuotientCarry j N m = 1
  · have hbit : m ≤ N%m+D%m := by have := hcarry h; dsimp only [r,gap] at this; omega
    rw [h,if_pos hbit]; omega
  · have hz : dyadicQuotientCarry j N m = 0 := by
      unfold dyadicQuotientCarry at h ⊢
      split
      next hbit => exact (h (if_pos hbit)).elim
      next => rfl
    rw [hz]; split <;> omega

/-- For reciprocal integer slopes the denominator boundary is exact. -/
theorem all_dyadic_carries_bound_iff (j d : ℕ) :
    (∀ N m : ℕ, 0 < m → dyadicQuotientCarry j N m + N/m + (N/d)/m ≤ (N+N/d)/m) ↔
      1 ≤ d ∧ d < 2^(j+1) := by
  let q := 2^(j+1)
  have hq : 2 ≤ q := by have := Nat.lt_two_pow_self (n := j+1); dsimp only [q]; omega
  constructor
  · intro h
    have hc : dyadicQuotientCarry j (q-1) q = 1 := by
      apply (carry_at_next_multiple (by omega : 0 < q)).mpr
      simp only [gap,Nat.mod_eq_of_lt (by omega : q-1 < q)]
      change q*(q-(q-1)) ≤ q
      rw [show q-(q-1) = 1 by omega,mul_one]
    have he := h (q-1) q (by omega)
    rw [hc,Nat.div_eq_of_lt (by omega : q-1 < q)] at he
    by_contra! hn
    have hzero : (q-1)/d=0 := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · exact Nat.div_zero _
      · exact Nat.div_eq_of_lt (by have := hn hd; omega)
    simp only [hzero,Nat.zero_div,add_zero,Nat.div_eq_of_lt (by omega : q-1 < q)] at he
    omega
  · rintro ⟨hd,hdq⟩ N m hm
    simpa only [one_mul] using dyadicQuotientCarry_le_rational_binomial_carry
      (j := j) (N := N) hm (le_refl 1) hd (by omega)

private theorem log_factorial_on_longer_range {M X : ℕ} (h : M ≤ X) :
    Real.log (M.factorial : ℝ) = ∑ m ∈ Icc 1 X, ((M/m:ℕ):ℝ)*vonMangoldt m := by
  rw [GaloisForLFunctions.RHTower.Matveev.log_factorial_eq_sum_vonMangoldt]
  apply sum_subset (Icc_subset_Icc_right h)
  intro m hm hn
  have hlt : M < m := by
    by_contra! he
    exact hn (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,he⟩)
  rw [Nat.div_eq_of_lt hlt,Nat.cast_zero,zero_mul]

/-- Logarithmic form of the binomial carry, with any longer common summation range. -/
theorem log_choose_eq_sum_mangoldt_carries {N D X : ℕ} (hNX : N+D ≤ X) :
    Real.log ((N+D).choose D : ℕ) =
      ∑ m ∈ Icc 1 X, ((((N+D)/m:ℕ):ℝ) - (N/m:ℕ) - (D/m:ℕ))*vonMangoldt m := by
  have hlog := congrArg (fun n : ℕ => Real.log (n:ℝ)) (Nat.add_choose_mul_factorial_mul_factorial N D)
  have hc : 0 < (N+D).choose D := Nat.choose_pos (by omega)
  simp only [Nat.cast_mul] at hlog
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity)] at hlog
  simp_rw [sub_mul]
  rw [sum_sub_distrib,sum_sub_distrib,← log_factorial_on_longer_range hNX,
    ← log_factorial_on_longer_range ((Nat.le_add_right N D).trans hNX),
    ← log_factorial_on_longer_range ((Nat.le_add_left D N).trans hNX)]
  linarith only [hlog]

/-- One short binomial coefficient bounds the complete selected Mangoldt
mass, including every small prime power. -/
theorem dyadicCommonPrimeMass_le_log_short_binomial {j N d : ℕ} (hd : 1 ≤ d)
    (hdq : d < 2^(j+1)) :
    dyadicCommonPrimeMass j N ≤ Real.log ((N+N/d).choose (N/d) : ℕ) := by
  let X := 2^(j+1)*N
  have hNX : N+N/d ≤ X := (by have := Nat.div_le_self N d; omega : N+N/d ≤ 2*N).trans
    (Nat.mul_le_mul_right N (by omega))
  rw [log_choose_eq_sum_mangoldt_carries hNX,dyadicCommonPrimeMass]
  refine sum_le_sum fun m hm => mul_le_mul_of_nonneg_right ?_ vonMangoldt_nonneg
  have he := (all_dyadic_carries_bound_iff j d).mpr ⟨hd,hdq⟩ N m (mem_Icc.mp hm).1
  exact (le_sub_iff_add_le.mpr (le_sub_iff_add_le.mpr (by
    exact_mod_cast (by omega : dyadicQuotientCarry j N m +(N/d)/m + N/m ≤ (N+N/d)/m))))

#print axioms dyadicCommonPrimeMass_eq_shifted_divisors
#print axioms dyadicCommonPrimeMass_eq_next_vonMangoldt
#print axioms dyadicCommonPrimeMass_le_log_short_binomial

end GaloisForLFunctions.ExceptionalLayerTheory
