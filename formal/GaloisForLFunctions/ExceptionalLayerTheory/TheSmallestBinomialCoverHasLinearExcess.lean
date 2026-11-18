import GaloisForLFunctions.ExceptionalLayerTheory.ShiftedDivisorsInADyadicBinomialGcd
import GaloisForLFunctions.RHTower.MertensSecondTheorem

/-!
# The excess of the smallest binomial cover

The binomial with added part `floor(N/(q-1))` covers every selected level.
In its second quotient interval it also counts an entire interval of
unselected prime powers. The prime number theorem gives this excess
positive linear mass at every fixed dyadic width greater than two.
-/

noncomputable section

open Finset ArithmeticFunction Filter Topology

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem extra_band {j N d P Q : ℕ} (hd : 1 ≤ d) (hdq : d < 2^(j+1))
    (hPQ : P ≤ Q) (hQN : Q ≤ N) (hNP : N ≤ 2*P) (hDP : N/d ≤ P)
    (hQ : 2*Q ≤ N+N/d) (hP : 2^(j+1)*N ≤ (2*2^(j+1)-1)*P) :
    dyadicCommonPrimeMass j N + (Chebyshev.psi Q-Chebyshev.psi P) ≤
      Real.log ((N+N/d).choose (N/d) : ℕ) := by
  let q := 2^(j+1)
  let D := N/d
  let X := q*N
  have hq : 2 ≤ q := by dsimp only [q]; omega
  have hNX : N+D ≤ X := (by dsimp only [D]; have := Nat.div_le_self N d; omega : N+D ≤ 2*N).trans
    (Nat.mul_le_mul_right N hq)
  have hp (M : ℕ) (hM : M ≤ X) : Chebyshev.psi M =
      ∑ m ∈ Icc 1 X, if m ≤ M then vonMangoldt m else 0 := by
    rw [← sum_filter]
    have hset : (Icc 1 X).filter (· ≤ M) = Icc 1 M := by
      ext m; simp only [mem_filter,mem_Icc]; omega
    rw [hset,Chebyshev.psi,Nat.floor_natCast]
    rfl
  have hQX := hQN.trans ((Nat.le_add_right N D).trans hNX)
  rw [dyadicCommonPrimeMass,hp Q hQX,hp P (hPQ.trans hQX),← sum_sub_distrib,← sum_add_distrib,
    log_choose_eq_sum_mangoldt_carries hNX]
  apply sum_le_sum
  intro m hm
  have hm0 := (mem_Icc.mp hm).1
  have hcarry : dyadicQuotientCarry j N m + N/m + D/m ≤ (N+D)/m :=
    (all_dyadic_carries_bound_iff j d).mpr ⟨hd,hdq⟩ N m hm0
  have hbase : (dyadicQuotientCarry j N m : ℝ)*vonMangoldt m ≤
      ((((N+D)/m:ℕ):ℝ) - (N/m:ℕ) - (D/m:ℕ))*vonMangoldt m := by
    apply mul_le_mul_of_nonneg_right _ vonMangoldt_nonneg
    exact le_sub_iff_add_le.mpr (le_sub_iff_add_le.mpr (by exact_mod_cast
      (by omega : dyadicQuotientCarry j N m+D/m+N/m ≤ (N+D)/m)))
  by_cases h1 : m ≤ P
  · simpa only [if_pos h1,if_pos (h1.trans hPQ),sub_self,add_zero] using hbase
  by_cases h2 : m ≤ Q
  · rw [if_pos h2,if_neg h1,sub_zero]
    have hmP : P < m := by omega
    have hn : N/m = 1 := by
      apply Nat.le_antisymm
      · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hm0).mpr (by omega : N < 2*m))
      · exact (Nat.le_div_iff_mul_le hm0).mpr (by simpa using h2.trans hQN)
    have hd0 : D/m = 0 := Nat.div_eq_of_lt (hDP.trans_lt hmP)
    have hsum := (Nat.le_div_iff_mul_le hm0).mpr (show 2*m ≤ N+D by
      exact (Nat.mul_le_mul_left 2 h2).trans hQ)
    have hlt := hP.trans_lt ((Nat.mul_lt_mul_left (by omega : 0 < 2*q-1)).mpr hmP)
    have hge := (Nat.le_div_iff_mul_le hm0).mpr (Nat.mul_le_mul_left q (h2.trans hQN))
    have hup := (Nat.div_lt_iff_lt_mul hm0).mpr hlt
    have hc : dyadicQuotientCarry j N m = 0 := by
      apply if_neg
      change ¬ q ∣ q*N/m+1
      rintro ⟨k,hk⟩
      have hk1 : 1 < k := (Nat.mul_lt_mul_left (by omega : 0 < q)).mp (by
        rw [mul_one,← hk]; omega)
      have hk2 := Nat.mul_le_mul_left q (show 2 ≤ k from hk1)
      rw [← hk,mul_comm q 2] at hk2
      change q*N/m < 2*q-1 at hup
      omega
    change (dyadicQuotientCarry j N m : ℝ)*vonMangoldt m+vonMangoldt m ≤
      ((((N+D)/m:ℕ):ℝ) - (N/m:ℕ) - (D/m:ℕ))*vonMangoldt m
    rw [hc,hn,hd0,Nat.cast_one,Nat.cast_zero,zero_mul,zero_add,sub_zero]
    apply le_mul_of_one_le_left vonMangoldt_nonneg
    have hr : (2:ℝ) ≤ ((N+D)/m : ℕ) := by exact_mod_cast hsum
    linarith only [hr]
  · simpa only [if_neg h1,if_neg h2,sub_zero,add_zero] using hbase

/-- An explicit interval of width `qL` is counted only by the binomial.
The base cutoff here is `2(q-1)(2q-1)L`. -/
theorem short_binomial_excess_prime_interval {j : ℕ} (hj : 1 ≤ j) (L : ℕ) :
    let q := 2^(j+1)
    let D := 2*(2*q-1)*L
    let N := (q-1)*D
    dyadicCommonPrimeMass j N +
      (Chebyshev.psi (q*(2*q-1)*L : ℕ)-Chebyshev.psi (2*q*(q-1)*L : ℕ)) ≤
        Real.log ((N+D).choose D : ℕ) := by
  dsimp only
  let q := 2^(j+1)
  let D := 2*(2*q-1)*L
  let N := (q-1)*D
  have hq : 4 ≤ q := by
    change 2^2 ≤ 2^(j+1)
    exact pow_le_pow_right₀ (by omega) (by omega)
  have hD : N/(q-1)=D := Nat.mul_div_cancel_left _ (by omega)
  have hc₁ : 2*q*(q-1) ≤ q*(2*q-1) := calc
    _ = q*(2*(q-1)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left q (by omega)
  have hc₂ : q*(2*q-1) ≤ (q-1)*(2*(2*q-1)) := calc
    _ ≤ ((q-1)*2)*(2*q-1) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := mul_assoc ..
  have hc₃ : (q-1)*(2*(2*q-1)) ≤ 2*(2*q*(q-1)) := calc
    _ = (2*(q-1))*(2*q-1) := by ring
    _ ≤ (2*(q-1))*(2*q) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring
  have hc₄ : 2*(2*q-1) ≤ 2*q*(q-1) := calc
    _ ≤ 2*(q*2) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 2*(q*(q-1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    _ = _ := (mul_assoc ..).symm
  have hxq : 2*(q*(2*q-1)*L) = N+D := by
    change _ = (q-1)*D+D
    rw [← add_one_mul,show q-1+1=q by omega]
    dsimp only [D]; ring
  have hxp : q*N = (2*q-1)*(2*q*(q-1)*L) := by dsimp only [N,D]; ring
  have h := extra_band (j := j) (N := N) (d := q-1) (P := 2*q*(q-1)*L) (Q := q*(2*q-1)*L)
    (by omega) (show q-1 < q by omega) (Nat.mul_le_mul_right L hc₁)
    (by simpa only [N,D,mul_assoc] using Nat.mul_le_mul_right L hc₂)
    (by simpa only [N,D,mul_assoc] using Nat.mul_le_mul_right L hc₃)
    (by rw [hD]; exact Nat.mul_le_mul_right L hc₄) (by rw [hD]; exact hxq.le) hxp.le
  simpa only [hD] using h

private theorem scaled_psi {a : ℕ} (ha : 0 < a) :
    Tendsto (fun L : ℕ => Chebyshev.psi (a*L : ℕ)/(L:ℝ)) atTop (𝓝 (a:ℝ)) := by
  have hat : Tendsto (fun L : ℕ => a*L) atTop atTop := tendsto_atTop.mpr fun M =>
    (eventually_ge_atTop M).mono fun L hL => hL.trans (Nat.le_mul_of_pos_left L ha)
  have h := (RHTower.tendsto_psi_natCast_div.comp hat).mul_const (a:ℝ)
  rw [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  change Chebyshev.psi (a*L : ℕ)/(a*L : ℕ)*(a:ℝ) = Chebyshev.psi (a*L : ℕ)/L
  rw [Nat.cast_mul]
  field_simp [(by exact_mod_cast ha.ne' : (a:ℝ) ≠ 0),
    (by exact_mod_cast (Nat.ne_of_gt hL) : (L:ℝ) ≠ 0)]

/-- The optimal reciprocal-slope binomial exceeds the log gcd by a positive
linear amount on an arithmetic progression at each fixed depth greater than one. -/
theorem short_binomial_exceeds_dyadic_gcd_linearly {j : ℕ} (hj : 1 ≤ j) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop,
      let q := 2^(j+1)
      let D := 2*(2*q-1)*L
      let N := (q-1)*D
      Real.log (dyadicBinomialGcd j N) + c*L ≤ Real.log ((N+D).choose D : ℕ) := by
  let q := 2^(j+1)
  let d := 2*(2*q-1)
  let n := (q-1)*d
  let a := q*(2*q-1)
  let b := 2*q*(q-1)
  have hq : 2 ≤ q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  have hqR : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hab : a=b+q := by
    dsimp only [a,b]
    rw [show 2*q-1=2*(q-1)+1 by omega]
    ring
  have hb : 0 < b := by dsimp only [b]; exact Nat.mul_pos (by omega) (by omega)
  have ha : 0 < a := by omega
  have hdiff := (scaled_psi ha).sub (scaled_psi hb)
  rw [show (a:ℝ)-b=q by rw [hab,Nat.cast_add]; ring] at hdiff
  have hband := hdiff.eventually_const_lt (by linarith only [hqR] : (q:ℝ)/2 < q)
  obtain ⟨C,hC⟩ := exists_uniform_dyadicBinomialGcd_log_error
  let B := C*Real.sqrt (q*n : ℕ)
  have hsub : Tendsto (fun L : ℕ => B/Real.sqrt L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨(q:ℝ)/4,by positivity,?_⟩
  filter_upwards [hband,hsub.eventually_lt_const (by positivity : 0 < (q:ℝ)/4),
    eventually_ge_atTop 1] with L hL hsmall hL1
  have hLpos : 0 < (L:ℝ) := by exact_mod_cast hL1
  change (q:ℝ)/2 < Chebyshev.psi (a*L : ℕ)/L-Chebyshev.psi (b*L : ℕ)/L at hL
  rw [← sub_div,lt_div_iff₀ hLpos] at hL
  have hs := (div_lt_iff₀ (Real.sqrt_pos.mpr hLpos)).mp hsmall
  have herr := mul_le_mul_of_nonneg_right hs.le (Real.sqrt_nonneg (L:ℝ))
  rw [mul_assoc ((q:ℝ)/4),Real.mul_self_sqrt hLpos.le] at herr
  have he := (le_abs_self _).trans (hC j (n*L))
  change Real.log (dyadicBinomialGcd j (n*L))-dyadicCommonPrimeMass j (n*L) ≤
    C*Real.sqrt (q*(n*L) : ℕ) at he
  rw [← mul_assoc q n L,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg (q*n)),← mul_assoc] at he
  have hg := short_binomial_excess_prime_interval hj L
  change dyadicCommonPrimeMass j ((q-1)*(d*L)) +
    (Chebyshev.psi (a*L : ℕ)-Chebyshev.psi (b*L : ℕ)) ≤
      Real.log ((((q-1)*(d*L))+d*L).choose (d*L) : ℕ) at hg
  change Real.log (dyadicBinomialGcd j ((q-1)*(d*L))) + ((q:ℝ)/4)*L ≤ _
  rw [← mul_assoc (q-1) d L] at hg ⊢
  change Real.log (dyadicBinomialGcd j (n*L)) + ((q:ℝ)/4)*L ≤ Real.log ((n*L+d*L).choose (d*L) : ℕ)
  change B*Real.sqrt L ≤ _ at herr
  change _ ≤ B*Real.sqrt L at he
  linarith only [hg,hL,herr,he]

#print axioms short_binomial_excess_prime_interval
#print axioms short_binomial_exceeds_dyadic_gcd_linearly

end GaloisForLFunctions.ExceptionalLayerTheory
