import GaloisForLFunctions.ExceptionalLayerTheory.EveryLastQuotientClassPreservesThePrimeLogarithmicSingularity
import GaloisForLFunctions.ExceptionalLayerTheory.AdjacentDenominatorsInDiscreteQuotientMeans
import GaloisForLFunctions.ExceptionalLayerTheory.DistinctPrimeFactorsInDyadicBinomialGcds
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound

/-!
# Counting distinct prime factors of a central binomial coefficient

The first mean of the unweighted count preserves the logarithmic
singularity of the ordinary-prime series at each right zero. Prime
powers and rounding to a multiple of the width cost square-root error.
-/

noncomputable section

open Finset Filter Topology Complex ArithmeticFunction
open scoped LSeries.notation

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Cumulative centered ordinary-prime count in the last quotient class. -/
def ordinaryLastClassTotal (q X : ℕ) : ℝ :=
  ∑ k ∈ range X, quotientClassMassOf ordinaryPrimeCountWeight q k

/-- Cumulative distinct-prime count of the gcd, centered at the same quotient
class of the discrete logarithmic integral. -/
def binomialDistinctPrimeTotal (j X : ℕ) : ℝ :=
  let q := 2^(j+1)
  ∑ k ∈ range X, (((dyadicBinomialGcd j (k/q)).primeFactors.card : ℝ) -
    quotientClassMassOf (fun m => (Real.log m)⁻¹) q k)

private theorem ordinaryLastClassTotal_above {b : ℝ} (hb : _root_.RHTower.zeroReSup<b) (hb1 : b<1) :
    ∃ C : ℝ, 0≤C ∧ ∀ q X : ℕ, 2≤q → 1≤X → |ordinaryLastClassTotal q X| ≤ C*(X:ℝ)^(b+1) := by
  obtain ⟨K,hK,hp⟩ := ordinary_prefix_power hb
  have hh := _root_.RHTower.half_le_zeroReSup.trans_lt hb
  have hb0 : 0<b := by linarith only [hh]
  refine ⟨K/b,by positivity,fun q X hq hx => ?_⟩
  let A := fun n : ℕ => if q∣n+1 then (1:ℝ) else 0
  have hn : ¬q∣1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
  have h0 : A 0=0 := by simp [A,hn]
  have he (k : ℕ) (hk : k∈range X) : quotientClassMassOf ordinaryPrimeCountWeight q k =
      ∑ m ∈ Icc 1 X, ordinaryPrimeCountWeight m*A (k/m) := by
    apply sum_subset (Icc_subset_Icc_right (mem_range.mp hk).le)
    intro m hm hm'
    have hm0 := (mem_Icc.mp hm).1
    have hkm : k<m := by by_contra! hg; exact hm' (mem_Icc.mpr ⟨hm0,hg⟩)
    rw [Nat.div_eq_of_lt hkm,h0,mul_zero]
  have ht : ordinaryLastClassTotal q X =
      ∑ m ∈ Icc 1 X, ordinaryPrimeCountWeight m*discreteQuotientMean A m X := by
    rw [ordinaryLastClassTotal,sum_congr rfl he,sum_comm]
    simp only [discreteQuotientMean,mul_sum]
  rw [ht]
  apply (abs_discreteQuotientMean_weighted _ A h0 (fun n => by dsimp only [A]; split <;> norm_num) X).trans
  have hxR : 0<(X:ℝ) := by exact_mod_cast hx
  rw [Real.rpow_add_one hxR.ne']
  calc
    _ ≤ X*∑ n ∈ Icc 1 X, K*(n:ℝ)^(b-1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
      refine sum_le_sum fun n hn => ?_
      have h1 := (mem_Icc.mp hn).1
      have hnR : 0<(n:ℝ) := by exact_mod_cast h1
      rw [Real.rpow_sub_one hnR.ne',← mul_div_assoc]
      exact (div_le_div_of_nonneg_left (abs_nonneg _) hnR (by linarith : (n:ℝ)≤n+1)).trans
        (div_le_div_of_nonneg_right (hp n h1) hnR.le)
    _ ≤ _ := by
      rw [← mul_sum,← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ)]
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (_root_.HTGeometry.sum_rpow_sub_one_le hb0 hb1 X) hK) hxR.le).trans_eq (by ring)

private theorem jump_series {q : ℕ} [NeZero q] {s : ℂ} (hs : 1<s.re) :
    let c := fun n => ((ordinaryPrimeCountWeight*lastClassCoefficients q) n : ℂ)
    LSeriesSummable c s ∧ LSeries c s =
      lastQuotientClassSymbol q s*LSeries (fun n => (ordinaryPrimeCountWeight n : ℂ)) s := by
  have hc {n : ℕ} (hn : n≠0) : (lastClassCoefficients q n : ℂ)=lastClassJumps (n : ZMod q) := by
    have h1 : ((n:ZMod q)=-1) ↔ q∣n+1 := by
      rw [← ZMod.natCast_eq_zero_iff,Nat.cast_add,Nat.cast_one,add_eq_zero_iff_eq_neg]
    change ((if n=0 then (0:ℝ) else (if q∣n+1 then 1 else 0)-(if q∣n then 1 else 0)):ℂ)=_
    simp only [if_neg hn,lastClassJumps,h1,ZMod.natCast_eq_zero_iff]
    split_ifs <;> simp
  have he : (fun n => ((ordinaryPrimeCountWeight*lastClassCoefficients q) n : ℂ)) =
      ((fun n => (ordinaryPrimeCountWeight n : ℂ)) ⍟ fun n => (lastClassCoefficients q n : ℂ)) := by
    funext n
    rw [LSeries.convolution_def]
    exact _root_.RHTower.Sieve.coe_mul_apply _ _ _
  have ha := ordinaryPrimeCountWeight_summable hs
  have hd : LSeriesSummable (fun n => (lastClassCoefficients q n : ℂ)) s :=
    (LSeriesSummable_congr s hc).mpr (ZMod.LSeriesSummable_of_one_lt_re lastClassJumps hs)
  dsimp only
  rw [he]
  refine ⟨ha.convolution hd,?_⟩
  rw [LSeries_convolution' ha hd,LSeries_congr hc s,lastQuotientClassSymbol_eq_LSeries q hs,mul_comm]

private theorem power_excludes_zero {q : ℕ} [NeZero q] (hq : 2≤q) {b C : ℝ}
    (hb : 1/2≤b) (hb1 : b<1) (hC : 0≤C)
    (h : ∀ N : ℕ, 1≤N → |ordinaryLastClassTotal q N| ≤ C*(N:ℝ)^(b+1))
    {ρ : ℂ} (hρ : b<ρ.re) : riemannZeta ρ≠0 := by
  let c := fun n => (ordinaryPrimeCountWeight*lastClassCoefficients q) n
  have hb0 : 0≤b := by linarith only [hb]
  have hprofile (N : ℕ) (hn : 1≤N) : |triangularPrimeProfile c (N:ℝ)⁻¹| ≤ C*(N:ℝ)^b := by
    have hp : 0<(N:ℝ) := by exact_mod_cast hn
    have he : (N:ℝ)*triangularPrimeProfile c (N:ℝ)⁻¹=ordinaryLastClassTotal q N := by
      rw [triangularPrimeProfile_sample,ordinaryLastClassTotal]
      exact sum_congr rfl fun k _ => (quotientClassMassOf_eq_prefix _ hq k).symm
    have hh := h N hn
    rw [← he,abs_mul,abs_of_pos hp,Real.rpow_add_one hp.ne'] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (by ring)) hp
  have hdiff : DifferentiableOn ℂ (triangularDirichletContinuation c) {s : ℂ | b<s.re} :=
    fun _ hs => (differentiableAt_triangularDirichletContinuation c hC hb0 hprofile hs).differentiableWithinAt
  apply lastClass_primePrimitive_continuation_excludes_zero hq hb hb1 (triangularDirichletContinuation c)
    ((hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)).meromorphicOn) _ hρ
  intro s hs
  let f := fun n => (c n:ℂ)
  have hf : LSeriesSummable f 2 := (jump_series (q := q) (s := 2) (by norm_num)).1
  let M := ∑' n, ‖LSeries.term f 2 n‖
  have hcoef (n : ℕ) : |c (n+1)| ≤ M*((n:ℝ)+1)^(2:ℝ) := by
    have he : ‖LSeries.term f 2 (n+1)‖ ≤ M := hf.norm.le_tsum (n+1) (fun k => norm_nonneg _)
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),norm_div] at he
    have hpow : (2:ℂ)=(2:ℕ) := by norm_num
    rw [hpow,Complex.cpow_natCast,norm_pow] at he
    simp only [f,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast,Nat.cast_succ] at he
    rw [Real.rpow_two]
    apply (div_le_iff₀ (by positivity : 0<((n:ℝ)+1)^2)).mp
    exact he
  have hs1 : 1<s.re := by linarith only [hs]
  rw [triangularDirichletContinuation_eq_series c hcoef (by linarith only [hs]) (by linarith only [hs]),
    ← (jump_series (q := q) hs1).2]
  have hsum := (jump_series (q := q) hs1).1.hasSum
  have hs' := (hasSum_nat_add_iff' 1).mpr hsum
  simp only [sum_range_one,LSeries.term_zero,sub_zero] at hs'
  refine (tsum_congr (g := fun n => LSeries.term f s (n+1)) fun n => ?_).trans hs'.tsum_eq
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),Complex.cpow_neg,div_eq_mul_inv]
  simp [f]

private theorem prime_reference (q X : ℕ) :
    quotientClassMassOf ordinaryPrimeCountWeight q X = ((lastClassPrimes q X).card:ℝ) -
      quotientClassMassOf (fun m => (Real.log m)⁻¹) q X := by
  rw [lastClassPrimes_card,quotientClassMassOf,quotientClassMassOf,quotientClassMassOf,← sum_sub_distrib]
  refine sum_congr rfl fun m _ => ?_
  exact sub_mul _ _ _

/-- Replacing the prime-level count by the distinct factors and sampling at
the preceding multiple costs at most a constant times the square root per base. -/
theorem binomialDistinctPrimeTotal_error (j : ℕ) {b : ℝ} (hb : 1/2≤b) :
    ∃ K : ℝ, 0≤K ∧ ∀ X : ℕ, 1≤X →
      |binomialDistinctPrimeTotal j X-ordinaryLastClassTotal (2^(j+1)) X| ≤ K*(X:ℝ)^(b+1) := by
  let q := 2^(j+1)
  have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let K := 1+(q:ℝ)*(2/Real.log 2)
  have hK : 0≤K := by dsimp only [K]; positivity
  refine ⟨K,hK,fun X hX => ?_⟩
  have hx : 1≤(X:ℝ) := by exact_mod_cast hX
  have hlog : Real.log ((X:ℝ)+1)≤2*Real.sqrt X := calc
    _ ≤ Real.sqrt ((X:ℝ)+1) := _root_.RHTower.log_le_sqrt (by positivity)
    _ ≤ Real.sqrt (4*(X:ℝ)) := Real.sqrt_le_sqrt (by linarith only [hx])
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
  have hcell (k : ℕ) (hk : k∈range X) :
      |((dyadicBinomialGcd j (k/q)).primeFactors.card:ℝ)-(lastClassPrimes q k).card| ≤ K*Real.sqrt X := by
    let Y := q*(k/q)
    have hy : Y≤k := Nat.mul_div_le k q
    have hkX := (mem_range.mp hk).le
    have hgap : k-Y≤q := by
      have := Nat.mod_add_div k q
      have := Nat.mod_lt k (by omega : 0<q)
      dsimp only [Y]; omega
    have hsmall : (Nat.primeCounting Y.sqrt:ℝ)≤Real.sqrt X := by
      have hc : Nat.primeCounting Y.sqrt ≤ Y.sqrt := by
        rw [← Nat.primesLE_card_eq_primeCounting,Nat.primesLE_eq_filter_Icc_one]
        exact (card_filter_le ..).trans (by simp)
      exact (show (Nat.primeCounting Y.sqrt:ℝ)≤(Y.sqrt:ℝ) by exact_mod_cast hc).trans
        (Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (by exact_mod_cast hy.trans hkX)))
    obtain ⟨hlo,hhi⟩ := dyadicBinomialGcd_distinct_prime_count_error j (k/q)
    have h₁ : |((dyadicBinomialGcd j (k/q)).primeFactors.card:ℝ)-(lastClassPrimes q Y).card| ≤ Real.sqrt X :=
      (abs_of_nonneg hlo).le.trans (hhi.trans hsmall)
    have h₂ := lastClassPrimes_cutoff_gap hq hy
    rw [abs_sub_comm] at h₂
    have hc := (Real.log_le_log (by positivity : 0<(k:ℝ)+1)
      (by exact_mod_cast Nat.add_le_add_right hkX 1)).trans hlog
    have ht := mul_le_mul (show ((k-Y:ℕ):ℝ)≤q by exact_mod_cast hgap)
      (div_le_div_of_nonneg_right hc hlog2.le)
      (div_nonneg (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg k))) hlog2.le) (Nat.cast_nonneg q)
    exact ((abs_sub_le _ ((lastClassPrimes q Y).card:ℝ) _).trans
      (add_le_add h₁ (h₂.trans ht))).trans_eq (by dsimp only [K]; ring)
  change |(∑ k ∈ range X, _) - (∑ k ∈ range X, quotientClassMassOf ordinaryPrimeCountWeight q k)| ≤ _
  simp_rw [prime_reference]
  rw [← sum_sub_distrib]
  simp only [sub_sub_sub_cancel_right]
  apply (abs_sum_le_sum_abs _ _).trans
  have hh := sum_le_sum hcell
  rw [sum_const,card_range,nsmul_eq_mul] at hh
  have hr : Real.sqrt X≤(X:ℝ)^b := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx hb
  rw [Real.rpow_add_one (ne_of_gt (zero_lt_one.trans_le hx))]
  exact hh.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hK)
    (Nat.cast_nonneg X)).trans_eq (by ring))

/-- At any one prescribed depth, the distinct-prime count recovers RH. -/
theorem riemannHypothesis_iff_binomialDistinctPrimeTotal (j : ℕ) :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/2<b → b<1 → ∃ C : ℝ, ∀ X : ℕ, 1≤X →
      |binomialDistinctPrimeTotal j X| ≤ C*(X:ℝ)^(b+1) := by
  let q := 2^(j+1)
  have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  constructor
  · intro hRH b hb hb1
    have hsup := _root_.RHTower.zeroReSup_le_of_forall_re_le fun z =>
      (_root_.RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH z).le
    obtain ⟨C,_,h⟩ := ordinaryLastClassTotal_above (hsup.trans_lt hb) hb1
    obtain ⟨K,_,hcmp⟩ := binomialDistinctPrimeTotal_error j hb.le
    refine ⟨K+C,fun X hx => ?_⟩
    have he := abs_sub_le (binomialDistinctPrimeTotal j X) (ordinaryLastClassTotal q X) 0
    simp only [sub_zero] at he
    exact (he.trans (add_le_add (hcmp X hx) (h q X hq hx))).trans_eq (add_mul ..).symm
  · intro h
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro ρ hρ hhi
    obtain ⟨b,hb,hbρ⟩ := exists_between hρ
    obtain ⟨C,hC⟩ := h b hb (hbρ.trans hhi)
    obtain ⟨K,hK,hcmp⟩ := binomialDistinctPrimeTotal_error j hb.le
    apply power_excludes_zero (q := 2^(j+1)) hq hb.le (hbρ.trans hhi) (add_nonneg hK (abs_nonneg C)) _ hbρ
    intro X hx
    have he := abs_sub_le (ordinaryLastClassTotal q X) (binomialDistinctPrimeTotal j X) 0
    simp only [sub_zero] at he
    rw [abs_sub_comm] at he
    have hh := (hC X hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    exact (he.trans (add_le_add (hcmp X hx) hh)).trans_eq (add_mul ..).symm

/-- The single central binomial coefficient suffices, including at zeros of the
alternating zeta function that appears in its logarithm. -/
theorem riemannHypothesis_iff_centralBinom_distinct_prime_count :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/2<b → b<1 → ∃ C : ℝ, ∀ X : ℕ, 1≤X →
      |∑ k ∈ range X, (((Nat.centralBinom (k/2)).primeFactors.card : ℝ) -
        quotientClassMassOf (fun m => (Real.log m)⁻¹) 2 k)| ≤ C*(X:ℝ)^(b+1) := by
  simpa only [binomialDistinctPrimeTotal,dyadicBinomialGcd,Nat.zero_add,pow_one] using
    riemannHypothesis_iff_binomialDistinctPrimeTotal 0

#print axioms binomialDistinctPrimeTotal_error
#print axioms riemannHypothesis_iff_binomialDistinctPrimeTotal
#print axioms riemannHypothesis_iff_centralBinom_distinct_prime_count

end GaloisForLFunctions.ExceptionalLayerTheory
