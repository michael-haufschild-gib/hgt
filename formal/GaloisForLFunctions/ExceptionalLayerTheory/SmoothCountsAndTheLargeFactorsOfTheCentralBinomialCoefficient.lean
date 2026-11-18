import GaloisForLFunctions.ExceptionalLayerTheory.TheDistinctPrimeFactorsOfOneCentralBinomialDetectEveryRightZero
import GaloisForLFunctions.RHTower.MobiusFriableLargestPrimeDecomposition
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence

/-!
# Smooth counts and the large prime factors of a central binomial coefficient

Before two primes above the smoothness cutoff can occur together, the
complement of the smooth integers is the disjoint union of their multiples.
The dyadic difference of the resulting floor counts is a binomial carry.
-/

noncomputable section

open Finset
open _root_.RHTower

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Positive integers up to X supported on primes at most y, counted once. -/
def smoothIntegerCount (X y : ℕ) : ℕ := (Sieve.smoothUpTo (Nat.primesLE y) X).card

private theorem count_smooth_and_multiples {x B y : ℕ} (hx : x≤B) (hs : x<(y+1)^2) :
    smoothIntegerCount x y + ∑ p ∈ largePrimes B y, x/p = x := by
  classical
  let P := largePrimes B y
  let S := Sieve.smoothUpTo (Nat.primesLE y) x
  have hrow (n : ℕ) (hn : n∈Icc 1 x) :
      (if n∈S then 1 else 0) + (∑ p ∈ P, if p∣n then 1 else 0) = (1:ℕ) := by
    have hn' := mem_Icc.mp hn
    have hmem (p : ℕ) (hp : p∈P) (hd : p∣n) : p∈n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨(mem_largePrimes.mp hp).1.2,hd,by omega⟩
    by_cases hS : n∈S
    · have h := (mem_smoothUpTo_iff.mp hS).2
      have hz : (∑ p ∈ P, if p∣n then 1 else 0) = (0:ℕ) := by
        refine sum_eq_zero fun p hp => if_neg fun hd => ?_
        exact (mem_largePrimes.mp hp).2.not_ge (h p (hmem p hp hd))
      simp [hS,hz]
    · have hf : ¬∀ p ∈ n.primeFactors, p≤y := fun hh => hS (mem_smoothUpTo_iff.mpr ⟨hn',hh⟩)
      push Not at hf
      obtain ⟨p,hp,hyp⟩ := hf
      have hpP : p∈P := mem_largePrimes.mpr ⟨⟨(Nat.le_of_dvd hn'.1
        (Nat.dvd_of_mem_primeFactors hp)).trans (hn'.2.trans hx),Nat.prime_of_mem_primeFactors hp⟩,hyp⟩
      have hsum : (∑ r ∈ P, if r∣n then 1 else 0)=(1:ℕ) := by
        rw [sum_eq_single_of_mem p hpP]
        · simp [Nat.dvd_of_mem_primeFactors hp]
        · intro r hr hrp
          apply if_neg
          intro hd
          have hh := mem_largePrimes.mp hr
          have hc := (Nat.coprime_primes hh.1.2 (Nat.prime_of_mem_primeFactors hp)).mpr hrp
          have hle := Nat.le_of_dvd hn'.1 (hc.mul_dvd_of_dvd_of_dvd hd (Nat.dvd_of_mem_primeFactors hp))
          have hm : (y+1)^2≤r*p := by rw [sq]; exact Nat.mul_le_mul hh.2 hyp
          exact (not_le_of_gt hs) (hm.trans (hle.trans hn'.2))
      simp [hS,hsum]
  have hS : (Icc 1 x).filter (· ∈ S)=S := by
    ext n
    exact mem_filter.trans ⟨And.right,fun h => ⟨mem_Icc.mpr (mem_smoothUpTo_iff.mp h).1,h⟩⟩
  have hcount : S.card = ∑ n ∈ Icc 1 x, (if n∈S then 1 else 0) := by rw [← sum_filter,hS]; simp
  have hlarge (p : ℕ) (hp : p∈P) :
      x/p = ∑ n ∈ Icc 1 x, (if p∣n then 1 else 0) := by
    rw [← sum_filter,_root_.RHTower.sum_Icc_filter_dvd_reindex p x (mem_largePrimes.mp hp).1.2.pos]
    simp
  change S.card + (∑ p ∈ P, _) = _
  rw [hcount,sum_congr rfl hlarge,sum_comm (s := P),← sum_add_distrib,sum_congr rfl hrow]
  simp

private theorem dyadic_floor_carry (n p : ℕ) :
    (2*n/p:ℕ)=2*(n/p)+(if 2∣2*n/p+1 then 1 else 0) := by
  have hh : (2*n/p)/2=n/p := by
    rw [Nat.div_div_eq_div_mul,mul_comm p 2,Nat.mul_div_mul_left n p two_pos]
  split <;> omega

/-- The number of large factors of the central binomial coefficient is the exact
dyadic difference of smooth counts. The floor of the square root is admissible. -/
theorem smoothIntegerCount_centralBinom_large_factors (n y : ℕ) (hs : 2*n<(y+1)^2) :
    2*smoothIntegerCount n y = smoothIntegerCount (2*n) y +
      (((Nat.centralBinom n).primeFactors).filter (y<·)).card := by
  classical
  let P := largePrimes (2*n) y
  have h₁ := count_smooth_and_multiples (y := y) (B := 2*n) (by omega : n≤2*n)
    (lt_of_le_of_lt (by omega : n≤2*n) hs)
  have h₂ := count_smooth_and_multiples (y := y) (B := 2*n) (le_refl _) hs
  have hset : P.filter (fun p => 2∣2*n/p+1) = (Nat.centralBinom n).primeFactors.filter (y<·) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpP,hcarry⟩ := mem_filter.mp hp
      obtain ⟨⟨hpX,hpr⟩,hpy⟩ := mem_largePrimes.mp hpP
      apply mem_filter.mpr
      refine ⟨(dyadicBinomialGcd_distinct_prime_factors 0 n).1 ?_,hpy⟩
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpX,hpr⟩,hcarry⟩
    · intro hp
      obtain ⟨hfac,hpy⟩ := mem_filter.mp hp
      have hpr := Nat.prime_of_mem_primeFactors hfac
      have hsq : 2*n<p^2 := hs.trans_le (Nat.pow_le_pow_left hpy 2)
      have hval := factorization_dyadicBinomialGcd_of_lt_sq (j := 0) (N := n) hpr hsq
      have hne : (dyadicBinomialGcd 0 n).factorization p ≠ 0 := by
        rw [← Finsupp.mem_support_iff,Nat.support_factorization]
        exact hfac
      rw [hval] at hne
      have hd : 2∣2*n/p+1 := by by_contra hh; exact hne (if_neg hh)
      have hle : p≤2*n := by by_contra! hl; rw [Nat.div_eq_of_lt hl] at hd; norm_num at hd
      exact mem_filter.mpr ⟨mem_largePrimes.mpr ⟨⟨hle,hpr⟩,hpy⟩,hd⟩
  have he : (∑ p ∈ P, 2*n/p) = 2*(∑ p ∈ P, n/p)+(P.filter (fun p => 2∣2*n/p+1)).card := by
    calc
      _ = ∑ p ∈ P, (2*(n/p)+(if 2∣2*n/p+1 then 1 else 0)) :=
        sum_congr rfl fun p _ => dyadic_floor_carry n p
      _ = _ := by rw [sum_add_distrib,← mul_sum,← sum_filter]; simp
  change _ + (∑ p ∈ P, _) = _ at h₁ h₂
  rw [hset] at he
  omega

/-- Dyadic smooth-count discrepancy with the prime support frozen at the
square root of the outer cutoff for every summand. -/
def smoothDyadicFirstTotal (X : ℕ) : ℝ :=
  ∑ k ∈ range X, (2*(smoothIntegerCount (k/2) X.sqrt:ℝ) -
    smoothIntegerCount (2*(k/2)) X.sqrt - quotientClassMassOf (fun m => (Real.log m)⁻¹) 2 k)

/-- At any cutoff the entire error from discarding the small prime divisors
is nonnegative and bounded by the cutoff times the number of small primes. -/
theorem centralBinom_smooth_first_total_error (X : ℕ) :
    0≤binomialDistinctPrimeTotal 0 X-smoothDyadicFirstTotal X ∧
      binomialDistinctPrimeTotal 0 X-smoothDyadicFirstTotal X≤(X:ℝ)*Nat.primeCounting X.sqrt := by
  let d := fun k : ℕ => (((Nat.centralBinom (k/2)).primeFactors.filter (·≤X.sqrt)).card:ℝ)
  have hcell (k : ℕ) (hk : k∈range X) :
      ((Nat.centralBinom (k/2)).primeFactors.card : ℝ) -
        (2*(smoothIntegerCount (k/2) X.sqrt : ℝ) - smoothIntegerCount (2*(k/2)) X.sqrt) = d k := by
    have hsmall : 2*(k/2)<(X.sqrt+1)^2 := (Nat.mul_div_le k 2).trans_lt ((mem_range.mp hk).trans
      (Nat.lt_succ_sqrt' X))
    have he := smoothIntegerCount_centralBinom_large_factors (k/2) X.sqrt hsmall
    have hc := card_filter_add_card_filter_not (s := (Nat.centralBinom (k/2)).primeFactors) (p := (X.sqrt<·))
    simp only [not_lt] at hc
    dsimp only [d]
    exact_mod_cast (show (↑(Nat.centralBinom (k/2)).primeFactors.card:ℤ)-
        (2*(smoothIntegerCount (k/2) X.sqrt:ℤ)-smoothIntegerCount (2*(k/2)) X.sqrt) =
        (((Nat.centralBinom (k/2)).primeFactors.filter (·≤X.sqrt)).card:ℤ) by omega)
  have he : binomialDistinctPrimeTotal 0 X - smoothDyadicFirstTotal X=∑ k ∈ range X, d k := by
    simp only [binomialDistinctPrimeTotal,smoothDyadicFirstTotal,dyadicBinomialGcd,Nat.zero_add,pow_one]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [sub_sub_sub_cancel_right]
    exact hcell k hk
  rw [he]
  refine ⟨sum_nonneg (fun _ _ => Nat.cast_nonneg _),?_⟩
  calc
    _ ≤ ∑ _k ∈ range X, (Nat.primeCounting X.sqrt:ℝ) := by
      refine sum_le_sum fun k _ => ?_
      have hsub : (Nat.centralBinom (k/2)).primeFactors.filter (·≤X.sqrt) ⊆ Nat.primesLE X.sqrt := by
        intro p hp
        obtain ⟨hf,hy⟩ := mem_filter.mp hp
        exact Nat.mem_primesLE.mpr ⟨hy,Nat.prime_of_mem_primeFactors hf⟩
      have hh := card_le_card hsub
      rw [Nat.primesLE_card_eq_primeCounting] at hh
      dsimp only [d]
      exact_mod_cast hh
    _ = _ := by simp

/-- The distinct-prime criterion can be tested using only smooth counts on the
single set of primes below the square root of each outer cutoff. -/
theorem riemannHypothesis_iff_smoothDyadicFirstTotal :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/2<b → b<1 → ∃ C : ℝ, ∀ X : ℕ, 1≤X →
      |smoothDyadicFirstTotal X|≤C*(X:ℝ)^(b+1) := by
  rw [riemannHypothesis_iff_binomialDistinctPrimeTotal 0]
  have hcmp (b : ℝ) (hb : 1/2<b) (X : ℕ) (hx : 1≤X) :
      |binomialDistinctPrimeTotal 0 X-smoothDyadicFirstTotal X|≤(X:ℝ)^(b+1) := by
    obtain ⟨hl,hu⟩ := centralBinom_smooth_first_total_error X
    have hcount : Nat.primeCounting X.sqrt≤X.sqrt := by
      rw [← Nat.primesLE_card_eq_primeCounting,Nat.primesLE_eq_filter_Icc_one]
      exact (card_filter_le ..).trans (by simp)
    have hr : (X.sqrt:ℝ)≤(X:ℝ)^b := by
      apply Real.nat_sqrt_le_real_sqrt.trans
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) hb.le
    rw [abs_of_nonneg hl,Real.rpow_add_one (show (X:ℝ)≠0 by positivity),mul_comm ((X:ℝ)^b)]
    exact hu.trans (mul_le_mul_of_nonneg_left ((show (Nat.primeCounting X.sqrt:ℝ)≤X.sqrt by exact_mod_cast hcount).trans hr)
      (Nat.cast_nonneg _))
  constructor <;> intro h b hb hb1 <;> obtain ⟨C,hC⟩ := h b hb hb1 <;> refine ⟨1+C,fun X hx => ?_⟩
  · have he := abs_sub_le (smoothDyadicFirstTotal X) (binomialDistinctPrimeTotal 0 X) 0
    simp only [sub_zero] at he
    rw [abs_sub_comm] at he
    exact (he.trans (add_le_add (hcmp b hb X hx) (hC X hx))).trans_eq (by ring)
  · have he := abs_sub_le (binomialDistinctPrimeTotal 0 X) (smoothDyadicFirstTotal X) 0
    simp only [sub_zero] at he
    exact (he.trans (add_le_add (hcmp b hb X hx) (hC X hx))).trans_eq (by ring)

#print axioms centralBinom_smooth_first_total_error
#print axioms riemannHypothesis_iff_smoothDyadicFirstTotal

#print axioms smoothIntegerCount_centralBinom_large_factors

end GaloisForLFunctions.ExceptionalLayerTheory
