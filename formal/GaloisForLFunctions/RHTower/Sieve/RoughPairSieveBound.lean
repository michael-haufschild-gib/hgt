import GaloisForLFunctions.RHTower.Sieve.MertensProductLower

/-!
# The bounding sum of the pair sieve, in Mertens terms

Composing the three previous steps — half the Euler product survives the truncation, the
two-dimensional Euler factor dominates the square of the classical one, and the classical product
dominates the exponential of the prime harmonic sum — gives a bounding sum at least

    (1/2) · exp(mertensS h − mertensS P₁)² · (shift correction) ,

which is the `(log h / log P₁)²` the short-interval argument needs.  The shift correction is a
product of `1 − 1/p` over the sifting primes dividing the shift, and since every sifting prime
exceeds `P₁` while their number is at most `log d / log P₁`, it is bounded below by an absolute
constant in the range where the argument is applied.
-/

namespace RHTower.Sieve

open Finset

/-- **The bounding sum of the pair sieve, in Mertens terms.** -/
theorem selbergBoundingSum_ge_mertens (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (d k : ℕ)
    {z : ℝ} (hz : 1 ≤ z) (hh1 : 1 ≤ h) (hP₁h : P₁ ≤ h) (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1
        * (∑ p ∈ rangePrimes P₁ h, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        + Real.log 2 ≤ (k : ℝ)) :
    (1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ 2
        * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)))
      ≤ SelbergSieve.selbergBoundingSum (roughPairSieve Y hP₁ h d hz) := by
  classical
  have hp3 : ∀ p ∈ rangePrimes P₁ h, 3 ≤ p := by
    intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    omega
  -- the shift correction is nonnegative
  have hC0 : (0 : ℝ) ≤ ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d),
      (((p : ℝ) - 1) / (p : ℝ)) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by
      have := hp3 p (Finset.mem_filter.1 hp).1
      exact_mod_cast this
    exact div_nonneg (by linarith) (by linarith)
  -- the Mertens product from below
  have hmert := prod_rangePrimes_ge P₁ h hP₁h
  have hexp0 : (0 : ℝ) < Real.exp (mertensS h - mertensS P₁) := Real.exp_pos _
  have hsq : Real.exp (mertensS h - mertensS P₁) ^ 2
      ≤ (∏ p ∈ rangePrimes P₁ h, ((p : ℝ) / ((p : ℝ) - 1))) ^ 2 :=
    pow_le_pow_left₀ hexp0.le hmert 2
  -- the two-dimensional Euler factor
  have heuler := prod_pairFactor_ge d hp3
  have hstep : Real.exp (mertensS h - mertensS P₁) ^ 2
        * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))
      ≤ ∏ p ∈ rangePrimes P₁ h,
          (pairClassCount d p / ((p : ℝ) - pairClassCount d p) + 1) := by
    refine le_trans (mul_le_mul_of_nonneg_right hsq hC0) heuler
  refine le_trans (mul_le_mul_of_nonneg_left hstep (by norm_num)) ?_
  exact selbergBoundingSum_roughPairSieve_ge Y hP₁ d k hz hh1 hlev hk

/-- Weierstrass' product inequality. -/
theorem one_sub_sum_le_prod_one_sub {s : Finset ℕ} {f : ℕ → ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) : 1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have h0a := h0 a (Finset.mem_insert_self a t)
      have h1a := h1 a (Finset.mem_insert_self a t)
      have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      nlinarith [ih', h0a, h1a,
        Finset.sum_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))]

/-- **The shift correction is bounded below.**  Every sifting prime exceeds `P₁`, and their number
is at most `log D / log P₁`. -/
theorem prod_shiftCorrection_ge (P₁ h d : ℕ) (hP₁ : 2 ≤ P₁) (hd : 1 ≤ d) {D : ℕ} (hdD : d ≤ D) :
    1 - Real.log D / (Real.log P₁ * (P₁ : ℝ))
      ≤ ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)) := by
  classical
  have hP₁R : (2 : ℝ) ≤ (P₁ : ℝ) := by exact_mod_cast hP₁
  have hP₁1 : (1 : ℝ) < (P₁ : ℝ) := by linarith
  have hlogP : 0 < Real.log (P₁ : ℝ) := Real.log_pos hP₁1
  have hge : ∀ p ∈ rangePrimes P₁ h, (P₁ : ℝ) ≤ (p : ℝ) := by
    intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have : P₁ ≤ p := by omega
    exact_mod_cast this
  set F : Finset ℕ := (rangePrimes P₁ h).filter (fun p => p ∣ d) with hF
  have hmem : ∀ p ∈ F, (P₁ : ℝ) ≤ (p : ℝ) := by
    intro p hp
    exact hge p (Finset.mem_filter.1 hp).1
  have hrw : ∏ p ∈ F, (((p : ℝ) - 1) / (p : ℝ)) = ∏ p ∈ F, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith [hmem p hp, hP₁R]
    field_simp
  rw [hrw]
  refine le_trans ?_ (one_sub_sum_le_prod_one_sub (f := fun p => 1 / (p : ℝ))
    (fun p _ => by positivity) (fun p hp => ?_))
  · have hcard : ((F.card : ℕ) : ℝ) ≤ Real.log D / Real.log P₁ := by
      have hdvd : (∏ p ∈ F, p) ∣ d := by
        refine Finset.prod_primes_dvd d (fun p hp => ?_) (fun p hp => ?_)
        · exact (rangePrimes_prime (Finset.mem_filter.1 hp).1).prime
        · exact (Finset.mem_filter.1 hp).2
      have hge' : ∀ p ∈ F, P₁ ≤ p := by
        intro p hp
        have hR := hmem p hp
        exact_mod_cast hR
      have hpow : P₁ ^ F.card ≤ d := by
        calc P₁ ^ F.card = ∏ _p ∈ F, P₁ := by rw [Finset.prod_const]
          _ ≤ ∏ p ∈ F, p := Finset.prod_le_prod' hge'
          _ ≤ d := Nat.le_of_dvd (by omega) hdvd
      have hpowR : ((P₁ : ℝ)) ^ F.card ≤ (D : ℝ) := by
        have h1 : ((P₁ ^ F.card : ℕ) : ℝ) ≤ ((D : ℕ) : ℝ) := by
          exact_mod_cast le_trans hpow hdD
        calc ((P₁ : ℝ)) ^ F.card = ((P₁ ^ F.card : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (D : ℝ) := h1
      have hpos : (0 : ℝ) < ((P₁ : ℝ)) ^ F.card := by positivity
      have hlog := Real.log_le_log hpos hpowR
      rw [Real.log_pow] at hlog
      rw [le_div_iff₀ hlogP]
      exact hlog
    have hsum : ∑ p ∈ F, 1 / (p : ℝ) ≤ ((F.card : ℕ) : ℝ) * (1 / (P₁ : ℝ)) := by
      have hterm : ∀ p ∈ F, 1 / (p : ℝ) ≤ 1 / (P₁ : ℝ) := by
        intro p hp
        exact one_div_le_one_div_of_le (by linarith) (hmem p hp)
      have := Finset.sum_le_sum hterm
      rwa [Finset.sum_const, nsmul_eq_mul] at this
    have hP₁0 : (0 : ℝ) < (P₁ : ℝ) := by linarith
    have hfinal : ∑ p ∈ F, 1 / (p : ℝ) ≤ Real.log D / (Real.log P₁ * (P₁ : ℝ)) := by
      refine hsum.trans ?_
      rw [div_mul_eq_div_div]
      rw [mul_one_div]
      exact (div_le_div_iff_of_pos_right hP₁0).mpr hcard
    linarith
  · have h2 := hmem p hp
    rw [div_le_one (by linarith)]
    linarith

end RHTower.Sieve
