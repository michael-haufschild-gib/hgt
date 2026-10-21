import GaloisForLFunctions.BezoutValuationIncidence.OmittedResidueClassLawOfThePrimeRow

/-!
# The cross-scale coupling of a fixed prime packet with the prime block

Let `c` be a row supported on a fixed finite set `S` of primes and let `c'_Q = Λ · 1_{(Q, 2Q]}` be the
prime block at scale `Q`. The third-order cross-scale law writes the fluctuation part of their pronic
Gram form as

`B + m R' + β H' = (π²/72) S' Σ_p c(p)(p² - 1)/p³ + Σ_p (c(p)/p) Λ_p(c') + O(Σ|c| p³ Σ |c'|/n⁴)`,

where the first term is the main term of a row equidistributed in all residue classes. For the prime
block, `Q S' → 1/2` (the prime number theorem, through the classes modulo `2`) and the omitted
residue class law gives `Q Λ_p(c'_Q) → -π²(p² - 1)²/(144 p² (p - 1))`. The two combine to

`Q (B + m R' + β H') → -(π²/144) Σ_{p ∈ S} c(p) (1 - 1/p²)`
(`tendsto_mul_rowBilinear_primeWindowRow`).

So against the actual prime block the coupling of a prime packet is the equidistributed main term
multiplied by `-p` at each prime: the class `0`, which the primes omit, reverses its sign. A positive
packet couples negatively, with weight `1 - p^{-2}` independent of the size of `p`. This is a law at
fixed small scale; it says nothing about packets whose primes grow with `Q`.
-/

open Finset Filter Topology
open ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

theorem tendsto_log_two_mul_div : Tendsto (fun Q : ℕ => Real.log (2 * (Q : ℝ)) / Q) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
  have h2 := h.const_mul 2
  simp only [mul_zero] at h2
  refine h2.congr' (eventually_ge_atTop 1 |>.mono fun Q hQ => ?_)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  simp only [Function.comp_apply, pow_one, add_zero, one_mul]
  field_simp

theorem sum_Icc_primeWindowRow_eq (Q : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 (2 * Q), primeWindowRow Q n * f n = ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n * f n := by
  have hsub : Ioc Q (2 * Q) ⊆ Icc 1 (2 * Q) := fun n hn => by
    rw [mem_Ioc] at hn; rw [mem_Icc]; omega
  rw [← sum_subset hsub fun n hn hn' => by
    have : ¬ (Q < n ∧ n ≤ 2 * Q) := fun h => hn' (mem_Ioc.mpr h)
    simp [primeWindowRow, this]]
  refine sum_congr rfl fun n hn => ?_
  rw [mem_Ioc] at hn
  simp [primeWindowRow, hn.1, hn.2]

/-- **The prime number theorem on the dyadic window**, `Q Σ_{Q<n≤2Q} Λ(n)/n² → 1/2`, read off the two
classes modulo `2`. -/
theorem tendsto_mul_sum_primeWindowRow_div_sq :
    Tendsto (fun Q : ℕ => (Q : ℝ) * ∑ n ∈ Icc 1 (2 * Q), primeWindowRow Q n / (n : ℝ) ^ 2)
      atTop (𝓝 (1 / 2)) := by
  have hsplit : ∀ Q : ℕ, ∑ n ∈ Icc 1 (2 * Q), primeWindowRow Q n / (n : ℝ) ^ 2 =
      primeClassMass 2 0 Q + primeClassMass 2 1 Q := by
    intro Q
    have h := sum_Icc_primeWindowRow_eq Q (fun n => 1 / (n : ℝ) ^ 2)
    simp only [mul_one_div] at h
    rw [h, primeClassMass, primeClassMass, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · simp [h0]
    · simp [h1]
  have h1 := tendsto_mul_primeClassMass_sub Nat.prime_two one_pos one_lt_two
  have hW := tendsto_mul_dyadicInverseSquareMass
  have hsum := (tendsto_mul_primeClassMass_zero Nat.prime_two).add (h1.add hW)
  rw [zero_add, zero_add] at hsum
  refine hsum.congr fun Q => ?_
  rw [hsplit]
  norm_num
  ring

/-- **The coupling of a fixed prime packet with the prime block.** For a row `c` supported on a finite
set `S` of primes, `Q (B + m R' + β H') → -(π²/144) Σ_{p ∈ S} c(p)(p² - 1)/p²` against
`c'_Q = Λ · 1_{(Q, 2Q]}`. -/
theorem tendsto_mul_rowBilinear_primeWindowRow {c : ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ d, c d ≠ 0 → d ∈ S) (hSp : ∀ p ∈ S, p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * (rowBilinear (2 * Q) c (primeWindowRow Q) +
        rowMean (2 * Q) c * vonMangoldtReadout (2 * Q) (primeWindowRow Q) +
        rowBeta (2 * Q) c * finiteHarmonicSum (2 * Q) (primeWindowRow Q))) atTop
      (𝓝 (-(Real.pi ^ 2 / 144 * ∑ p ∈ S, c p * ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2))) := by
  have hcP : ∀ d, c d ≠ 0 → d.Prime := fun d hd => hSp d (hS d hd)
  -- from some horizon on, `S ⊆ [1, 2Q]`
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q → S ⊆ Icc 1 (2 * Q) :=
    ⟨S.sup id, fun Q hQ p hp => by
      rw [mem_Icc]
      exact ⟨(hSp p hp).one_lt.le, by have := le_sup (f := id) hp; simp at this; omega⟩⟩
  set L : ℕ → ℝ := fun p => -(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)))
  -- the main term
  have hmain : Tendsto (fun Q : ℕ => (Q : ℝ) * equidistributedMain (2 * Q) c (primeWindowRow Q))
      atTop (𝓝 (Real.pi ^ 2 / 72 * (1 / 2) * ∑ d ∈ S, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3)) := by
    have h := (tendsto_mul_sum_primeWindowRow_div_sq.const_mul (Real.pi ^ 2 / 72)).mul_const
      (∑ d ∈ S, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3)
    refine h.congr' (eventually_ge_atTop Q₀ |>.mono fun Q hQ => ?_)
    have hr : ∑ d ∈ Icc 1 (2 * Q), c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3 =
        ∑ d ∈ S, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3 :=
      (sum_subset (hQ₀ Q hQ) fun d _ hd => by
        have : c d = 0 := by by_contra h; exact hd (hS d h)
        simp [this]).symm
    dsimp only
    rw [equidistributedMain, hr]; ring
  -- the kernel statistics
  have hker : Tendsto (fun Q : ℕ => (Q : ℝ) * ∑ d ∈ Icc 1 (2 * Q),
      c d / d * kernelStatistic (2 * Q) (primeWindowRow Q) d) atTop (𝓝 (∑ p ∈ S, c p / p * L p)) := by
    have h := tendsto_finsetSum S fun p hp =>
      (tendsto_mul_kernelStatistic_primeWindowRow (hSp p hp)).const_mul (c p / p)
    refine h.congr' (eventually_ge_atTop Q₀ |>.mono fun Q hQ => ?_)
    have hr : ∑ d ∈ Icc 1 (2 * Q), c d / d * kernelStatistic (2 * Q) (primeWindowRow Q) d =
        ∑ d ∈ S, c d / d * kernelStatistic (2 * Q) (primeWindowRow Q) d :=
      (sum_subset (hQ₀ Q hQ) fun d _ hd => by
        have : c d = 0 := by by_contra h; exact hd (hS d h)
        simp [this]).symm
    dsimp only
    rw [hr, mul_sum]
    exact sum_congr rfl fun p _ => by ring
  -- the fourth-order error
  set C₃ := ∑ d ∈ S, |c d| * (d : ℝ) ^ 3
  have herr : Tendsto (fun Q : ℕ => (Q : ℝ) * (6 * (∑ d ∈ Icc 1 (2 * Q), |c d| * (d : ℝ) ^ 3) *
      ∑ n ∈ Icc 1 (2 * Q), |primeWindowRow Q n| / (n : ℝ) ^ 4)) atTop (𝓝 0) := by
    have hb : ∀ Q : ℕ, Q₀ ≤ Q → 1 ≤ Q → 0 ≤ (Q : ℝ) * (6 * (∑ d ∈ Icc 1 (2 * Q), |c d| * (d : ℝ) ^ 3) *
        ∑ n ∈ Icc 1 (2 * Q), |primeWindowRow Q n| / (n : ℝ) ^ 4) ∧
        (Q : ℝ) * (6 * (∑ d ∈ Icc 1 (2 * Q), |c d| * (d : ℝ) ^ 3) *
          ∑ n ∈ Icc 1 (2 * Q), |primeWindowRow Q n| / (n : ℝ) ^ 4) ≤
          6 * C₃ * (Real.log (2 * (Q : ℝ)) / Q) := by
      intro Q hQ hQ1
      have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
      have hC : ∑ d ∈ Icc 1 (2 * Q), |c d| * (d : ℝ) ^ 3 = C₃ := by
        rw [← sum_subset (hQ₀ Q hQ) fun d _ hd => by
          have : c d = 0 := by by_contra h; exact hd (hS d h)
          simp [this]]
      have hC0 : 0 ≤ C₃ := sum_nonneg fun d _ => by positivity
      have hlog0 : 0 ≤ Real.log (2 * (Q : ℝ)) :=
        Real.log_nonneg (by have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
                            linarith)
      have hrow : ∑ n ∈ Icc 1 (2 * Q), |primeWindowRow Q n| / (n : ℝ) ^ 4 =
          ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n * (1 / (n : ℝ) ^ 4) := by
        rw [← sum_Icc_primeWindowRow_eq]
        refine sum_congr rfl fun n _ => ?_
        have : 0 ≤ primeWindowRow Q n := by
          unfold primeWindowRow; split_ifs <;> simp [vonMangoldt_nonneg]
        rw [abs_of_nonneg this]; ring
      have hsum : ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n * (1 / (n : ℝ) ^ 4) ≤
          Real.log (2 * Q) / (Q : ℝ) ^ 3 := by
        have hterm : ∀ n ∈ Ioc Q (2 * Q), vonMangoldt n * (1 / (n : ℝ) ^ 4) ≤
            Real.log (2 * Q) / (Q : ℝ) ^ 4 := by
          intro n hn
          rw [mem_Ioc] at hn
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hn.1.le
          have hn2 : (n : ℝ) ≤ 2 * Q := by exact_mod_cast hn.2
          rw [mul_one_div]
          calc vonMangoldt n / (n : ℝ) ^ 4 ≤ Real.log (2 * Q) / (n : ℝ) ^ 4 :=
                div_le_div_of_nonneg_right (vonMangoldt_le_log.trans (Real.log_le_log hn0 hn2))
                  (by positivity)
            _ ≤ Real.log (2 * Q) / (Q : ℝ) ^ 4 :=
                div_le_div_of_nonneg_left hlog0 (by positivity) (pow_le_pow_left₀ hQ0.le hQn 4)
        calc _ ≤ ∑ _n ∈ Ioc Q (2 * Q), Real.log (2 * Q) / (Q : ℝ) ^ 4 := sum_le_sum hterm
          _ = Real.log (2 * Q) / (Q : ℝ) ^ 3 := by
              rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * Q - Q = Q by omega]; field_simp
      have hnn : 0 ≤ ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n * (1 / (n : ℝ) ^ 4) :=
        sum_nonneg fun n _ => mul_nonneg vonMangoldt_nonneg (by positivity)
      rw [hC, hrow]
      refine ⟨by positivity, ?_⟩
      calc (Q : ℝ) * (6 * C₃ * ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n * (1 / (n : ℝ) ^ 4))
          ≤ (Q : ℝ) * (6 * C₃ * (Real.log (2 * Q) / (Q : ℝ) ^ 3)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) hQ0.le
        _ ≤ 6 * C₃ * (Real.log (2 * (Q : ℝ)) / Q) := by
            have h1 : (Q : ℝ) * (Real.log (2 * Q) / (Q : ℝ) ^ 3) ≤ Real.log (2 * Q) / Q := by
              rw [show (Q : ℝ) * (Real.log (2 * Q) / (Q : ℝ) ^ 3) = Real.log (2 * Q) / Q / Q by
                field_simp]
              exact div_le_self (div_nonneg hlog0 hQ0.le) (by exact_mod_cast hQ1)
            nlinarith
    exact squeeze_zero' ((eventually_ge_atTop (max Q₀ 1)).mono fun Q hQ =>
        (hb Q (le_of_max_le_left hQ) (le_of_max_le_right hQ)).1)
      ((eventually_ge_atTop (max Q₀ 1)).mono fun Q hQ =>
        (hb Q (le_of_max_le_left hQ) (le_of_max_le_right hQ)).2)
      (by simpa using tendsto_log_two_mul_div.const_mul (6 * C₃))
  -- assemble
  have hrest : Tendsto (fun Q : ℕ => (Q : ℝ) * (rowBilinear (2 * Q) c (primeWindowRow Q) +
      rowMean (2 * Q) c * vonMangoldtReadout (2 * Q) (primeWindowRow Q) +
      rowBeta (2 * Q) c * finiteHarmonicSum (2 * Q) (primeWindowRow Q) -
      equidistributedMain (2 * Q) c (primeWindowRow Q) -
      ∑ d ∈ Icc 1 (2 * Q), c d / d * kernelStatistic (2 * Q) (primeWindowRow Q) d)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun Q => ?_) herr
    rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left
      (abs_rowBilinear_sub_kernelStatistic_le (2 * Q) (primeWindowRow Q) hcP) (Nat.cast_nonneg Q)
  have htot := (hmain.add hker).add hrest
  have hval : Real.pi ^ 2 / 72 * (1 / 2) * ∑ d ∈ S, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3 +
      ∑ p ∈ S, c p / p * L p + 0 =
      -(Real.pi ^ 2 / 144 * ∑ p ∈ S, c p * ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2) := by
    rw [add_zero, mul_sum, mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun p hp => ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hSp p hp).one_lt
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have : (p : ℝ) ≠ 0 := by positivity
    simp only [L]
    field_simp
    ring
  rw [← hval]
  refine htot.congr fun Q => ?_
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence
