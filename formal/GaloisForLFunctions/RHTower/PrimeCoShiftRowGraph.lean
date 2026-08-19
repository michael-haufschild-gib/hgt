import GaloisForLFunctions.RHTower.PrimeCoShiftModel

/-!
# The graph of the all-prime co-shift row

The all-prime row `R_s x = (T_{p,s}x)_p`, `T_{p,s} = V_p^* - p^{-s}`, is an unbounded operator on
`H = ℓ²(ℕ≥1)`.  This module computes its graph exactly.

The pure co-shift energy is an `ω`-weighted energy: Tonelli and unique factorization give

```
W(x) = ∑_p ‖V_p^* x‖² = ∑_n ω(n)|x_n|²                                (4)
```

where `ω(n)` is the number of distinct prime divisors of `n`.  Since the prime zeta value
`A_σ = ∑_p p^{-2σ}` is finite for `σ > 1/2`, the row energy and `W` differ by a bounded multiple of
`‖x‖²` in both directions, so the graph domain is exactly the `ω`-weighted space and the graph norm
is equivalent to `∑_n (1+ω(n))|x_n|²`.

All identities are stated in `ℝ≥0∞`, hence hold unconditionally, with no summability hypothesis.
-/

open scoped ENNReal NNReal
open RHTower

namespace RHTower.PrimeCoShift

noncomputable section

/-! ### Prime divisors as a finite set of `Nat.Primes` -/

/-- The prime factors of a positive integer, embedded into `Nat.Primes`. -/
def primeDivisorsEmb (k : ℕ+) : {q : ℕ // q ∈ (k : ℕ).primeFactors} ↪ Nat.Primes where
  toFun q := ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    simpa using congrArg (fun z : Nat.Primes => (z : ℕ)) h

/-- The prime divisors of a positive integer, as a `Finset Nat.Primes`. -/
def primeDivisors (k : ℕ+) : Finset Nat.Primes :=
  (k : ℕ).primeFactors.attach.map (primeDivisorsEmb k)

theorem mem_primeDivisors {k : ℕ+} {p : Nat.Primes} :
    p ∈ primeDivisors k ↔ (p : ℕ) ∣ (k : ℕ) := by
  simp only [primeDivisors, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (Nat.mem_primeFactors.mp hq).2.1
  · intro hd
    exact ⟨(p : ℕ), Nat.mem_primeFactors.mpr ⟨p.property, hd, (k.property).ne'⟩, rfl⟩

/-- `ω(n)`, the number of distinct prime divisors of a positive integer. -/
def omegaPNat (n : ℕ+) : ℕ := (n : ℕ).primeFactors.card

theorem card_primeDivisors (k : ℕ+) : (primeDivisors k).card = omegaPNat k := by
  simp [primeDivisors, omegaPNat]

/-- **Prime-shift double counting.**  Summing any `ℝ≥0∞`-valued weight over all pairs
`(p, m)` with `p` prime counts each index `n` exactly `ω(n)` times. -/
theorem tsum_prime_shift (G : ℕ+ → ℝ≥0∞) :
    ∑' p : Nat.Primes, ∑' m : ℕ+, G (primePNat p * m)
      = ∑' k : ℕ+, (omegaPNat k : ℝ≥0∞) * G k := by
  classical
  have step1 : ∀ p : Nat.Primes, ∑' m : ℕ+, G (primePNat p * m)
      = ∑' k : ℕ+, (if (p : ℕ) ∣ (k : ℕ) then G k else 0) := by
    intro p
    have hinj : Function.Injective (fun m : ℕ+ => primePNat p * m) := mulLeft_injective _
    have hsupp : Function.support (fun k : ℕ+ => (if (p : ℕ) ∣ (k : ℕ) then G k else 0))
        ⊆ Set.range (fun m : ℕ+ => primePNat p * m) := by
      intro k hk
      simp only [Function.mem_support] at hk
      by_cases hd : (p : ℕ) ∣ (k : ℕ)
      · obtain ⟨c, hc⟩ := hd
        have hcpos : 0 < c := by
          rcases Nat.eq_zero_or_pos c with h0 | h0
          · exfalso; rw [h0, Nat.mul_zero] at hc; exact absurd hc (k.property).ne'
          · exact h0
        exact ⟨⟨c, hcpos⟩, PNat.coe_injective (by simpa [primePNat] using hc.symm)⟩
      · exact absurd (if_neg hd) hk
    have hbij := hinj.tsum_eq
      (f := fun k : ℕ+ => (if (p : ℕ) ∣ (k : ℕ) then G k else 0)) hsupp
    rw [← hbij]
    refine tsum_congr fun m => ?_
    rw [if_pos]
    exact ⟨(m : ℕ), rfl⟩
  simp only [step1]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rw [tsum_eq_sum (s := primeDivisors k) (fun p hp => by
    rw [if_neg]; exact fun hd => hp (mem_primeDivisors.mpr hd))]
  rw [Finset.sum_congr rfl (fun p hp => by rw [if_pos (mem_primeDivisors.mp hp)])]
  rw [Finset.sum_const, card_primeDivisors]
  simp

/-! ### Coordinate energy of an `ℓ²` vector -/

theorem summable_norm_sq (y : H) : Summable fun n : ℕ+ => ‖y n‖ ^ 2 := by
  have h := (lp.memℓp y).summable (p := 2) (by norm_num)
  refine h.congr ?_
  intro n
  norm_num

theorem norm_sq_eq_tsum (y : H) : ‖y‖ ^ 2 = ∑' n : ℕ+, ‖y n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ+ => ℂ) (by norm_num) y
  simp only [ENNReal.toReal_ofNat] at h
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num] at h
  simpa [Real.rpow_natCast] using h

theorem summable_nnnorm_sq (y : H) : Summable fun n : ℕ+ => ‖y n‖₊ ^ 2 := by
  rw [← NNReal.summable_coe]
  simpa using summable_norm_sq y

/-- The `ℓ²` norm identity in `ℝ≥0∞`. -/
theorem enorm_sq_eq_tsum (y : H) :
    ((‖y‖₊ : ℝ≥0∞)) ^ 2 = ∑' n : ℕ+, ((‖y n‖₊ : ℝ≥0∞)) ^ 2 := by
  have hnn : ‖y‖₊ ^ 2 = ∑' n : ℕ+, ‖y n‖₊ ^ 2 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_tsum]
    push_cast
    exact norm_sq_eq_tsum y
  rw [← ENNReal.coe_pow, hnn, ENNReal.coe_tsum (summable_nnnorm_sq y)]
  simp [ENNReal.coe_pow]

/-! ### The three energies -/

/-- The pure co-shift energy `W(x) = ∑_p ‖V_p^* x‖²`. -/
def coShiftEnergy (x : H) : ℝ≥0∞ :=
  ∑' p : Nat.Primes, ((‖primeCoShift (primePNat p) x‖₊ : ℝ≥0∞)) ^ 2

/-- The `ω`-weighted coordinate energy `∑_n ω(n)|x_n|²`. -/
def omegaEnergy (x : H) : ℝ≥0∞ :=
  ∑' k : ℕ+, (omegaPNat k : ℝ≥0∞) * ((‖x k‖₊ : ℝ≥0∞)) ^ 2

/-- The row energy `‖R_s x‖² = ∑_p ‖T_{p,s} x‖²`. -/
def rowEnergy (s : ℂ) (x : H) : ℝ≥0∞ :=
  ∑' p : Nat.Primes, ((‖rowOp s p x‖₊ : ℝ≥0∞)) ^ 2

/-- **The exact co-shift energy identity.**  Tonelli plus unique factorization. -/
theorem coShiftEnergy_eq_omegaEnergy (x : H) : coShiftEnergy x = omegaEnergy x := by
  rw [coShiftEnergy, omegaEnergy]
  rw [← tsum_prime_shift (fun k => ((‖x k‖₊ : ℝ≥0∞)) ^ 2)]
  refine tsum_congr fun p => ?_
  rw [enorm_sq_eq_tsum]
  rfl

/-! ### The prime zeta energy -/

/-- `A_s = ∑_p |p^{-s}|²`, the prime zeta value at `2 Re s`. -/
def primeZetaEnergy (s : ℂ) : ℝ≥0∞ :=
  ∑' p : Nat.Primes, ((‖((p : ℕ) : ℂ) ^ (-s)‖₊ : ℝ≥0∞)) ^ 2

theorem summable_prime_rpow {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ (2 * σ))⁻¹ := by
  have hbase : Summable fun n : ℕ => (((n : ℝ)) ^ (2 * σ))⁻¹ := by
    rw [Real.summable_nat_rpow_inv]; linarith
  exact hbase.comp_injective (fun a b h => Subtype.ext h)

theorem primeZetaEnergy_ne_top {s : ℂ} (hs : 1 / 2 < s.re) : primeZetaEnergy s ≠ ⊤ := by
  have hsum : Summable fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-s)‖₊ ^ 2 := by
    rw [← NNReal.summable_coe]
    refine (summable_prime_rpow hs).congr fun p => ?_
    have hp : 0 < (p : ℕ) := p.property.pos
    have hb : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    rw [Complex.norm_natCast_cpow_of_pos hp]
    simp only [Complex.neg_re]
    rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul hb, ← Real.rpow_neg hb]
    congr 1
    ring
  rw [primeZetaEnergy]
  have : ∑' p : Nat.Primes, ((‖((p : ℕ) : ℂ) ^ (-s)‖₊ : ℝ≥0∞)) ^ 2
      = ((∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-s)‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_tsum hsum]
    simp
  rw [this]
  exact ENNReal.coe_ne_top

/-! ### Two-sided comparison of the row energy and the `ω` energy -/

theorem enn_sq_add_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  rcases eq_or_ne a ⊤ with ha | ha
  · subst ha
    rcases eq_or_ne b 0 with hb | hb <;> simp [ENNReal.top_pow]
  rcases eq_or_ne b ⊤ with hb | hb
  · subst hb
    simp [ENNReal.top_pow]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  rw [← ENNReal.coe_add, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_pow]
  rw [show ((2 : ℝ≥0∞)) = ((2 : ℝ≥0) : ℝ≥0∞) by simp]
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ))]

theorem norm_scalar_smul (s : ℂ) (p : Nat.Primes) (x : H) :
    (‖(((p : ℕ) : ℂ) ^ (-s)) • x‖₊ : ℝ≥0∞)
      = (‖((p : ℕ) : ℂ) ^ (-s)‖₊ : ℝ≥0∞) * (‖x‖₊ : ℝ≥0∞) := by
  rw [nnnorm_smul]
  simp

/-- **Row energy dominated by the co-shift energy.** -/
theorem rowEnergy_le (s : ℂ) (x : H) :
    rowEnergy s x ≤ 2 * coShiftEnergy x + 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  have hterm : ∀ p : Nat.Primes, ((‖rowOp s p x‖₊ : ℝ≥0∞)) ^ 2
      ≤ 2 * ((‖primeCoShift (primePNat p) x‖₊ : ℝ≥0∞)) ^ 2
        + 2 * (((‖((p : ℕ) : ℂ) ^ (-s)‖₊ : ℝ≥0∞)) ^ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2) := by
    intro p
    have hsplit : rowOp s p x
        = primeCoShift (primePNat p) x - (((p : ℕ) : ℂ) ^ (-s)) • x := by
      simp [rowOp]
    have h1 : (‖rowOp s p x‖₊ : ℝ≥0∞)
        ≤ (‖primeCoShift (primePNat p) x‖₊ : ℝ≥0∞)
          + (‖(((p : ℕ) : ℂ) ^ (-s)) • x‖₊ : ℝ≥0∞) := by
      rw [hsplit]
      exact_mod_cast ENNReal.coe_le_coe.mpr (nnnorm_sub_le _ _)
    calc ((‖rowOp s p x‖₊ : ℝ≥0∞)) ^ 2
        ≤ ((‖primeCoShift (primePNat p) x‖₊ : ℝ≥0∞)
            + (‖(((p : ℕ) : ℂ) ^ (-s)) • x‖₊ : ℝ≥0∞)) ^ 2 := by
          exact pow_le_pow_left' h1 2
      _ ≤ 2 * ((‖primeCoShift (primePNat p) x‖₊ : ℝ≥0∞)) ^ 2
            + 2 * ((‖(((p : ℕ) : ℂ) ^ (-s)) • x‖₊ : ℝ≥0∞)) ^ 2 := enn_sq_add_le _ _
      _ = 2 * ((‖primeCoShift (primePNat p) x‖₊ : ℝ≥0∞)) ^ 2
            + 2 * (((‖((p : ℕ) : ℂ) ^ (-s)‖₊ : ℝ≥0∞)) ^ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2) := by
          rw [norm_scalar_smul, mul_pow]
  calc rowEnergy s x ≤ ∑' p : Nat.Primes, (2 * ((‖primeCoShift (primePNat p) x‖₊ : ℝ≥0∞)) ^ 2
        + 2 * (((‖((p : ℕ) : ℂ) ^ (-s)‖₊ : ℝ≥0∞)) ^ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2)) :=
        ENNReal.tsum_le_tsum hterm
    _ = 2 * coShiftEnergy x + 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_right]
        rw [coShiftEnergy, primeZetaEnergy]
        ring

/-- **Co-shift energy dominated by the row energy.** -/
theorem coShiftEnergy_le (s : ℂ) (x : H) :
    coShiftEnergy x ≤ 2 * rowEnergy s x + 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  have hterm : ∀ p : Nat.Primes, ((‖primeCoShift (primePNat p) x‖₊ : ℝ≥0∞)) ^ 2
      ≤ 2 * ((‖rowOp s p x‖₊ : ℝ≥0∞)) ^ 2
        + 2 * (((‖((p : ℕ) : ℂ) ^ (-s)‖₊ : ℝ≥0∞)) ^ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2) := by
    intro p
    have hsplit : primeCoShift (primePNat p) x
        = rowOp s p x + (((p : ℕ) : ℂ) ^ (-s)) • x := by
      simp [rowOp]
    have h1 : (‖primeCoShift (primePNat p) x‖₊ : ℝ≥0∞)
        ≤ (‖rowOp s p x‖₊ : ℝ≥0∞) + (‖(((p : ℕ) : ℂ) ^ (-s)) • x‖₊ : ℝ≥0∞) := by
      rw [hsplit]
      exact_mod_cast ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)
    calc ((‖primeCoShift (primePNat p) x‖₊ : ℝ≥0∞)) ^ 2
        ≤ ((‖rowOp s p x‖₊ : ℝ≥0∞) + (‖(((p : ℕ) : ℂ) ^ (-s)) • x‖₊ : ℝ≥0∞)) ^ 2 :=
          pow_le_pow_left' h1 2
      _ ≤ 2 * ((‖rowOp s p x‖₊ : ℝ≥0∞)) ^ 2
            + 2 * ((‖(((p : ℕ) : ℂ) ^ (-s)) • x‖₊ : ℝ≥0∞)) ^ 2 := enn_sq_add_le _ _
      _ = 2 * ((‖rowOp s p x‖₊ : ℝ≥0∞)) ^ 2
            + 2 * (((‖((p : ℕ) : ℂ) ^ (-s)‖₊ : ℝ≥0∞)) ^ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2) := by
          rw [norm_scalar_smul, mul_pow]
  calc coShiftEnergy x ≤ ∑' p : Nat.Primes, (2 * ((‖rowOp s p x‖₊ : ℝ≥0∞)) ^ 2
        + 2 * (((‖((p : ℕ) : ℂ) ^ (-s)‖₊ : ℝ≥0∞)) ^ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2)) :=
        ENNReal.tsum_le_tsum hterm
    _ = 2 * rowEnergy s x + 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_right]
        rw [rowEnergy, primeZetaEnergy]
        ring

/-! ### The graph domain and the graph norm -/

/-- The `(1+ω)`-weighted coordinate energy. -/
def graphWeightEnergy (x : H) : ℝ≥0∞ :=
  ∑' n : ℕ+, ((1 : ℝ≥0∞) + (omegaPNat n : ℝ≥0∞)) * ((‖x n‖₊ : ℝ≥0∞)) ^ 2

theorem graphWeightEnergy_eq (x : H) :
    graphWeightEnergy x = (‖x‖₊ : ℝ≥0∞) ^ 2 + omegaEnergy x := by
  rw [graphWeightEnergy, omegaEnergy, enorm_sq_eq_tsum, ← ENNReal.tsum_add]
  refine tsum_congr fun n => ?_
  rw [add_mul, one_mul]

/-- **Graph norm bounded by the weighted norm.** -/
theorem graphEnergy_le_weight (s : ℂ) (x : H) :
    (‖x‖₊ : ℝ≥0∞) ^ 2 + rowEnergy s x
      ≤ (2 + 2 * primeZetaEnergy s) * graphWeightEnergy x := by
  have h := rowEnergy_le s x
  rw [coShiftEnergy_eq_omegaEnergy] at h
  rw [graphWeightEnergy_eq]
  calc (‖x‖₊ : ℝ≥0∞) ^ 2 + rowEnergy s x
      ≤ (‖x‖₊ : ℝ≥0∞) ^ 2 + (2 * omegaEnergy x
          + 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2) := by
        exact add_le_add le_rfl h
    _ ≤ (2 + 2 * primeZetaEnergy s) * ((‖x‖₊ : ℝ≥0∞) ^ 2 + omegaEnergy x) := by
        rw [add_mul, mul_add, mul_add]
        have h1 : (‖x‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2 := by
          nth_rewrite 1 [← one_mul ((‖x‖₊ : ℝ≥0∞) ^ 2)]
          gcongr
          norm_num
        have h2 : 2 * omegaEnergy x ≤ 2 * omegaEnergy x := le_rfl
        have h3 : 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2
            ≤ 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2
              + 2 * primeZetaEnergy s * omegaEnergy x := le_self_add
        calc (‖x‖₊ : ℝ≥0∞) ^ 2 + (2 * omegaEnergy x
              + 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2)
            ≤ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2 + (2 * omegaEnergy x
              + (2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2
                + 2 * primeZetaEnergy s * omegaEnergy x)) := by
              exact add_le_add h1 (add_le_add h2 h3)
          _ = 2 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 2 * omegaEnergy x
              + (2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2
                + 2 * primeZetaEnergy s * omegaEnergy x) := by ring

/-- **Weighted norm bounded by the graph norm.** -/
theorem weight_le_graphEnergy (s : ℂ) (x : H) :
    graphWeightEnergy x
      ≤ (2 + 2 * primeZetaEnergy s) * ((‖x‖₊ : ℝ≥0∞) ^ 2 + rowEnergy s x) := by
  have h := coShiftEnergy_le s x
  rw [coShiftEnergy_eq_omegaEnergy] at h
  rw [graphWeightEnergy_eq]
  calc (‖x‖₊ : ℝ≥0∞) ^ 2 + omegaEnergy x
      ≤ (‖x‖₊ : ℝ≥0∞) ^ 2 + (2 * rowEnergy s x
          + 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2) := add_le_add le_rfl h
    _ ≤ (2 + 2 * primeZetaEnergy s) * ((‖x‖₊ : ℝ≥0∞) ^ 2 + rowEnergy s x) := by
        rw [add_mul, mul_add, mul_add]
        have h1 : (‖x‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2 := by
          nth_rewrite 1 [← one_mul ((‖x‖₊ : ℝ≥0∞) ^ 2)]
          gcongr
          norm_num
        have h3 : 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2
            ≤ 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2
              + 2 * primeZetaEnergy s * rowEnergy s x := le_self_add
        calc (‖x‖₊ : ℝ≥0∞) ^ 2 + (2 * rowEnergy s x
              + 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2)
            ≤ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2 + (2 * rowEnergy s x
              + (2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2
                + 2 * primeZetaEnergy s * rowEnergy s x)) :=
              add_le_add h1 (add_le_add le_rfl h3)
          _ = 2 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 2 * rowEnergy s x
              + (2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2
                + 2 * primeZetaEnergy s * rowEnergy s x) := by ring

/-- **The exact graph domain.**  A vector lies in the domain of the all-prime row iff its
`ω`-weighted coordinate energy is finite. -/
theorem rowEnergy_ne_top_iff {s : ℂ} (hs : 1 / 2 < s.re) (x : H) :
    rowEnergy s x ≠ ⊤ ↔ omegaEnergy x ≠ ⊤ := by
  have hA : primeZetaEnergy s ≠ ⊤ := primeZetaEnergy_ne_top hs
  have hx : (‖x‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ := by
    simp [← ENNReal.coe_pow]
  have hprod : 2 * primeZetaEnergy s * (‖x‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hA) hx
  constructor
  · intro h
    rw [← coShiftEnergy_eq_omegaEnergy]
    refine ne_top_of_le_ne_top ?_ (coShiftEnergy_le s x)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) h, hprod⟩
  · intro h
    refine ne_top_of_le_ne_top ?_ (rowEnergy_le s x)
    rw [coShiftEnergy_eq_omegaEnergy]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) h, hprod⟩

/-! ### The prime-supported non-closability sequence -/

/-- The constant vector on a finite set of indices. -/
def finsetVector (S : Finset ℕ+) (c : ℂ) : H := ∑ n ∈ S, lp.single 2 n c

theorem finsetVector_apply (S : Finset ℕ+) (c : ℂ) (m : ℕ+) :
    finsetVector S c m = if m ∈ S then c else 0 := by
  classical
  rw [finsetVector, lp.coeFn_sum]
  simp [lp.single_apply]

theorem norm_sq_finsetVector (S : Finset ℕ+) (c : ℂ) :
    ‖finsetVector S c‖ ^ 2 = S.card * ‖c‖ ^ 2 := by
  classical
  rw [norm_sq_eq_tsum]
  rw [tsum_eq_sum (s := S) (fun n hn => by rw [finsetVector_apply, if_neg hn]; simp)]
  rw [Finset.sum_congr rfl (fun n hn => by rw [finsetVector_apply, if_pos hn])]
  rw [Finset.sum_const, nsmul_eq_mul]

theorem omegaEnergy_finsetVector (S : Finset ℕ+) (c : ℂ) :
    omegaEnergy (finsetVector S c) = ∑ n ∈ S, (omegaPNat n : ℝ≥0∞) * (‖c‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  rw [omegaEnergy]
  rw [tsum_eq_sum (s := S) (fun n hn => by rw [finsetVector_apply, if_neg hn]; simp)]
  exact Finset.sum_congr rfl fun n hn => by rw [finsetVector_apply, if_pos hn]

theorem sum_finsetVector (S : Finset ℕ+) (c : ℂ) :
    ∑ n ∈ S, finsetVector S c n = S.card * c := by
  classical
  rw [Finset.sum_congr rfl (fun n hn => by rw [finsetVector_apply, if_pos hn])]
  rw [Finset.sum_const, nsmul_eq_mul]

theorem primePNat_injective : Function.Injective primePNat := by
  intro a b h
  exact Subtype.ext (congrArg (fun m : ℕ+ => (m : ℕ)) h)

theorem omegaPNat_primePNat (p : Nat.Primes) : omegaPNat (primePNat p) = 1 := by
  rw [omegaPNat]
  simp [primePNat, Nat.Prime.primeFactors p.property]

/-- The `ℓ²` energy of a constant vector on a finite index set, in `ℝ≥0∞`. -/
theorem enorm_sq_finsetVector (S : Finset ℕ+) (c : ℂ) :
    ((‖finsetVector S c‖₊ : ℝ≥0∞)) ^ 2 = (S.card : ℝ≥0∞) * ((‖c‖₊ : ℝ≥0∞)) ^ 2 := by
  classical
  rw [enorm_sq_eq_tsum]
  rw [tsum_eq_sum (s := S) (fun n hn => by rw [finsetVector_apply, if_neg hn]; simp)]
  have hterm : ∀ n ∈ S, ((‖finsetVector S c n‖₊ : ℝ≥0∞)) ^ 2 = ((‖c‖₊ : ℝ≥0∞)) ^ 2 := by
    intro n hn
    rw [finsetVector_apply, if_pos hn]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

theorem enorm_nat_inv (M : ℕ) (hM : 0 < M) :
    (‖((M : ℂ))⁻¹‖₊ : ℝ≥0∞) = ((M : ℝ≥0∞))⁻¹ := by
  rw [nnnorm_inv]
  rw [ENNReal.coe_inv (by simpa using (Nat.cast_ne_zero (R := ℝ≥0)).mpr hM.ne')]
  norm_num

/-- **The explicit prime-supported vectors.**  For every `M ≥ 1` there is a set of `M` distinct
primes and the corresponding uniform vector of total coefficient sum one, with square norm `1/M`
and `ω`-energy `1/M`. -/
theorem exists_prime_uniform_vector (M : ℕ) (hM : 0 < M) :
    ∃ (S : Finset ℕ+) (x : H),
      S.card = M ∧ (∀ n ∈ S, ((n : ℕ)).Prime) ∧ (∀ n ∉ S, x n = 0) ∧
      ‖x‖ ^ 2 = 1 / M ∧ ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ((M : ℝ≥0∞))⁻¹ ∧
      omegaEnergy x = ((M : ℝ≥0∞))⁻¹ ∧ ∑ n ∈ S, x n = 1 := by
  classical
  obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq Nat.Primes M
  have hcard : (F.image primePNat).card = M := by
    rw [Finset.card_image_of_injective _ primePNat_injective, hF]
  have hMt : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
  have hM0 : (M : ℝ≥0∞) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hM.ne'
  have hnorm : (‖((M : ℂ))⁻¹‖₊ : ℝ≥0∞) = ((M : ℝ≥0∞))⁻¹ := enorm_nat_inv M hM
  refine ⟨F.image primePNat, finsetVector (F.image primePNat) ((M : ℂ))⁻¹, hcard, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro n hn
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
    exact p.property
  · intro n hn
    rw [finsetVector_apply, if_neg hn]
  · rw [norm_sq_finsetVector, hcard]
    have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
    rw [norm_inv, Complex.norm_natCast]
    field_simp
  · rw [enorm_sq_finsetVector, hcard, hnorm, pow_two, ← mul_assoc,
      ENNReal.mul_inv_cancel hM0 hMt, one_mul]
  · rw [omegaEnergy_finsetVector]
    have hterm : ∀ n ∈ F.image primePNat,
        (omegaPNat n : ℝ≥0∞) * ((‖((M : ℂ))⁻¹‖₊ : ℝ≥0∞)) ^ 2
          = ((‖((M : ℂ))⁻¹‖₊ : ℝ≥0∞)) ^ 2 := by
      intro n hn
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
      rw [omegaPNat_primePNat]
      simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcard, nsmul_eq_mul, hnorm, pow_two,
      ← mul_assoc, ENNReal.mul_inv_cancel hM0 hMt, one_mul]
  · rw [sum_finsetVector, hcard]
    have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
    field_simp

/-- **Failure of closability of additive boundary evaluation.**  There are finitely supported
vectors of arbitrarily small graph energy whose coefficient sum equals one.  Hence no closed
scalar trace on the row graph extends finite-support additive evaluation. -/
theorem exists_small_graphEnergy_unit_coefficient_sum {s : ℂ} (hs : 1 / 2 < s.re)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (S : Finset ℕ+) (x : H),
      (∀ n ∉ S, x n = 0) ∧ ∑ n ∈ S, x n = 1 ∧
      (‖x‖₊ : ℝ≥0∞) ^ 2 + rowEnergy s x < ε := by
  classical
  set C : ℝ≥0∞ := 2 + 2 * primeZetaEnergy s with hC
  have hCtop : C ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.mul_ne_top (by norm_num)
      (primeZetaEnergy_ne_top hs)⟩
  have hlim : Filter.Tendsto (fun M : ℕ => C * (2 * ((M : ℝ≥0∞))⁻¹)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun M : ℕ => ((M : ℝ≥0∞))⁻¹) Filter.atTop (nhds 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero
    have h1 : Filter.Tendsto (fun M : ℕ => 2 * ((M : ℝ≥0∞))⁻¹) Filter.atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul h0 (Or.inr (by norm_num))
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hCtop)
  obtain ⟨M, hM⟩ := ((hlim.eventually (eventually_lt_nhds hε)).and
    (Filter.eventually_gt_atTop 0)).exists
  obtain ⟨S, x, _hcard, _hprime, hsupp, _hnorm, hnnorm, homega, hsum⟩ :=
    exists_prime_uniform_vector M hM.2
  refine ⟨S, x, hsupp, hsum, ?_⟩
  have hbound : (‖x‖₊ : ℝ≥0∞) ^ 2 + rowEnergy s x ≤ C * (2 * ((M : ℝ≥0∞))⁻¹) := by
    refine le_trans (graphEnergy_le_weight s x) ?_
    rw [← hC]
    refine mul_le_mul_left' ?_ C
    rw [graphWeightEnergy_eq, homega, hnnorm, two_mul]
  exact lt_of_le_of_lt hbound hM.1

/-- **The coefficient functional is unbounded on the weighted graph space.**  Equivalently, the
series `∑_n (1+ω(n))^{-1}` diverges: its prime subseries alone is a constant `1/2`. -/
theorem not_summable_inv_one_add_omega :
    ¬ Summable fun n : ℕ+ => ((1 + omegaPNat n : ℕ) : ℝ)⁻¹ := by
  intro h
  have h2 := h.comp_injective primePNat_injective
  have h3 : ∀ p : Nat.Primes, ((fun n : ℕ+ => ((1 + omegaPNat n : ℕ) : ℝ)⁻¹) ∘ primePNat) p
      = (2 : ℝ)⁻¹ := by
    intro p
    simp [Function.comp, omegaPNat_primePNat]
  have h4 : Summable fun _ : Nat.Primes => (2 : ℝ)⁻¹ := h2.congr h3
  have := (summable_const_iff (2 : ℝ)⁻¹).mp h4
  simp at this

/-! ### The closed all-prime row -/

/-- The prime-indexed target of the all-prime row. -/
abbrev RowSpace : Type := lp (fun _ : Nat.Primes => H) 2


theorem summable_norm_sq_row (y : RowSpace) : Summable fun p : Nat.Primes => ‖y p‖ ^ 2 := by
  have h := (lp.memℓp y).summable (p := 2) (by norm_num)
  refine h.congr ?_
  intro n
  norm_num

theorem enorm_sq_eq_tsum_row (y : RowSpace) :
    ((‖y‖₊ : ℝ≥0∞)) ^ 2 = ∑' p : Nat.Primes, ((‖y p‖₊ : ℝ≥0∞)) ^ 2 := by
  have hsum : Summable fun p : Nat.Primes => ‖y p‖₊ ^ 2 := by
    rw [← NNReal.summable_coe]
    simpa using summable_norm_sq_row y
  have hreal : ‖y‖ ^ 2 = ∑' p : Nat.Primes, ‖y p‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : Nat.Primes => H) (by norm_num) y
    simp only [ENNReal.toReal_ofNat] at h
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num] at h
    simpa [Real.rpow_natCast] using h
  have hnn : ‖y‖₊ ^ 2 = ∑' p : Nat.Primes, ‖y p‖₊ ^ 2 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_tsum]
    push_cast
    exact hreal
  rw [← ENNReal.coe_pow, hnn, ENNReal.coe_tsum hsum]
  simp [ENNReal.coe_pow]

theorem rowEnergy_summable {s : ℂ} {x : H} (hx : rowEnergy s x ≠ ⊤) :
    Summable fun p : Nat.Primes => ‖rowOp s p x‖ ^ 2 := by
  have h1 : (∑' p : Nat.Primes, ((‖rowOp s p x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := by
    simpa [ENNReal.coe_pow, rowEnergy] using hx
  have h2 : Summable fun p : Nat.Primes => ‖rowOp s p x‖₊ ^ 2 :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp h1
  rw [← NNReal.summable_coe] at h2
  simpa using h2

theorem memℓp_row {s : ℂ} {x : H} (hx : rowEnergy s x ≠ ⊤) :
    Memℓp (fun p : Nat.Primes => rowOp s p x) 2 := by
  refine memℓp_gen ?_
  refine (rowEnergy_summable hx).congr ?_
  intro p
  norm_num

theorem rowEnergy_eq_of_memℓp {s : ℂ} {x : H} (y : RowSpace)
    (hy : ∀ p : Nat.Primes, y p = rowOp s p x) :
    rowEnergy s x = ((‖y‖₊ : ℝ≥0∞)) ^ 2 := by
  rw [enorm_sq_eq_tsum_row y, rowEnergy]
  exact tsum_congr fun p => by rw [hy]

/-- The graph of the all-prime row, as a submodule of `H × ℓ²(primes; H)`. -/
def rowGraph (s : ℂ) : Submodule ℂ (H × RowSpace) where
  carrier := {z | ∀ p : Nat.Primes, z.2 p = rowOp s p z.1}
  zero_mem' := by intro p; simp
  add_mem' := by
    intro z w hz hw p
    have : (z + w).2 p = z.2 p + w.2 p := rfl
    rw [this, hz p, hw p]
    simp
  smul_mem' := by
    intro c z hz p
    have : (c • z).2 p = c • z.2 p := rfl
    rw [this, hz p]
    simp

theorem mem_rowGraph_iff {s : ℂ} {z : H × RowSpace} :
    z ∈ rowGraph s ↔ ∀ p : Nat.Primes, z.2 p = rowOp s p z.1 := Iff.rfl

/-- **The all-prime row is closed.** -/
theorem isClosed_rowGraph (s : ℂ) : IsClosed ((rowGraph s : Submodule ℂ (H × RowSpace)) : Set (H × RowSpace)) := by
  have hset : ((rowGraph s : Submodule ℂ (H × RowSpace)) : Set (H × RowSpace))
      = ⋂ p : Nat.Primes, {z : H × RowSpace | z.2 p - rowOp s p z.1 = 0} := by
    ext z
    simp [rowGraph, sub_eq_zero, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun p => ?_
  have hcont : Continuous fun z : H × RowSpace => z.2 p - rowOp s p z.1 := by
    refine Continuous.sub ?_ ?_
    · exact ((lp.lipschitzWith_one_eval (E := fun _ : Nat.Primes => H) 2 p).continuous).comp
        continuous_snd
    · exact (rowOp s p).continuous.comp continuous_fst
  have hpre : IsClosed ((fun z : H × RowSpace => z.2 p - rowOp s p z.1) ⁻¹' {(0 : H)}) :=
    (isClosed_singleton (x := (0 : H))).preimage hcont
  convert hpre using 1
  rfl

/-- **The kernel of the all-prime row is the common eigenline.** -/
theorem rowGraph_kernel (s : ℂ) {x : H} :
    ((x, (0 : RowSpace)) ∈ rowGraph s) ↔ x ∈ eigenSubmodule s := by
  rw [mem_rowGraph_iff, mem_eigenSubmodule_iff]
  constructor
  · intro h p
    have := h p
    simpa using this.symm
  · intro h p
    simp [h p]

/-- The domain of the all-prime row. -/
def rowDomain (s : ℂ) : Submodule ℂ H where
  carrier := {x | rowEnergy s x ≠ ⊤}
  zero_mem' := by
    have : rowEnergy s 0 = 0 := by simp [rowEnergy]
    simp [this]
  add_mem' := by
    intro x y hx hy
    have hterm : ∀ p : Nat.Primes, ((‖rowOp s p (x + y)‖₊ : ℝ≥0∞)) ^ 2
        ≤ 2 * ((‖rowOp s p x‖₊ : ℝ≥0∞)) ^ 2 + 2 * ((‖rowOp s p y‖₊ : ℝ≥0∞)) ^ 2 := by
      intro p
      have h1 : (‖rowOp s p (x + y)‖₊ : ℝ≥0∞)
          ≤ (‖rowOp s p x‖₊ : ℝ≥0∞) + (‖rowOp s p y‖₊ : ℝ≥0∞) := by
        rw [map_add]
        exact_mod_cast ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)
      exact le_trans (pow_le_pow_left' h1 2) (enn_sq_add_le _ _)
    have hle : rowEnergy s (x + y) ≤ 2 * rowEnergy s x + 2 * rowEnergy s y := by
      calc rowEnergy s (x + y)
          ≤ ∑' p : Nat.Primes, (2 * ((‖rowOp s p x‖₊ : ℝ≥0∞)) ^ 2
              + 2 * ((‖rowOp s p y‖₊ : ℝ≥0∞)) ^ 2) := ENNReal.tsum_le_tsum hterm
        _ = 2 * rowEnergy s x + 2 * rowEnergy s y := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
            rfl
    refine ne_top_of_le_ne_top ?_ hle
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hx,
      ENNReal.mul_ne_top (by norm_num) hy⟩
  smul_mem' := by
    intro c x hx
    have heq : rowEnergy s (c • x) = ((‖c‖₊ : ℝ≥0∞)) ^ 2 * rowEnergy s x := by
      rw [rowEnergy, rowEnergy, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun p => ?_
      rw [map_smul, nnnorm_smul]
      push_cast
      ring
    rw [Set.mem_setOf_eq, heq]
    exact ENNReal.mul_ne_top (by simp [← ENNReal.coe_pow]) hx

theorem mem_rowDomain_iff {s : ℂ} {x : H} :
    x ∈ rowDomain s ↔ ∃ y : RowSpace, (x, y) ∈ rowGraph s := by
  constructor
  · intro hx
    exact ⟨⟨fun p => rowOp s p x, memℓp_row hx⟩, fun p => rfl⟩
  · rintro ⟨y, hy⟩
    have hEq : rowEnergy s x = ((‖y‖₊ : ℝ≥0∞)) ^ 2 := rowEnergy_eq_of_memℓp y hy
    show rowEnergy s x ≠ ⊤
    rw [hEq]
    simp [← ENNReal.coe_pow]

/-- Truncation of a vector to a finite index set. -/
def truncate (x : H) (F : Finset ℕ+) : H := ∑ n ∈ F, lp.single 2 n (x n)

theorem truncate_apply (x : H) (F : Finset ℕ+) (m : ℕ+) :
    truncate x F m = if m ∈ F then x m else 0 := by
  classical
  rw [truncate, lp.coeFn_sum]
  simp [lp.single_apply]

theorem omegaEnergy_truncate_ne_top (x : H) (F : Finset ℕ+) : omegaEnergy (truncate x F) ≠ ⊤ := by
  classical
  rw [omegaEnergy]
  rw [tsum_eq_sum (s := F) (fun n hn => by rw [truncate_apply, if_neg hn]; simp)]
  refine (ENNReal.sum_lt_top.mpr fun n _ => ?_).ne
  exact ENNReal.mul_lt_top (by simp) (by simp [← ENNReal.coe_pow])

theorem truncate_mem_rowDomain {s : ℂ} (hs : 1 / 2 < s.re) (x : H) (F : Finset ℕ+) :
    truncate x F ∈ rowDomain s :=
  (rowEnergy_ne_top_iff hs _).mpr (omegaEnergy_truncate_ne_top x F)

/-- **The all-prime row is densely defined.** -/
theorem rowDomain_dense {s : ℂ} (hs : 1 / 2 < s.re) :
    (rowDomain s).topologicalClosure = ⊤ := by
  refine top_unique fun x _ => ?_
  have hsum := lp.hasSum_single (E := fun _ : ℕ+ => ℂ) (p := 2) (by norm_num) x
  have hx : x ∈ closure ((rowDomain s : Submodule ℂ H) : Set H) := by
    refine mem_closure_of_tendsto hsum ?_
    filter_upwards with F
    exact truncate_mem_rowDomain hs x F
  rwa [← Submodule.topologicalClosure_coe] at hx

end

end RHTower.PrimeCoShift
