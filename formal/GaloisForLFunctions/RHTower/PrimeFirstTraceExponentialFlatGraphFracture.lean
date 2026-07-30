import GaloisForLFunctions.RHTower.ArithmeticSchurFirstTraceNonclosability

/-!
# Exponential flatness of the actual-prime first-trace graph fracture

The existing actual-prime graph-null witness proves that the arithmetic-Schur first-trace clock is
not sequentially closable.  Its two visible coordinates contain strictly more information than
binary nonclosability:

* the source norm is between `1 / (2 log p)` and `4 / log p`;
* the response error is between `1 / p` and `8 / p`.

Consequently, if `a` is source size and `b` is response error, then

`exp (-4 / a) ≤ b ≤ 8 exp (-1 / (2a))`.

Along consecutive actual primes the logarithmic blow-up of the source converges to the first
valuation basis vector and the dimensionless rate-distortion product tends exactly to one:

`log(p_n) X_n → e₁` and `‖X_n‖ (-log ‖Y_n‖) → 1`.

Thus the graph fracture is exponentially flat in inverse source size but retains a canonical
rate-normal direction and grade. Any comparison mechanism controlled only to finite algebraic
order at the closed graph boundary is blind to this arithmetic rate. No Xi zero, RH criterion,
numerical computation, or extra axiom is used.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- Exact first coordinate of the actual-prime source packet. -/
theorem primeHardyKernelMap_farWitness_apply_one (p : Nat.Primes) :
    primeHardyKernelMap (primeFirstTraceWitness p (farPrime p)) 1 =
      (1 - (p.1 : ℝ) / (farPrime p).1) / Real.log (p.1 : ℝ) := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hr0 : ((farPrime p).1 : ℝ) ≠ 0 := by
    exact_mod_cast (farPrime p).2.ne_zero
  have hlogp : Real.log (p.1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
  rw [primeHardyKernelMap_witness]
  change ((p.1 : ℝ) / Real.log (p.1 : ℝ)) *
      (primeHardyTail p 1 - primeHardyTail (farPrime p) 1) = _
  simp [primeHardyTail, primeReciprocal, hardyFirstTail_apply_succ]
  field_simp [hp0, hr0, hlogp]

/-- Exact first coordinate of the response error left after removing the first basis vector. -/
theorem primeFirstTraceClock_farWitness_sub_basisOne_apply_one (p : Nat.Primes) :
    ((primeFirstTraceClock (primeFirstTraceWitness p (farPrime p)) -
        lp.single 2 1 1 : PrimeHardy) : ℕ → ℝ) 1 =
      -((p.1 : ℝ) * Real.log ((farPrime p).1 : ℝ) /
        ((farPrime p).1 * Real.log (p.1 : ℝ))) := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hr0 : ((farPrime p).1 : ℝ) ≠ 0 := by
    exact_mod_cast (farPrime p).2.ne_zero
  have hlogp : Real.log (p.1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
  rw [primeFirstTraceClock_witness]
  change (p.1 : ℝ) * primeHardyTail p 1 -
      ((p.1 : ℝ) * Real.log ((farPrime p).1 : ℝ) /
        Real.log (p.1 : ℝ)) * primeHardyTail (farPrime p) 1 -
      (lp.single (E := fun _ : ℕ => ℝ) 2 1 1) 1 = _
  simp [primeHardyTail, primeReciprocal, hardyFirstTail_apply_succ, lp.single_apply]
  field_simp [hp0, hr0, hlogp]
  all_goals ring

/-- The source packet has the reciprocal-logarithmic lower bound hidden by the original
nonclosability estimate. -/
theorem one_div_two_log_le_norm_primeHardyKernelMap_farWitness (p : Nat.Primes) :
    1 / (2 * Real.log (p.1 : ℝ)) ≤
      ‖primeHardyKernelMap (primeFirstTraceWitness p (farPrime p))‖ := by
  let P : ℝ := p.1
  let R : ℝ := (farPrime p).1
  let L : ℝ := Real.log P
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hR0 : 0 < R := by dsimp [R]; exact_mod_cast (farPrime p).2.pos
  have hL0 : 0 < L := by
    dsimp [L, P]
    exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hP2 : 2 ≤ P := by dsimp [P]; exact_mod_cast p.2.two_le
  have hsq : P ^ 2 ≤ R := by
    dsimp [P, R]
    exact_mod_cast (farPrime_sq_lt p).le
  have hratio : P / R ≤ 1 / 2 := by
    apply (div_le_iff₀ hR0).2
    nlinarith
  have hcoord0 : 0 ≤ (1 - P / R) / L :=
    div_nonneg (by linarith) hL0.le
  have hcoordLower : 1 / (2 * L) ≤ (1 - P / R) / L := by
    rw [show 1 / (2 * L) = (1 / 2 : ℝ) / L by ring]
    exact (div_le_div_iff_of_pos_right hL0).2 (by linarith)
  have happ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (primeHardyKernelMap (primeFirstTraceWitness p (farPrime p))) 1
  rw [primeHardyKernelMap_farWitness_apply_one] at happ
  change |(1 - P / R) / L| ≤ _ at happ
  rw [abs_of_nonneg hcoord0] at happ
  exact hcoordLower.trans happ

/-- The first-trace response error has a reciprocal-prime lower bound. -/
theorem one_div_prime_le_norm_primeFirstTraceClock_farWitness_sub_basisOne
    (p : Nat.Primes) :
    1 / (p.1 : ℝ) ≤
      ‖primeFirstTraceClock (primeFirstTraceWitness p (farPrime p)) -
        lp.single 2 1 1‖ := by
  let P : ℝ := p.1
  let R : ℝ := (farPrime p).1
  let L : ℝ := Real.log P
  let M : ℝ := Real.log R
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hR0 : 0 < R := by dsimp [R]; exact_mod_cast (farPrime p).2.pos
  have hL0 : 0 < L := by
    dsimp [L, P]
    exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hM0 : 0 < M := by
    dsimp [M, R]
    exact Real.log_pos (by exact_mod_cast (farPrime p).2.one_lt)
  have hsq : P ^ 2 ≤ R := by
    dsimp [P, R]
    exact_mod_cast (farPrime_sq_lt p).le
  have hRupper : R ≤ 2 * P ^ 2 := by
    dsimp [P, R]
    exact_mod_cast farPrime_le_two_sq p
  have hMlower : 2 * L ≤ M := by
    calc
      2 * L = Real.log (P ^ 2) := by
        dsimp [L]
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log R := Real.log_le_log (sq_pos_of_pos hP0) hsq
      _ = M := rfl
  have hratio0 : 0 ≤ P * M / (R * L) :=
    (div_pos (mul_pos hP0 hM0) (mul_pos hR0 hL0)).le
  have hratioLower : 1 / P ≤ P * M / (R * L) := by
    apply (le_div_iff₀ (mul_pos hR0 hL0)).2
    have hrL : R * L ≤ (2 * P ^ 2) * L :=
      mul_le_mul_of_nonneg_right hRupper hL0.le
    calc
      1 / P * (R * L) = P⁻¹ * (R * L) := by rw [one_div]
      _ ≤ P⁻¹ * ((2 * P ^ 2) * L) :=
        mul_le_mul_of_nonneg_left hrL (inv_nonneg.mpr hP0.le)
      _ = 2 * P * L := by field_simp [ne_of_gt hP0]
      _ ≤ P * M := by nlinarith
  have happ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (primeFirstTraceClock (primeFirstTraceWitness p (farPrime p)) -
      lp.single 2 1 1) 1
  rw [primeFirstTraceClock_farWitness_sub_basisOne_apply_one] at happ
  change |- (P * M / (R * L))| ≤ _ at happ
  rw [abs_neg, abs_of_nonneg hratio0] at happ
  exact hratioLower.trans happ

/-- Exact exponential rate class of the actual-prime graph fracture.  This is the quantitative
positive survivor of the binary nonclosability no-go. -/
theorem primeFirstTrace_farWitness_exponential_graph_sandwich (p : Nat.Primes) :
    let a :=
      ‖primeHardyKernelMap (primeFirstTraceWitness p (farPrime p))‖
    let b :=
      ‖primeFirstTraceClock (primeFirstTraceWitness p (farPrime p)) -
        lp.single 2 1 1‖
    Real.exp (-4 / a) ≤ b ∧
      b ≤ 8 * Real.exp (-1 / (2 * a)) := by
  let P : ℝ := p.1
  let L : ℝ := Real.log P
  let a :=
    ‖primeHardyKernelMap (primeFirstTraceWitness p (farPrime p))‖
  let b :=
    ‖primeFirstTraceClock (primeFirstTraceWitness p (farPrime p)) -
      lp.single 2 1 1‖
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hL0 : 0 < L := by
    dsimp [L, P]
    exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  have haLower : 1 / (2 * L) ≤ a := by
    simpa [a, L, P] using one_div_two_log_le_norm_primeHardyKernelMap_farWitness p
  have haUpper : a ≤ 4 / L := by
    simpa [a, L, P] using norm_primeHardyKernelMap_farWitness_le p
  have hbLower : 1 / P ≤ b := by
    simpa [b, P] using
      one_div_prime_le_norm_primeFirstTraceClock_farWitness_sub_basisOne p
  have hbUpper : b ≤ 8 / P := by
    simpa [b, P] using norm_primeFirstTraceClock_farWitness_sub_basisOne_le p
  have ha0 : 0 < a := by
    apply lt_of_lt_of_le _ haLower
    exact div_pos (by norm_num) (mul_pos (by norm_num) hL0)
  have hexp : Real.exp (-L) = 1 / P := by
    dsimp [L]
    rw [Real.exp_neg, Real.exp_log hP0]
    simp [one_div]
  have hLa : L ≤ 4 / a := by
    apply (le_div_iff₀ ha0).2
    have h := (le_div_iff₀ hL0).mp haUpper
    nlinarith
  have hInv : 1 / (2 * a) ≤ L := by
    apply (div_le_iff₀ (mul_pos (by norm_num) ha0)).2
    have h := (div_le_iff₀ (mul_pos (by norm_num) hL0)).mp haLower
    nlinarith
  constructor
  · calc
      Real.exp (-4 / a) ≤ Real.exp (-L) :=
        Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hLa)
      _ = 1 / P := hexp
      _ ≤ b := hbLower
  · calc
      b ≤ 8 / P := hbUpper
      _ = 8 * Real.exp (-L) := by rw [hexp]; ring
      _ ≤ 8 * Real.exp (-1 / (2 * a)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.exp_le_exp.mpr (by
          simpa only [neg_div] using neg_le_neg hInv)

/-! ## Canonical rate-normal direction and distortion grade -/

/-- Multiplication by `log p` blows up the vanishing source packet to the first valuation basis
vector, with an explicit reciprocal-prime error. -/
theorem norm_log_smul_primeHardyKernelMap_farWitness_sub_basisOne_le
    (p : Nat.Primes) :
    ‖Real.log (p.1 : ℝ) •
          primeHardyKernelMap (primeFirstTraceWitness p (farPrime p)) -
        lp.single 2 1 1‖ ≤
      4 / (p.1 : ℝ) := by
  let P : ℝ := p.1
  let R : ℝ := (farPrime p).1
  let L : ℝ := Real.log P
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hR0 : 0 < R := by dsimp [R]; exact_mod_cast (farPrime p).2.pos
  have hL0 : 0 < L := by
    dsimp [L, P]
    exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hsq : P ^ 2 ≤ R := by
    dsimp [P, R]
    exact_mod_cast (farPrime_sq_lt p).le
  rw [primeHardyKernelMap_witness]
  have hcoef : L * (P / L) = P := by field_simp [ne_of_gt hL0]
  rw [smul_smul, hcoef, smul_sub, prime_smul_tail_eq_remainder_add_basisOne]
  have heq :
      (hardyFirstTailRemainder (primeReciprocal p) (primeReciprocal_abs_lt_one p) +
          lp.single 2 1 1 - P • primeHardyTail (farPrime p)) -
          lp.single 2 1 1 =
        hardyFirstTailRemainder (primeReciprocal p) (primeReciprocal_abs_lt_one p) -
          P • primeHardyTail (farPrime p) := by abel
  rw [heq]
  calc
    ‖hardyFirstTailRemainder (primeReciprocal p) (primeReciprocal_abs_lt_one p) -
        P • primeHardyTail (farPrime p)‖ ≤
        ‖hardyFirstTailRemainder (primeReciprocal p) (primeReciprocal_abs_lt_one p)‖ +
          ‖P • primeHardyTail (farPrime p)‖ := norm_sub_le _ _
    _ ≤ 2 / P + P * (2 / R) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hP0]
      exact add_le_add (by simpa [P] using norm_primeHardyRemainder_le p)
        (mul_le_mul_of_nonneg_left
          (by simpa [R] using norm_primeHardyTail_le (farPrime p)) hP0.le)
    _ ≤ 2 / P + 2 / P := by
      gcongr
      apply (le_div_iff₀ hP0).2
      rw [show P * (2 / R) * P = 2 * P ^ 2 / R by ring]
      exact (div_le_iff₀ hR0).2 (by nlinarith)
    _ = 4 / P := by ring
    _ = 4 / (p.1 : ℝ) := rfl

/-- The logarithmic blow-up of the actual-prime null sequence has the canonical nonzero first
valuation direction. -/
theorem tendsto_log_smul_primeHardyKernelMap_nullSequence_basisOne :
    Tendsto
      (fun n =>
        Real.log ((nthPrimePoint n).1 : ℝ) •
          primeHardyKernelMap (primeFirstTraceNullSequence n))
      atTop (𝓝 (lp.single 2 1 1)) := by
  have hP := tendsto_nthPrimePoint_cast_atTop
  have hinv : Tendsto (fun n : ℕ => (((nthPrimePoint n).1 : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hP
  have hbound : Tendsto (fun n : ℕ =>
      4 / ((nthPrimePoint n).1 : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv :
      Tendsto (fun n : ℕ => 4 * (((nthPrimePoint n).1 : ℝ))⁻¹)
        atTop (𝓝 (4 * 0)))
  have hzero : Tendsto
      (fun n =>
        Real.log ((nthPrimePoint n).1 : ℝ) •
            primeHardyKernelMap (primeFirstTraceNullSequence n) -
          lp.single 2 1 1)
      atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hevent : ∀ᶠ n : ℕ in atTop,
        4 / ((nthPrimePoint n).1 : ℝ) < ε :=
      (tendsto_order.1 hbound).2 ε hε
    filter_upwards [hevent] with n hn
    exact lt_of_le_of_lt
      (by
        simpa [primeFirstTraceNullSequence] using
          (norm_log_smul_primeHardyKernelMap_farWitness_sub_basisOne_le
            (nthPrimePoint n))) hn
  have hadd := hzero.add (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (lp.single 2 1 1 : PrimeHardy))
      atTop (𝓝 (lp.single 2 1 1)))
  simpa only [sub_add_cancel, zero_add] using hadd

/-- Source norm has exact first-order logarithmic scale: `log p_n * a_n → 1`. -/
theorem tendsto_log_mul_norm_primeHardyKernelMap_nullSequence_one :
    Tendsto
      (fun n =>
        Real.log ((nthPrimePoint n).1 : ℝ) *
          ‖primeHardyKernelMap (primeFirstTraceNullSequence n)‖)
      atTop (𝓝 1) := by
  have h := tendsto_log_smul_primeHardyKernelMap_nullSequence_basisOne.norm
  convert h using 1
  · funext n
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by
        exact_mod_cast (nthPrimePoint n).2.one_lt))]
  · simp

/-- Response error has exact logarithmic prime rate:
`log ‖clock(w_n)-e₁‖ / log p_n → -1`. -/
theorem tendsto_log_norm_primeFirstTraceClock_error_div_log_prime_neg_one :
    Tendsto
      (fun n =>
        Real.log
            ‖primeFirstTraceClock (primeFirstTraceNullSequence n) -
              lp.single 2 1 1‖ /
          Real.log ((nthPrimePoint n).1 : ℝ))
      atTop (𝓝 (-1)) := by
  let b : ℕ → ℝ := fun n =>
    ‖primeFirstTraceClock (primeFirstTraceNullSequence n) -
      lp.single 2 1 1‖
  let L : ℕ → ℝ := fun n => Real.log ((nthPrimePoint n).1 : ℝ)
  have hLtop : Tendsto L atTop atTop := by
    simpa [L] using! Real.tendsto_log_atTop.comp tendsto_nthPrimePoint_cast_atTop
  have hinvL : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hLtop
  have hupperT : Tendsto
      (fun n => -1 + Real.log 8 * (L n)⁻¹) atTop (𝓝 (-1)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hinvL))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupperT
  · filter_upwards with n
    let P : ℝ := (nthPrimePoint n).1
    have hP0 : 0 < P := by
      dsimp [P]
      exact_mod_cast (nthPrimePoint n).2.pos
    have hL0 : 0 < L n := by
      dsimp [L, P]
      exact Real.log_pos (by exact_mod_cast (nthPrimePoint n).2.one_lt)
    have hbLower : 1 / P ≤ b n := by
      simpa [b, P, primeFirstTraceNullSequence] using
        one_div_prime_le_norm_primeFirstTraceClock_farWitness_sub_basisOne
          (nthPrimePoint n)
    have hlogLower : -L n ≤ Real.log (b n) := by
      have h := Real.log_le_log (one_div_pos.mpr hP0) hbLower
      simpa [L, P, one_div, Real.log_inv] using h
    change -1 ≤ Real.log (b n) / L n
    exact (le_div_iff₀ hL0).2 (by simpa using hlogLower)
  · filter_upwards with n
    let P : ℝ := (nthPrimePoint n).1
    have hP0 : 0 < P := by
      dsimp [P]
      exact_mod_cast (nthPrimePoint n).2.pos
    have hL0 : 0 < L n := by
      dsimp [L, P]
      exact Real.log_pos (by exact_mod_cast (nthPrimePoint n).2.one_lt)
    have hbLower : 1 / P ≤ b n := by
      simpa [b, P, primeFirstTraceNullSequence] using
        one_div_prime_le_norm_primeFirstTraceClock_farWitness_sub_basisOne
          (nthPrimePoint n)
    have hbUpper : b n ≤ 8 / P := by
      simpa [b, P, primeFirstTraceNullSequence] using
        norm_primeFirstTraceClock_farWitness_sub_basisOne_le (nthPrimePoint n)
    have hb0 : 0 < b n :=
      lt_of_lt_of_le (one_div_pos.mpr hP0) hbLower
    have hlogUpper : Real.log (b n) ≤ Real.log 8 - L n := by
      have h := Real.log_le_log hb0 hbUpper
      simpa [L, P, Real.log_div (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hP0)]
        using h
    change Real.log (b n) / L n ≤ -1 + Real.log 8 * (L n)⁻¹
    apply (div_le_iff₀ hL0).2
    rw [show (-1 + Real.log 8 * (L n)⁻¹) * L n =
        Real.log 8 - L n by field_simp [ne_of_gt hL0]; ring]
    exact hlogUpper

/-- **Canonical exponential rate-distortion grade.**  The product of source size and negative
logarithmic response error tends exactly to one along the actual-prime graph-null sequence. -/
theorem tendsto_primeFirstTrace_exponentialRateDistortion_one :
    Tendsto
      (fun n =>
        ‖primeHardyKernelMap (primeFirstTraceNullSequence n)‖ *
          (-Real.log
            ‖primeFirstTraceClock (primeFirstTraceNullSequence n) -
              lp.single 2 1 1‖))
      atTop (𝓝 1) := by
  have hsource := tendsto_log_mul_norm_primeHardyKernelMap_nullSequence_one
  have hresponse :=
    tendsto_log_norm_primeFirstTraceClock_error_div_log_prime_neg_one.neg
  have hmul := hsource.mul hresponse
  convert hmul using 1
  · funext n
    have hlog0 : Real.log ((nthPrimePoint n).1 : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (nthPrimePoint n).2.one_lt))
    field_simp [hlog0]
  · norm_num

/-- **Beyond-all-orders flatness.**  For every fixed algebraic order `N`, response error divided
by the `N`th power of source size tends to zero.  Thus every finite-order classical symbol loses
the quantitative response, while the exponential rate-distortion grade above remains nonzero. -/
theorem tendsto_primeFirstTrace_error_div_source_pow_zero (N : ℕ) :
    Tendsto
      (fun n =>
        ‖primeFirstTraceClock (primeFirstTraceNullSequence n) -
            lp.single 2 1 1‖ /
          ‖primeHardyKernelMap (primeFirstTraceNullSequence n)‖ ^ N)
      atTop (𝓝 0) := by
  let P : ℕ → ℝ := fun n => (nthPrimePoint n).1
  let L : ℕ → ℝ := fun n => Real.log (P n)
  let a : ℕ → ℝ := fun n =>
    ‖primeHardyKernelMap (primeFirstTraceNullSequence n)‖
  let b : ℕ → ℝ := fun n =>
    ‖primeFirstTraceClock (primeFirstTraceNullSequence n) -
      lp.single 2 1 1‖
  have hPtop : Tendsto P atTop atTop := by
    simpa [P] using tendsto_nthPrimePoint_cast_atTop
  have hcore : Tendsto (fun n => L n ^ N / P n) atTop (𝓝 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 N one_ne_zero).comp hPtop
    simpa [L] using! h
  have hupper : Tendsto
      (fun n => (8 * 2 ^ N : ℝ) * (L n ^ N / P n))
      atTop (𝓝 0) := by
    simpa using (hcore.const_mul (8 * 2 ^ N : ℝ))
  apply squeeze_zero
  · intro n
    exact div_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) N)
  · intro n
    have hP0 : 0 < P n := by
      dsimp [P]
      exact_mod_cast (nthPrimePoint n).2.pos
    have hL0 : 0 < L n := by
      dsimp [L, P]
      exact Real.log_pos (by exact_mod_cast (nthPrimePoint n).2.one_lt)
    have haLower : 1 / (2 * L n) ≤ a n := by
      simpa [a, L, P, primeFirstTraceNullSequence] using
        one_div_two_log_le_norm_primeHardyKernelMap_farWitness (nthPrimePoint n)
    have hbUpper : b n ≤ 8 / P n := by
      simpa [b, P, primeFirstTraceNullSequence] using
        norm_primeFirstTraceClock_farWitness_sub_basisOne_le (nthPrimePoint n)
    have hdenLower :
        (1 / (2 * L n)) ^ N ≤ (a n) ^ N :=
      pow_le_pow_left₀ (by positivity) haLower N
    calc
      b n / a n ^ N ≤ (8 / P n) / a n ^ N := by
        exact div_le_div_of_nonneg_right hbUpper
          (pow_nonneg (norm_nonneg _) N)
      _ ≤ (8 / P n) / (1 / (2 * L n)) ^ N := by
        exact div_le_div_of_nonneg_left (by positivity)
          (pow_pos (by positivity) N) hdenLower
      _ = (8 * 2 ^ N : ℝ) * (L n ^ N / P n) := by
        field_simp [ne_of_gt hP0, ne_of_gt hL0]
        rw [← mul_pow]
        rw [show 1 / (2 * L n) * 2 = (L n)⁻¹ by
          field_simp [ne_of_gt hL0]]
        rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hL0), one_pow]
  · exact hupper

end

end RHTower
