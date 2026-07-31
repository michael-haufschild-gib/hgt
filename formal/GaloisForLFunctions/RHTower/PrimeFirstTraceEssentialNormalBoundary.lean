import GaloisForLFunctions.RHTower.PrimeFirstTraceExponentialFlatGraphFracture
import GaloisForLFunctions.RHTower.PrimeFirstTraceExactGraphClosureUniversalityLaw

/-!
# Essential normal boundary of the actual-prime first-trace graph

Ordinary graph closure erases the input--output coupling of the actual-prime first-trace clock,
and every finite Rees grade loses its exponentially flat response.  This module retains the
first vector-valued essential associated grade.

For the canonical graph-null witness, remove the fixed first response coordinate before the
reciprocal-prime blow-up.  The resulting vector converges to the second Hardy basis vector:

`p • primeFirstTraceEssentialResponse p → e₂`.

The explicit error is at most `2 / p + 6 / p²`, uniformly in the auxiliary Bertrand prime.
No Xi zero, numerical computation, or additional axiom is used.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- Remove the fixed first non-vacuum Hardy coordinate. -/
def primeHardyRemoveFirst (y : PrimeHardy) : PrimeHardy :=
  y - y 1 • lp.single 2 1 1

/-- Multiplying the first Hardy remainder by its prime scale and subtracting the second basis
vector leaves exactly the zero-prepended remainder. -/
theorem prime_smul_remainder_sub_basisTwo_eq_prependZero (p : Nat.Primes) :
    (p.1 : ℝ) •
          hardyFirstTailRemainder
            (primeReciprocal p) (primeReciprocal_abs_lt_one p) -
        lp.single 2 2 1 =
      hardyPrependZero
        (hardyFirstTailRemainder
          (primeReciprocal p) (primeReciprocal_abs_lt_one p)) := by
  have hq0 : primeReciprocal p ≠ 0 := ne_of_gt (primeReciprocal_pos p)
  have hp0 : ((p.1 : ℝ)) ≠ 0 := by exact_mod_cast p.2.ne_zero
  apply lp.ext
  funext n
  cases n with
  | zero =>
      simp [hardyPrependZero_apply_zero,
        hardyFirstTailRemainder_apply_zero, lp.single_apply]
  | succ n =>
      rw [hardyPrependZero_apply_succ]
      cases n with
      | zero =>
          change (p.1 : ℝ) *
              hardyFirstTailRemainder
                (primeReciprocal p) (primeReciprocal_abs_lt_one p) 1 -
              (lp.single (E := fun _ : ℕ => ℝ) 2 2 1) 1 =
            hardyFirstTailRemainder
              (primeReciprocal p) (primeReciprocal_abs_lt_one p) 0
          rw [hardyFirstTailRemainder_apply_one hq0,
            hardyFirstTailRemainder_apply_zero]
          simp [lp.single_apply]
      | succ n =>
          cases n with
          | zero =>
              change (p.1 : ℝ) *
                  hardyFirstTailRemainder
                    (primeReciprocal p) (primeReciprocal_abs_lt_one p) 2 -
                  (lp.single (E := fun _ : ℕ => ℝ) 2 2 1) 2 =
                hardyFirstTailRemainder
                  (primeReciprocal p) (primeReciprocal_abs_lt_one p) 1
              rw [show 2 = 0 + 2 by omega,
                hardyFirstTailRemainder_apply_add_two,
                hardyFirstTailRemainder_apply_one hq0]
              simp [primeReciprocal, lp.single_apply, hp0]
          | succ n =>
              change (p.1 : ℝ) *
                  hardyFirstTailRemainder
                    (primeReciprocal p) (primeReciprocal_abs_lt_one p) (n + 3) -
                  (lp.single (E := fun _ : ℕ => ℝ) 2 2 1) (n + 3) =
                hardyFirstTailRemainder
                  (primeReciprocal p) (primeReciprocal_abs_lt_one p) (n + 2)
              rw [show n + 3 = (n + 1) + 2 by omega,
                hardyFirstTailRemainder_apply_add_two,
                hardyFirstTailRemainder_apply_add_two]
              simp only [lp.single_apply]
              simp [primeReciprocal, pow_succ]
              field_simp [hp0]

/-- First-trace response error after removal of its fixed first non-vacuum coordinate. -/
def primeFirstTraceEssentialResponse (p : Nat.Primes) : PrimeHardy :=
  primeHardyRemoveFirst
    (primeFirstTraceClock (primeFirstTraceWitness p (farPrime p)) -
      lp.single 2 1 1)

/-- Exact two-remainder formula for the relative first-trace response.  The auxiliary-prime
contribution has an extra reciprocal-prime order. -/
theorem primeFirstTraceEssentialResponse_eq (p : Nat.Primes) :
    primeFirstTraceEssentialResponse p =
      hardyFirstTailRemainder
          (primeReciprocal p) (primeReciprocal_abs_lt_one p) -
        ((p.1 : ℝ) * Real.log ((farPrime p).1 : ℝ) /
            ((farPrime p).1 * Real.log (p.1 : ℝ))) •
          hardyFirstTailRemainder
            (primeReciprocal (farPrime p))
            (primeReciprocal_abs_lt_one (farPrime p)) := by
  let P : ℝ := p.1
  let R : ℝ := (farPrime p).1
  let L : ℝ := Real.log P
  let M : ℝ := Real.log R
  have hR0 : R ≠ 0 := by
    dsimp [R]
    exact_mod_cast (farPrime p).2.ne_zero
  have hL0 : L ≠ 0 := by
    dsimp [L, P]
    exact ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
  have hcoef : P * M / L = (P * M / (R * L)) * R := by
    field_simp [hR0, hL0]
  unfold primeFirstTraceEssentialResponse primeHardyRemoveFirst
  rw [primeFirstTraceClock_farWitness_sub_basisOne_apply_one]
  rw [primeFirstTraceClock_witness,
    prime_smul_tail_eq_remainder_add_basisOne]
  change
    (hardyFirstTailRemainder
          (primeReciprocal p) (primeReciprocal_abs_lt_one p) +
        lp.single 2 1 1 -
        (P * M / L) • primeHardyTail (farPrime p) -
        lp.single 2 1 1) -
      (-(P * M / (R * L))) • lp.single 2 1 1 =
    hardyFirstTailRemainder
        (primeReciprocal p) (primeReciprocal_abs_lt_one p) -
      (P * M / (R * L)) •
        hardyFirstTailRemainder
          (primeReciprocal (farPrime p))
          (primeReciprocal_abs_lt_one (farPrime p))
  rw [hcoef, mul_smul, prime_smul_tail_eq_remainder_add_basisOne]
  module

/-- Uniform vector error bound for the reciprocal-prime essential blow-up. -/
theorem norm_primeFirstTraceEssentialResponse_blowup_sub_basisTwo_le
    (p : Nat.Primes) :
    ‖(p.1 : ℝ) • primeFirstTraceEssentialResponse p -
        lp.single 2 2 1‖ ≤
      2 / (p.1 : ℝ) + 6 / (p.1 : ℝ) ^ 2 := by
  let P : ℝ := p.1
  let R : ℝ := (farPrime p).1
  let L : ℝ := Real.log P
  let M : ℝ := Real.log R
  let remP : PrimeHardy :=
    hardyFirstTailRemainder
      (primeReciprocal p) (primeReciprocal_abs_lt_one p)
  let remR : PrimeHardy :=
    hardyFirstTailRemainder
      (primeReciprocal (farPrime p))
      (primeReciprocal_abs_lt_one (farPrime p))
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
  have hlog : M ≤ 3 * L := by
    simpa [M, L, P, R] using farPrime_log_le_three_log p
  have hcoef0 : 0 ≤ P * (P * M / (R * L)) :=
    mul_nonneg hP0.le
      (div_nonneg (mul_nonneg hP0.le hM0.le)
        (mul_nonneg hR0.le hL0.le))
  have hcoef3 : P * (P * M / (R * L)) ≤ 3 := by
    rw [show P * (P * M / (R * L)) = P ^ 2 * M / (R * L) by ring]
    apply (div_le_iff₀ (mul_pos hR0 hL0)).2
    calc
      P ^ 2 * M ≤ R * M := mul_le_mul_of_nonneg_right hsq hM0.le
      _ ≤ R * (3 * L) := mul_le_mul_of_nonneg_left hlog hR0.le
      _ = 3 * (R * L) := by ring
  have hfirst :
      ‖P • remP - lp.single 2 2 1‖ ≤ 2 / P := by
    rw [show P = (p.1 : ℝ) by rfl]
    rw [show remP =
        hardyFirstTailRemainder
          (primeReciprocal p) (primeReciprocal_abs_lt_one p) by rfl,
      prime_smul_remainder_sub_basisTwo_eq_prependZero]
    change ‖hardyPrependZeroVec
        (hardyFirstTailRemainder
          (primeReciprocal p) (primeReciprocal_abs_lt_one p))‖ ≤
      2 / (p.1 : ℝ)
    rw [norm_hardyPrependZeroVec]
    exact norm_primeHardyRemainder_le p
  have hsecond :
      ‖(P * (P * M / (R * L))) • remR‖ ≤ 6 / P ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef0]
    calc
      P * (P * M / (R * L)) * ‖remR‖
          ≤ 3 * ‖remR‖ :=
        mul_le_mul_of_nonneg_right hcoef3 (norm_nonneg remR)
      _ ≤ 3 * (2 / R) := by
        gcongr
        simpa [remR, R] using norm_primeHardyRemainder_le (farPrime p)
      _ ≤ 6 / P ^ 2 := by
        rw [show 3 * (2 / R) = 6 / R by ring]
        exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hP0) hsq
  rw [primeFirstTraceEssentialResponse_eq]
  change
    ‖P • (remP - (P * M / (R * L)) • remR) -
        lp.single 2 2 1‖ ≤ 2 / P + 6 / P ^ 2
  rw [smul_sub, smul_smul]
  calc
    ‖P • remP - (P * (P * M / (R * L))) • remR -
          lp.single 2 2 1‖ =
        ‖(P • remP - lp.single 2 2 1) -
          (P * (P * M / (R * L))) • remR‖ := by
            congr 1
            module
    _ ≤ ‖P • remP - lp.single 2 2 1‖ +
          ‖(P * (P * M / (R * L))) • remR‖ := norm_sub_le _ _
    _ ≤ 2 / P + 6 / P ^ 2 := add_le_add hfirst hsecond

/-- The relative reciprocal-prime blow-up has the canonical second Hardy-jet boundary. -/
theorem tendsto_primeFirstTraceEssentialResponse_blowup_basisTwo :
    Tendsto
      (fun n =>
        ((nthPrimePoint n).1 : ℝ) •
          primeFirstTraceEssentialResponse (nthPrimePoint n))
      atTop (𝓝 (lp.single 2 2 1)) := by
  have hP := tendsto_nthPrimePoint_cast_atTop
  have hinv : Tendsto
      (fun n : ℕ => (((nthPrimePoint n).1 : ℝ))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hP
  have hinvSq : Tendsto
      (fun n : ℕ => (((nthPrimePoint n).1 : ℝ))⁻¹ ^ 2)
      atTop (𝓝 0) := by
    simpa using hinv.pow 2
  have hbound : Tendsto
      (fun n : ℕ =>
        2 / ((nthPrimePoint n).1 : ℝ) +
          6 / ((nthPrimePoint n).1 : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have htwo : Tendsto
        (fun n : ℕ => (2 : ℝ) * (((nthPrimePoint n).1 : ℝ))⁻¹)
        atTop (𝓝 0) := by
      simpa using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul hinv)
    have hsix : Tendsto
        (fun n : ℕ => (6 : ℝ) * (((nthPrimePoint n).1 : ℝ))⁻¹ ^ 2)
        atTop (𝓝 0) := by
      simpa using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (6 : ℝ)) atTop (𝓝 6)).mul hinvSq)
    convert
      htwo.add hsix using 1 <;>
      simp [div_eq_mul_inv, inv_pow]
  have hzero : Tendsto
      (fun n =>
        ((nthPrimePoint n).1 : ℝ) •
            primeFirstTraceEssentialResponse (nthPrimePoint n) -
          lp.single 2 2 1)
      atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hevent : ∀ᶠ n : ℕ in atTop,
        2 / ((nthPrimePoint n).1 : ℝ) +
            6 / ((nthPrimePoint n).1 : ℝ) ^ 2 < ε :=
      (tendsto_order.1 hbound).2 ε hε
    filter_upwards [hevent] with n hn
    exact lt_of_le_of_lt
      (norm_primeFirstTraceEssentialResponse_blowup_sub_basisTwo_le
        (nthPrimePoint n)) hn
  have hadd := hzero.add (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (lp.single 2 2 1 : PrimeHardy))
      atTop (𝓝 (lp.single 2 2 1)))
  simpa only [sub_add_cancel, zero_add] using hadd

/-- The zero-prepending shift sends the first non-vacuum Hardy basis vector to the second. -/
theorem hardyPrependZero_basisOne_eq_basisTwo :
    hardyPrependZero (lp.single 2 1 1 : PrimeHardy) =
      lp.single 2 2 1 := by
  apply lp.ext
  funext n
  cases n with
  | zero => simp [hardyPrependZero_apply_zero, lp.single_apply]
  | succ n =>
      rw [hardyPrependZero_apply_succ]
      simp only [lp.single_apply, Pi.single_apply]
      by_cases hn : n = 1
      · subst n
        simp
      · have hsucc : n + 1 ≠ 2 := by omega
        simp [hn, hsucc]

/-- **Anisotropic essential graph limit.**  The logarithmic source normal and reciprocal-prime
relative response normal converge jointly to one edge of the unilateral Hardy shift.  This is a
relative associated-graded graph, not a graph in the ordinary Hilbert topology. -/
theorem tendsto_primeFirstTrace_anisotropicEssentialGraph :
    Tendsto
      (fun n =>
        (Real.log ((nthPrimePoint n).1 : ℝ) •
            primeHardyKernelMap (primeFirstTraceNullSequence n),
          ((nthPrimePoint n).1 : ℝ) •
            primeFirstTraceEssentialResponse (nthPrimePoint n)))
      atTop
      (𝓝 ((lp.single 2 1 1 : PrimeHardy),
        hardyPrependZero (lp.single 2 1 1 : PrimeHardy))) := by
  rw [hardyPrependZero_basisOne_eq_basisTwo]
  simpa only [nhds_prod_eq] using
    tendsto_log_smul_primeHardyKernelMap_nullSequence_basisOne.prodMk
      tendsto_primeFirstTraceEssentialResponse_blowup_basisTwo

end

end RHTower
