import GaloisForLFunctions.MultiplicativePositivityGeometry.ArithmeticBochner
import GaloisForLFunctions.MultiplicativePositivityGeometry.IntegralLatticeRealization

/-!
# Integral Euler products realize every locally finite positive-definite divisor

Greedy rounding (`IntegralRealization`) keeps the running prime error `Σ_{p ≤ n} log p (m(p) − g(p))`
below `log(n + 1)` for every nonnegative profile `g`; a bound on `g` enters only through the proper
prime powers. With logarithmic growth `g(n) ≤ M(1 + log n)` the prime-power defect is dominated by
`Σ_{n not prime} (1 + log n)² Λ(n)/n < ∞`, so rounding still preserves the boundary divisor
(`IsBoundaryDivisor.round_log`).

The arithmetic Bochner profile has this growth (`arithProfile_le`). Hence (`integral_bochner`) a
locally finite `D` is the boundary divisor of an Euler product `Π_p (1 − p^{−s})^{−m(p)}` with
exponents `m(p) ∈ ℕ` iff it is even and positive definite: neither integrality of the exponents nor
restriction to the rational primes constrains a locally finite boundary configuration.
-/

open Finset Filter Topology Complex

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- `Λ(n)/n ≤ (1 + log n)² Λ(n)/n` off the primes. -/
theorem nonprime_div_le_logSq (n : ℕ) :
    (if n.Prime then 0 else (1 + Real.log n) * (ArithmeticFunction.vonMangoldt n : ℝ) / n) ≤
      if n.Prime then 0 else (1 + Real.log n) ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
  split_ifs
  · exact le_rfl
  · have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
    rw [mul_div_assoc, mul_div_assoc]
    have hsq : 1 + Real.log n ≤ (1 + Real.log n) ^ 2 := by
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + Real.log n) hl
      linarith [sq (1 + Real.log n)]
    exact mul_le_mul_of_nonneg_right hsq hΛ

/-- **Rounding a logarithmically growing profile preserves the boundary divisor.** If the weights
`g(n) Λ(n) n^{−1−x}` with `0 ≤ g(n) ≤ M(1 + log n)` have boundary divisor `D`, so does the Euler
product with the greedy integer exponents `m = roundMult g`. -/
theorem IsBoundaryDivisor.round_log {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {M : ℝ}
    (hgM : ∀ n, g n ≤ M * (1 + logFrequency n)) {D : ℝ → ℝ}
    (hD : IsBoundaryDivisor logFrequency (fun x n => zetaBoundaryWeight x n * g n) D) :
    IsBoundaryDivisor logFrequency (intWeight (roundMult g)) D := by
  have hM0 : 0 ≤ M := by simpa [logFrequency] using (hg 0).trans (hgM 0)
  have hm : ∀ n, (roundMult g n : ℝ) ≤ M * (1 + logFrequency n) + 1 := fun n => by
    have h := (abs_lt.mp (abs_roundStep_sub_lt (roundError g (n - 1)) (hg n))).2
    unfold roundMult
    linarith [hgM n]
  -- Where `Λ(n) ≠ 0`, `minFac n ≤ n`.
  have hmin : ∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0 →
      logFrequency n.minFac ≤ logFrequency n := fun n hn => by
    have hn1 : 1 < n := by
      by_contra h
      interval_cases n <;> simp at hn
    exact Real.log_le_log (by exact_mod_cast Nat.minFac_pos n)
      (by exact_mod_cast Nat.minFac_le (by omega))
  have hmz : ∀ x, 0 < x → ∀ n, |powerDefect (roundMult g) g x n| ≤ (2 * M + 1) *
      (if n.Prime then 0 else (1 + Real.log n) ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) / n) := by
    intro x hx n
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (nonprime_div_le_logSq n) (by linarith))
    unfold powerDefect
    split_ifs with hp
    · simp
    · rw [abs_mul, abs_of_nonneg (zetaBoundaryWeight_nonneg x n)]
      by_cases hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) = 0
      · have : zetaBoundaryWeight x n = 0 := by simp [zetaBoundaryWeight, hΛ]
        rw [this, zero_mul]
        exact mul_nonneg (by linarith) (div_nonneg (mul_nonneg (by
          linarith [Real.log_natCast_nonneg n]) ArithmeticFunction.vonMangoldt_nonneg)
          (Nat.cast_nonneg n))
      · have hl : 0 ≤ logFrequency n := Real.log_natCast_nonneg n
        have h1 : |(roundMult g n.minFac : ℝ) - g n| ≤ (2 * M + 1) * (1 + Real.log n) := by
          have hmm := hm n.minFac
          have hmn := hmin n hΛ
          have hgn := hgM n
          unfold logFrequency at hmm hmn hgn hl
          have hML := mul_le_mul_of_nonneg_left hmn hM0
          have hML0 := mul_nonneg hM0 hl
          have hm0 : (0 : ℝ) ≤ roundMult g n.minFac := Nat.cast_nonneg _
          rw [abs_le]
          constructor <;> linarith [hg n]
        calc zetaBoundaryWeight x n * |(roundMult g n.minFac : ℝ) - g n|
            ≤ ArithmeticFunction.vonMangoldt n / n * ((2 * M + 1) * (1 + Real.log n)) :=
              mul_le_mul (zetaBoundaryWeight_le_div hx.le n) h1 (abs_nonneg _)
                (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
          _ = (2 * M + 1) * ((1 + Real.log n) * ArithmeticFunction.vonMangoldt n / n) := by ring
  have hR := summable_nonprime_logSq
  set R := ∑' n : ℕ, (if n.Prime then 0 else
    (1 + Real.log n) ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) / n)
  have hmw : ∀ x, 0 < x → ∀ n, intWeight (roundMult g) x n ≤
      M * zetaBoundaryWeight x n + M * (zetaBoundaryWeight x n * logFrequency n) +
        zetaBoundaryWeight x n := fun x hx n => by
    unfold intWeight
    by_cases hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) = 0
    · have : zetaBoundaryWeight x n = 0 := by simp [zetaBoundaryWeight, hΛ]
      simp [this]
    · have h := mul_le_mul_of_nonneg_right (hm n.minFac) (zetaBoundaryWeight_nonneg x n)
      have h2 := mul_le_mul_of_nonneg_left (hmin n hΛ)
        (mul_nonneg hM0 (zetaBoundaryWeight_nonneg x n))
      have e : (M * (1 + logFrequency n.minFac) + 1) * zetaBoundaryWeight x n =
          M * zetaBoundaryWeight x n + M * zetaBoundaryWeight x n * logFrequency n.minFac +
            zetaBoundaryWeight x n := by ring
      rw [e] at h
      linarith
  refine ⟨fun x _ n => mul_nonneg (Nat.cast_nonneg _) (zetaBoundaryWeight_nonneg x n),
    fun x hx => Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg _) (zetaBoundaryWeight_nonneg x n)) (hmw x hx)
      ((((summable_zetaBoundaryWeight hx).mul_left M).add
        ((summable_zetaBoundaryWeight_mul_log hx).mul_left M)).add
          (summable_zetaBoundaryWeight hx)), fun u => ?_⟩
  -- Split the trace into the target trace, the prime defect and the prime-power defect.
  set L : ℝ → ℝ := fun x =>
    (LSeries (fun n => (primeRoundError g n : ℂ)) (((1 + x : ℝ) : ℂ) + (u : ℂ) * I)).re
  set T : ℝ → ℝ := fun x =>
    ∑' n, powerDefect (roundMult g) g x n * Real.cos (logFrequency n * u)
  have hsplit : ∀ x, 0 < x → cosineTrace (intWeight (roundMult g) x) logFrequency u =
      cosineTrace (fun n => zetaBoundaryWeight x n * g n) logFrequency u + L x + T x := by
    intro x hx
    have hA := summable_cosineTrace_terms (hD.nonneg x hx) (hD.summable x hx) logFrequency u
    have hBs : Summable fun n =>
        primeRoundError g n * (n : ℝ) ^ (-(1 + x)) * Real.cos (logFrequency n * u) := by
      refine Summable.of_norm_bounded (summable_zetaBoundaryWeight hx) fun n => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), zetaBoundaryWeight]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _) |>.trans
        (mul_le_mul_of_nonneg_right (abs_primeRoundError_le hg n)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    have hCs : Summable fun n =>
        powerDefect (roundMult g) g x n * Real.cos (logFrequency n * u) := by
      refine Summable.of_norm_bounded (hR.mul_left (2 * M + 1)) fun n => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _) |>.trans (hmz x hx n)
    have hL : L x = ∑' n,
        primeRoundError g n * (n : ℝ) ^ (-(1 + x)) * Real.cos (logFrequency n * u) := by
      have hS : LSeriesSummable (fun n => (primeRoundError g n : ℂ))
          (((1 + x : ℝ) : ℂ) + (u : ℂ) * I) := by
        refine Summable.of_norm_bounded
          (summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt
            (s := ((1 + x : ℝ) : ℂ) + (u : ℂ) * I) (by simp; linarith)))
          fun n => LSeries.norm_term_le _ ?_
        rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact abs_primeRoundError_le hg n
      simp only [L, LSeries, Complex.re_tsum hS, re_term_primeRoundError]
    unfold cosineTrace
    rw [hL, ← Summable.tsum_add hA hBs, ← Summable.tsum_add (hA.add hBs) hCs]
    refine tsum_congr fun n => ?_
    rw [intWeight_roundMult_eq]
    ring
  -- Both defects stay bounded as `x ↓ 0`.
  have hLb : ∀ x, 0 < x → x ≤ 1 → |L x| ≤ (2 + |u|) * 8 := by
    intro x hx hx1
    have hre : (((1 + x : ℝ) : ℂ) + (u : ℂ) * I).re = 1 + x := by simp
    have hnorm : ‖((1 + x : ℝ) : ℂ) + (u : ℂ) * I‖ ≤ 2 + |u| := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have hb := norm_LSeries_primeRoundError_le hg (s := ((1 + x : ℝ) : ℂ) + (u : ℂ) * I)
      (by rw [hre]; linarith)
    rw [hre] at hb
    have h8 : 4 / (1 + x - 1 / 2) ≤ 8 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    calc |L x| ≤ ‖LSeries (fun n => (primeRoundError g n : ℂ))
          (((1 + x : ℝ) : ℂ) + (u : ℂ) * I)‖ := Complex.abs_re_le_norm _
      _ ≤ _ := hb
      _ ≤ (2 + |u|) * 8 :=
        mul_le_mul hnorm h8 (div_nonneg (by norm_num) (by linarith)) (by positivity)
  have hTb : ∀ x, 0 < x → |T x| ≤ (2 * M + 1) * R := by
    intro x hx
    have hCs : Summable fun n =>
        ‖powerDefect (roundMult g) g x n * Real.cos (logFrequency n * u)‖ := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
        (hR.mul_left (2 * M + 1))
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _) |>.trans (hmz x hx n)
    calc |T x| = ‖T x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' n, ‖powerDefect (roundMult g) g x n * Real.cos (logFrequency n * u)‖ :=
        norm_tsum_le_tsum_norm hCs
      _ ≤ ∑' n : ℕ, (2 * M + 1) * (if n.Prime then 0 else
            (1 + Real.log n) ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) / n) := by
        refine Summable.tsum_le_tsum (fun n => ?_) hCs (hR.mul_left _)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _) |>.trans
          (hmz x hx n)
      _ = (2 * M + 1) * R := tsum_mul_left
  have hzero : ∀ {F : ℝ → ℝ} {B : ℝ}, (∀ x, 0 < x → x ≤ 1 → |F x| ≤ B) →
      Tendsto (fun x => x * F x) (𝓝[>] 0) (𝓝 0) := by
    intro F B hF
    have hlin : Tendsto (fun x : ℝ => x * B) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const B).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlin
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx.1]
    exact mul_le_mul_of_nonneg_left (hF x hx.1 hx.2) hx.1.le
  have hlim := ((hD.tendsto u).add (hzero hLb)).add (hzero fun x hx _ => hTb x hx)
  rw [add_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [hsplit x hx]
  ring

variable {D : ℝ → ℝ}

/-- **Integral Bochner theorem.** A locally finite `D` is the boundary divisor of an Euler product
`Π_p (1 − p^{−s})^{−m(p)}` with exponents `m(p) ∈ ℕ` iff it is even and positive definite. -/
theorem integral_bochner (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) :
    IsEvenPosDef D ↔ ∃ m : ℕ → ℕ, IsBoundaryDivisor logFrequency (intWeight m) D := by
  refine ⟨fun hpd => ⟨_, IsBoundaryDivisor.round_log
    (g := fun n => arithProfile hloc (logFrequency n))
    (fun n => arithProfile_nonneg hpd hloc (Real.log_natCast_nonneg n))
    (M := 2 * D 0 * blockSize hloc 0) (fun n => ?_) (arithmetic_isBoundaryDivisor hpd hloc)⟩,
    fun ⟨_, hm⟩ => hm.isEvenPosDef⟩
  have h : arithProfile hloc (logFrequency n) ≤ 2 * D 0 * (blockSize hloc 0 + logFrequency n) :=
    arithProfile_le hpd hloc (Real.log_natCast_nonneg n)
  have hS := one_le_blockSize hloc 0
  have hl : 0 ≤ logFrequency n := Real.log_natCast_nonneg n
  have hD0 := hpd.apply_zero_nonneg
  have h3 := mul_nonneg (mul_nonneg hD0 hl) (sub_nonneg.mpr hS)
  have e : 2 * D 0 * blockSize hloc 0 * (1 + logFrequency n) - 2 * D 0 * (blockSize hloc 0 + logFrequency n) =
      2 * (D 0 * logFrequency n * (blockSize hloc 0 - 1)) := by ring
  linarith

end GaloisForLFunctions.MultiplicativePositivityGeometry
