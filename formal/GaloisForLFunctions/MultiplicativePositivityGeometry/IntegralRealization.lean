import GaloisForLFunctions.MultiplicativePositivityGeometry.ProfileCharacterization
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryCompleteness
import GaloisForLFunctions.RHTower.PrimeDeletionLogDerivativeCeiling
import GaloisForLFunctions.RHTower.WeilPrimeDeficitSetRigidity

/-!
# Integral realization: Euler products with integer exponents realize every boundary profile

For `m : ℕ → ℕ`, the Euler product `Z_m(s) = Π_p (1 − p^{−s})^{−m(p)}` has nonnegative integer
Dirichlet coefficients. Its logarithmic derivative has coefficient `m(p) Λ(n)` at `n = p^k`
(`intWeight`); in the boundary calculus it is the sum, over the primes `p`, of `m(p)` copies of the
one-prime factor `(1 − p^{−s})^{−1}`.

**Rounding preserves the boundary divisor** (`IsBoundaryDivisor.round`). Let `0 ≤ g ≤ M`. Round
`g(p)` to `m(p) ∈ {⌊g(p)⌋, ⌈g(p)⌉}`, upwards exactly when the running error
`E(n) = Σ_{p ≤ n} log p · (m(p) − g(p))` is negative. Then `|E(n)| ≤ log(n + 1)`
(`abs_roundError_le`). By Abel summation the error series `Σ_p log p (m(p) − g(p)) p^{−s}` is
`s ∫₁^∞ E(t) t^{−s−1} dt`, bounded on `Re s = 1 + x` uniformly as `x ↓ 0`; prime powers carry
bounded mass. So the weights `m(p) Λ(n)` and `g(n) Λ(n)` have the same boundary divisor.

Consequences:
* every nonnegative cosine polynomial `P` is realized by an integral Euler product: the greedy
  rounding of `P(t₀ log p)` has the twisted divisor `Σ_k (a_k/2)(δ_{kt₀} + δ_{−kt₀})`
  (`integral_isBoundaryDivisor`);
* a finitely supported even profile is the boundary profile of an Euler product with nonnegative
  integer exponents iff it is positive definite (`integral_boundary_profile_iff`);
* integer exponents `m(p) ∈ {0, 1, 2}` already give a simple pole at `1` and half zeros at `1 ± i`
  (`integral_half_zero`). The value `−1/2` is not the order of a meromorphic function, so this
  product has no meromorphic continuation across `Re s = 1`.

Integrality of the Euler product therefore imposes no boundary constraint beyond positive
definiteness. The boundary invariant (Z) is a statement about meromorphic continuation, not about
integrality of the prime data.
-/

open Finset Filter Topology Complex Asymptotics MeasureTheory

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-! ### Greedy rounding with a logarithmic running error -/

/-- Round `y` up when the running error `E` is negative, down otherwise. -/
noncomputable def roundStep (E y : ℝ) : ℕ := if E < 0 then ⌈y⌉₊ else ⌊y⌋₊

/-- Running error `Σ_{p ≤ n} log p · (m(p) − g(p))` of the greedy rounding of `g` at the primes. -/
noncomputable def roundError (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => roundError g n + if (n + 1).Prime then
      Real.log ((n + 1 : ℕ) : ℝ) * ((roundStep (roundError g n) (g (n + 1)) : ℝ) - g (n + 1))
    else 0

/-- The greedy integer exponent at `n`. -/
noncomputable def roundMult (g : ℕ → ℝ) (n : ℕ) : ℕ := roundStep (roundError g (n - 1)) (g n)

/-- The prime rounding defect `log p · (m(p) − g(p))`, zero off the primes. -/
noncomputable def primeRoundError (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n.Prime then Real.log n * ((roundMult g n : ℝ) - g n) else 0

theorem roundStep_sub_mem {E y : ℝ} (hy : 0 ≤ y) :
    (E < 0 → 0 ≤ (roundStep E y : ℝ) - y ∧ (roundStep E y : ℝ) - y < 1) ∧
      (0 ≤ E → -1 < (roundStep E y : ℝ) - y ∧ (roundStep E y : ℝ) - y ≤ 0) := by
  constructor
  · intro hE
    rw [roundStep, if_pos hE]
    exact ⟨sub_nonneg.mpr (Nat.le_ceil y), by linarith [Nat.ceil_lt_add_one hy]⟩
  · intro hE
    rw [roundStep, if_neg (not_lt.mpr hE)]
    exact ⟨by linarith [Nat.lt_floor_add_one y], sub_nonpos.mpr (Nat.floor_le hy)⟩

theorem abs_roundStep_sub_lt (E : ℝ) {y : ℝ} (hy : 0 ≤ y) : |(roundStep E y : ℝ) - y| < 1 := by
  rcases lt_or_ge E 0 with hE | hE
  · obtain ⟨h1, h2⟩ := (roundStep_sub_mem (E := E) hy).1 hE
    exact abs_lt.mpr ⟨by linarith, h2⟩
  · obtain ⟨h1, h2⟩ := (roundStep_sub_mem (E := E) hy).2 hE
    exact abs_lt.mpr ⟨h1, by linarith⟩

/-- **The running error stays below `log(n + 1)`.** A negative error is pushed up by less than
`log p`, a nonnegative one down by less than `log p`. -/
theorem abs_roundError_le {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    |roundError g n| ≤ Real.log ((n : ℝ) + 1) := by
  induction n with
  | zero => simp [roundError]
  | succ n ih =>
    have hL0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 n)
    have hL1 : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (((n + 1 : ℕ) : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hmono : Real.log ((n : ℝ) + 1) ≤ Real.log (((n + 1 : ℕ) : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    rw [abs_le] at ih
    simp only [roundError]
    rw [abs_le]
    split_ifs with hp
    · set E := roundError g n
      set d := (roundStep E (g (n + 1)) : ℝ) - g (n + 1)
      obtain ⟨hneg, hpos⟩ := roundStep_sub_mem (E := E) (hg (n + 1))
      rcases lt_or_ge E 0 with hE | hE
      · obtain ⟨h1, h2⟩ := hneg hE
        have k1 := mul_nonneg hL0 h1
        have k2 := mul_nonneg hL0 (by linarith : 0 ≤ 1 - d)
        constructor <;> nlinarith
      · obtain ⟨h1, h2⟩ := hpos hE
        have k1 := mul_nonneg hL0 (by linarith : 0 ≤ d + 1)
        have k2 := mul_nonneg hL0 (by linarith : 0 ≤ -d)
        constructor <;> nlinarith
    · rw [add_zero]
      constructor <;> linarith [ih.1, ih.2]

theorem sum_primeRoundError (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, primeRoundError g k = roundError g n := by
  induction n with
  | zero => simp [roundError]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [roundError, primeRoundError, roundMult, Nat.add_sub_cancel]

theorem abs_primeRoundError_le {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    |primeRoundError g n| ≤ ArithmeticFunction.vonMangoldt n := by
  unfold primeRoundError
  split_ifs with hp
  · have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp, abs_mul, abs_of_nonneg hlog]
    exact mul_le_of_le_one_right hlog (abs_roundStep_sub_lt _ (hg n)).le
  · simp [ArithmeticFunction.vonMangoldt_nonneg]

/-! ### Abel summation bounds the defect series on the boundary -/

theorem log_add_one_le_rpow {t : ℝ} (ht : 1 ≤ t) : Real.log (t + 1) ≤ 4 * t ^ (1 / 2 : ℝ) := by
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ t + 1) (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : (t + 1) ^ (1 / 2 : ℝ) ≤ (2 * t) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h2
  have h4 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h5 := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ t) (1 / 2))
  have h6 : (t + 1) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (t + 1) ^ (1 / 2 : ℝ) := by ring
  linarith

/-- **The defect series is bounded.** For `Re s > 1`,
`‖Σ_p log p (m(p) − g(p)) p^{−s}‖ ≤ 4‖s‖/(Re s − 1/2)`. -/
theorem norm_LSeries_primeRoundError_le {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {s : ℂ}
    (hs : 1 < s.re) :
    ‖LSeries (fun n => (primeRoundError g n : ℂ)) s‖ ≤ ‖s‖ * (4 / (s.re - 1 / 2)) := by
  have hS : LSeriesSummable (fun n => (primeRoundError g n : ℂ)) s := by
    refine Summable.of_norm_bounded
      (summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt hs))
      fun n => LSeries.norm_term_le s ?_
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact abs_primeRoundError_le hg n
  have hpart : ∀ n, ∑ k ∈ Icc 1 n, (primeRoundError g k : ℂ) = (roundError g n : ℂ) :=
    fun n => by rw [← sum_primeRoundError, Complex.ofReal_sum]
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, (primeRoundError g k : ℂ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) := by
    refine IsBigO.of_bound 4 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hpart, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact (abs_roundError_le hg n).trans (log_add_one_le_rpow (by exact_mod_cast hn))
  rw [LSeries_eq_mul_integral _ (by norm_num) (by linarith) hS hO, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
  refine RHTower.IntegerBeurling.norm_integral_mul_cpow_le (fun t ht => ?_) (by linarith)
  rw [hpart, Complex.norm_real, Real.norm_eq_abs]
  have hfl : (⌊t⌋₊ : ℝ) + 1 ≤ t + 1 := by linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ t)]
  exact (abs_roundError_le hg _).trans
    ((Real.log_le_log (by positivity) hfl).trans (log_add_one_le_rpow ht))

theorem re_term_primeRoundError (g : ℕ → ℝ) (σ u : ℝ) (n : ℕ) :
    (LSeries.term (fun n => (primeRoundError g n : ℂ)) ((σ : ℂ) + (u : ℂ) * I) n).re =
      primeRoundError g n * (n : ℝ) ^ (-σ) * Real.cos (logFrequency n * u) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeRoundError, Nat.not_prime_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg, Complex.mul_re,
      RHTower.re_natCast_cpow_neg hn σ u, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, logFrequency, mul_comm (Real.log n) u]
    ring

/-! ### Rounding preserves the boundary divisor -/

/-- Weights of `Π_p (1 − p^{−s})^{−m(p)}` on `Re s = 1 + x`: `m(p) Λ(n) n^{−1−x}` at `n = p^k`. -/
noncomputable def intWeight (m : ℕ → ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  (m n.minFac : ℝ) * zetaBoundaryWeight x n

/-- The defect of the integer exponents at proper prime powers. -/
noncomputable def powerDefect (m : ℕ → ℕ) (g : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then 0 else zetaBoundaryWeight x n * ((m n.minFac : ℝ) - g n)

theorem intWeight_roundMult_eq (g : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    intWeight (roundMult g) x n = zetaBoundaryWeight x n * g n +
      primeRoundError g n * (n : ℝ) ^ (-(1 + x)) + powerDefect (roundMult g) g x n := by
  unfold intWeight powerDefect primeRoundError
  split_ifs with hp
  · rw [hp.minFac_eq, zetaBoundaryWeight, ArithmeticFunction.vonMangoldt_apply_prime hp]
    ring
  · ring

theorem zetaBoundaryWeight_le_div {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    zetaBoundaryWeight x n ≤ ArithmeticFunction.vonMangoldt n / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zetaBoundaryWeight]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [zetaBoundaryWeight, div_eq_mul_inv, ← Real.rpow_neg_one]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
    ArithmeticFunction.vonMangoldt_nonneg

/-- **Rounding preserves the boundary divisor.** If the weights `g(n) Λ(n) n^{−1−x}`, with
`0 ≤ g ≤ M`, have boundary divisor `D`, so does the Euler product `Π_p (1 − p^{−s})^{−m(p)}` with the
greedy integer exponents `m = roundMult g`. -/
theorem IsBoundaryDivisor.round {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {M : ℝ} (hgM : ∀ n, g n ≤ M)
    {D : ℝ → ℝ}
    (hD : IsBoundaryDivisor logFrequency (fun x n => zetaBoundaryWeight x n * g n) D) :
    IsBoundaryDivisor logFrequency (intWeight (roundMult g)) D := by
  have hM0 : 0 ≤ M := (hg 0).trans (hgM 0)
  -- `m(n) ≤ M + 1` everywhere.
  have hm : ∀ n, (roundMult g n : ℝ) ≤ M + 1 := fun n => by
    have := abs_roundStep_sub_lt (roundError g (n - 1)) (hg n)
    have h := (abs_lt.mp this).2
    unfold roundMult
    linarith [hgM n]
  have hmz : ∀ x, 0 < x → ∀ n, |powerDefect (roundMult g) g x n| ≤
      (2 * M + 1) * (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n / n) := by
    intro x hx n
    unfold powerDefect
    split_ifs with hp
    · simp
    · rw [abs_mul, abs_of_nonneg (zetaBoundaryWeight_nonneg x n), mul_comm]
      have h1 : |(roundMult g n.minFac : ℝ) - g n| ≤ 2 * M + 1 := by
        rw [abs_le]
        constructor <;> linarith [hm n.minFac, hg n, hgM n, (Nat.cast_nonneg _ :
          (0 : ℝ) ≤ roundMult g n.minFac)]
      exact mul_le_mul h1 (zetaBoundaryWeight_le_div hx.le n) (zetaBoundaryWeight_nonneg x n)
        (by linarith)
  have hR := RHTower.WeilPrimeDeficit.summable_nonprime_vonMangoldt_div
  set R := ∑' n : ℕ, (if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℝ) / n)
  refine ⟨fun x _ n => mul_nonneg (Nat.cast_nonneg _) (zetaBoundaryWeight_nonneg x n),
    fun x hx => Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg _) (zetaBoundaryWeight_nonneg x n))
      (fun n => mul_le_mul_of_nonneg_right (hm _) (zetaBoundaryWeight_nonneg x n))
      ((summable_zetaBoundaryWeight hx).mul_left (M + 1)), fun u => ?_⟩
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
  -- The two defects stay bounded as `x ↓ 0`.
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
      _ ≤ ∑' n, (2 * M + 1) * (if n.Prime then 0 else
            (ArithmeticFunction.vonMangoldt n : ℝ) / n) := by
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

/-! ### Integral realization of every boundary profile -/

/-- The cosine polynomial `P(t₀ log n)` sampled at the integers. -/
noncomputable def twistSample (a : ℕ → ℝ) (K : ℕ) (t₀ : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.cosinePolynomial a K (t₀ * logFrequency n)

/-- Greedy integer exponents tracking `P(t₀ log p)`. -/
noncomputable def twistRound (a : ℕ → ℝ) (K : ℕ) (t₀ : ℝ) : ℕ → ℕ :=
  roundMult (twistSample a K t₀)

theorem twistRound_close {a : ℕ → ℝ} {K : ℕ} (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ)
    (t₀ : ℝ) (n : ℕ) :
    |(twistRound a K t₀ n : ℝ) - HTGeometry.cosinePolynomial a K (t₀ * logFrequency n)| < 1 :=
  abs_roundStep_sub_lt _ (hP _)

/-- **Integral realization.** For a nonnegative cosine polynomial `P`, the Euler product
`Π_p (1 − p^{−s})^{−m(p)}` with the greedy integer exponents `m(p) ≈ P(t₀ log p)` has the twisted
boundary divisor `Σ_k (a_k/2)(δ_{kt₀} + δ_{−kt₀})`. -/
theorem integral_isBoundaryDivisor {a : ℕ → ℝ} {K : ℕ}
    (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ) (t₀ : ℝ) :
    IsBoundaryDivisor logFrequency (intWeight (twistRound a K t₀)) (twistedDivisor a K t₀) :=
  IsBoundaryDivisor.round (fun _ => hP _)
    (fun _ => (le_abs_self _).trans (abs_cosinePolynomial_le a K _))
    (twisted_isBoundaryDivisor hP t₀)

/-- **Profiles of integral Euler products.** A finitely supported even profile on `ℤ` is the
progression profile of the boundary divisor of an Euler product with nonnegative integer exponents
iff its cosine polynomial is nonnegative. -/
theorem integral_boundary_profile_iff {d : ℤ → ℝ} {K : ℕ} (hev : ∀ m, d (-m) = d m)
    (hsupp : ∀ m : ℤ, (K : ℤ) < |m| → d m = 0) :
    (∃ (mult : ℕ → ℕ) (D : ℝ → ℝ) (t₀ : ℝ),
        IsBoundaryDivisor logFrequency (intWeight mult) D ∧ ∀ m : ℤ, D (m * t₀) = d m) ↔
      ∀ θ, 0 ≤ HTGeometry.cosinePolynomial (profileCoeff d) K θ := by
  constructor
  · rintro ⟨mult, D, t₀, hD, hd⟩
    exact (boundary_profile_iff hev hsupp).mp ⟨_, _, D, t₀, hD, hd⟩
  · intro hP
    exact ⟨twistRound (profileCoeff d) K 1, _, 1, integral_isBoundaryDivisor hP 1,
      fun m => by rw [mul_one]; exact twistedDivisor_profileCoeff hev hsupp hP m⟩

/-- **Integral Euler products with half zeros.** Exponents `m(p) ∈ {0, 1, 2}` rounding
`1 − cos(log p)` give a simple pole at `1`, no other boundary pole, and boundary divisor `−1/2` at
`1 ± i`. -/
theorem integral_half_zero :
    ∃ mult : ℕ → ℕ, (∀ n, mult n ≤ 2) ∧ ∃ D : ℝ → ℝ,
      IsBoundaryDivisor logFrequency (intWeight mult) D ∧ D 0 = 1 ∧
        (∀ u, u ≠ 0 → D u ≤ 0) ∧ D 1 = -1 / 2 := by
  refine ⟨twistRound halfZeroCoeff 1 1, fun n => ?_, twistedDivisor halfZeroCoeff 1 1,
    integral_isBoundaryDivisor halfZeroCoeff_nonneg_poly 1,
    twistedDivisor_zero _ _ one_ne_zero, fun u hu => twistedDivisor_nonpos ?_ 1 hu, ?_⟩
  · have hc := (abs_lt.mp (twistRound_close halfZeroCoeff_nonneg_poly 1 n)).2
    have hb := (le_abs_self _).trans (abs_cosinePolynomial_le halfZeroCoeff 1 (1 * logFrequency n))
    have h2 : ∑ k ∈ range (1 + 1), |halfZeroCoeff k| = 2 := by
      simp [Finset.sum_range_succ, halfZeroCoeff]
      norm_num
    rw [h2] at hb
    have h3 : (twistRound halfZeroCoeff 1 1 n : ℝ) < 3 := by linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast h3)
  · intro k hk
    rcases k with _ | _ | k
    · omega
    · norm_num [halfZeroCoeff]
    · simp [halfZeroCoeff]
  · rw [twistedDivisor_one_at_one]
    norm_num [halfZeroCoeff]

end GaloisForLFunctions.MultiplicativePositivityGeometry
