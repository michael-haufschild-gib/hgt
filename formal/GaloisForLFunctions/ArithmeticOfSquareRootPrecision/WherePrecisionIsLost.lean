import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheIntegralityExponentIsTheZeroWidth

/-!
# Where precision is lost: the Chebyshev ledger

Chebyshev's method computes the count from an identity. Each step has its own precision:

1. **The identity is exact** (`chebyshevTransform_vonMangoldt`). The Chebyshev transform
   `T_a(n) = Σ_{d ≤ n} a(d) ⌊n/d⌋` of `Λ` is `log n!`. It determines the weight
   (`eq_of_chebyshevTransform_eq`): its precision class is `{0}`. Every nonzero nonnegative
   perturbation, even at a single point `d₀`, moves it by at least `δ(d₀)⌊n/d₀⌋`, a linear amount
   (`chebyshevTransform_ge_of_nonneg`), while the count does not see finite modifications at all.
2. **The identity is known at precision `log n`** (`log_factorial_sub_bounds`, Stirling):
   `0 < log n! − (n log n − n) ≤ 1 + ½ log n`.
3. **The count is the Möbius inversion of the identity** (`partialSum_eq_sum_moebius`,
   `psi_eq_sum_moebius_log_factorial`): `A(n) = Σ_{k ≤ n} μ(k) T_a(⌊n/k⌋)`, and so
   `ψ(n) = Σ_{k ≤ n} μ(k) log ⌊n/k⌋!`.
4. **Inversion is unbounded at every precision** (`exists_inversion_amplification`,
   `not_inversion_bounded`). For every `θ ≥ 0` and `x ≥ 1` some error `E` with `|E(y)| ≤ y^θ` is
   inverted to `Σ_{k ≤ x} μ(k) E(x/k) ≥ π(x)`; no bound `C x^{θ'}` with `θ' < 1` holds uniformly.

All precision is lost in step 4. A power saving for `ψ` through this route must use the
arithmetic of the specific Stirling error together with cancellation in `μ`; no size bound on the
error of the identity can be transported through the inversion.
-/

noncomputable section

open Real Finset Filter Asymptotics
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- A weight as an arithmetic function (value `0` at `0`). -/
def weightFun (a : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else a n, if_pos rfl⟩

theorem weightFun_apply {a : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) : weightFun a n = a n := if_neg hn

theorem weightFun_vonMangoldt : weightFun vonMangoldtWeight = vonMangoldt := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [weightFun]
  · exact weightFun_apply hn

/-- The **Chebyshev transform** `T_a(n) = Σ_{d ≤ n} a(d) ⌊n/d⌋`. -/
def chebyshevTransform (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ d ∈ Ioc 0 n, a d * ((n / d : ℕ) : ℝ)

/-- `T_a` is the partial sum of `a ∗ 1`. -/
theorem chebyshevTransform_eq_sum_mul_zeta (a : ℕ → ℝ) (n : ℕ) :
    chebyshevTransform a n = ∑ m ∈ Ioc 0 n, (weightFun a * ArithmeticFunction.zeta) m := by
  rw [ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
  exact sum_congr rfl fun d hd => by rw [weightFun_apply (by have := (mem_Ioc.mp hd).1; omega)]

/-- **The count is the Möbius inversion of the identity**: `A(n) = Σ_{k ≤ n} μ(k) T_a(⌊n/k⌋)`. -/
theorem partialSum_eq_sum_moebius (a : ℕ → ℝ) (n : ℕ) :
    partialSum a n = ∑ k ∈ Ioc 0 n, (ArithmeticFunction.moebius k : ℝ) *
      chebyshevTransform a (n / k) := by
  have hA : weightFun a = (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
      (weightFun a * ArithmeticFunction.zeta) := by
    rw [mul_comm (weightFun a), ← mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]
  have h1 : partialSum a n = ∑ m ∈ Ioc 0 n, weightFun a m := by
    unfold partialSum
    rw [Nat.floor_natCast]
    exact sum_congr rfl fun m hm => (weightFun_apply (by have := (mem_Ioc.mp hm).1; omega)).symm
  rw [h1, hA, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [chebyshevTransform_eq_sum_mul_zeta, ArithmeticFunction.intCoe_apply]

/-- `Σ_{m ≤ n} log m = log n!`. -/
theorem sum_log_eq_log_factorial (n : ℕ) :
    ∑ m ∈ Ioc 0 n, Real.log m = Real.log (n.factorial : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos n).ne'), add_comm]

/-- **The Chebyshev identity**: `T_Λ(n) = log n!`. -/
theorem chebyshevTransform_vonMangoldt (n : ℕ) :
    chebyshevTransform vonMangoldtWeight n = Real.log (n.factorial : ℕ) := by
  rw [chebyshevTransform_eq_sum_mul_zeta, weightFun_vonMangoldt,
    ArithmeticFunction.vonMangoldt_mul_zeta, ← sum_log_eq_log_factorial]
  exact sum_congr rfl fun m _ => ArithmeticFunction.log_apply

/-- **The Chebyshev–Möbius formula**: `ψ(n) = Σ_{k ≤ n} μ(k) log ⌊n/k⌋!`. -/
theorem psi_eq_sum_moebius_log_factorial (n : ℕ) :
    Chebyshev.psi n = ∑ k ∈ Ioc 0 n, (ArithmeticFunction.moebius k : ℝ) *
      Real.log ((n / k).factorial : ℕ) := by
  rw [← partialSum_vonMangoldt, partialSum_eq_sum_moebius]
  exact sum_congr rfl fun k _ => by rw [chebyshevTransform_vonMangoldt]

/-- **The identity determines the weight**: two weights with the same Chebyshev transform agree on
`n ≥ 1`. The precision class of the identity is `{0}`. -/
theorem eq_of_chebyshevTransform_eq {a b : ℕ → ℝ}
    (h : ∀ n, chebyshevTransform a n = chebyshevTransform b n) {n : ℕ} (hn : 1 ≤ n) :
    a n = b n := by
  have hps : ∀ m : ℕ, partialSum a m = partialSum b m := fun m => by
    rw [partialSum_eq_sum_moebius, partialSum_eq_sum_moebius]
    exact sum_congr rfl fun k _ => by rw [h]
  have hs : ∀ m : ℕ, partialSum a (m + 1 : ℕ) - partialSum a m = a (m + 1) := fun m => by
    unfold partialSum; rw [Nat.floor_natCast, Nat.floor_natCast, sum_Ioc_succ_top (Nat.zero_le m)]
    ring
  have hs' : ∀ m : ℕ, partialSum b (m + 1 : ℕ) - partialSum b m = b (m + 1) := fun m => by
    unfold partialSum; rw [Nat.floor_natCast, Nat.floor_natCast, sum_Ioc_succ_top (Nat.zero_le m)]
    ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← hs, ← hs', hps, hps]

/-- **Linear visibility.** A nonnegative perturbation positive at `d₀` moves the Chebyshev
transform by at least `δ(d₀) ⌊n/d₀⌋`. -/
theorem chebyshevTransform_ge_of_nonneg {δ : ℕ → ℝ} (hδ : ∀ d, 0 ≤ δ d) {d₀ n : ℕ}
    (hd₀ : 1 ≤ d₀) (hn : d₀ ≤ n) : δ d₀ * ((n / d₀ : ℕ) : ℝ) ≤ chebyshevTransform δ n :=
  single_le_sum (f := fun d => δ d * ((n / d : ℕ) : ℝ))
    (fun d _ => mul_nonneg (hδ d) (Nat.cast_nonneg _)) (mem_Ioc.mpr ⟨hd₀, hn⟩)

/-- **The identity is known at precision `log n`** (Stirling):
`0 < log n! − (n log n − n) ≤ 1 + ½ log n` for `n ≥ 1`. -/
theorem log_factorial_sub_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 < Real.log (n.factorial : ℕ) - (n * Real.log n - n) ∧
      Real.log (n.factorial : ℕ) - (n * Real.log n - n) ≤ 1 + Real.log n / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hf := Stirling.log_stirlingSeq_formula n
  have hlo : Real.log √π ≤ Real.log (Stirling.stirlingSeq n) :=
    Real.log_le_log (by positivity) (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  have hhi : Real.log (Stirling.stirlingSeq n) ≤ Real.log (Stirling.stirlingSeq 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact Real.log_le_log (lt_of_lt_of_le (by positivity) (Stirling.sqrt_pi_le_stirlingSeq
      (by omega))) (Stirling.stirlingSeq'_antitone (Nat.zero_le m))
  rw [Stirling.stirlingSeq_one, Real.log_div (exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num)] at hhi
  have hpi : 0 < Real.log √π := Real.log_pos (by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [pi_gt_three]))
  have hlog : Real.log (n / exp 1) = Real.log n - 1 := by
    rw [Real.log_div hn0.ne' (exp_pos 1).ne', Real.log_exp]
  have h2n : Real.log (2 * n) = Real.log 2 + Real.log n := Real.log_mul (by norm_num) hn0.ne'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [hlog, h2n] at hf
  constructor <;> nlinarith [Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ n)]

/-! ### Inversion is unbounded at every precision -/

/-- The **inversion operator** `I_x(E) = Σ_{k ≤ x} μ(k) E(x/k)`; `ψ(n) = I_n(log ⌊·⌋!)`. -/
def inversionOp (E : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Ioc 0 ⌊x⌋₊, (ArithmeticFunction.moebius k : ℝ) * E (x / k)

/-- **Inversion amplification.** For `θ ≥ 0`, `x ≥ 1` some error `E` with `|E(y)| ≤ y^θ` is inverted
to at least `π(x)`. -/
theorem exists_inversion_amplification {θ : ℝ} (hθ : 0 ≤ θ) {x : ℝ} (hx : 1 ≤ x) :
    ∃ E : ℝ → ℝ, (∀ y : ℝ, 0 < y → |E y| ≤ y ^ θ) ∧
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ inversionOp E x := by
  have hx0 : 0 < x := by linarith
  refine ⟨fun y => (ArithmeticFunction.moebius ⌊x / y⌋₊ : ℝ) * y ^ θ, fun y hy => ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hy.le θ)]
    refine mul_le_of_le_one_left (Real.rpow_nonneg hy.le θ) ?_
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · have hterm : ∀ k ∈ Ioc 0 ⌊x⌋₊, (ArithmeticFunction.moebius k : ℝ) *
        ((ArithmeticFunction.moebius ⌊x / (x / k)⌋₊ : ℝ) * (x / k) ^ θ) =
          (ArithmeticFunction.moebius k : ℝ) ^ 2 * (x / k) ^ θ := by
      intro k hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Ioc.mp hk).1
      rw [div_div_cancel₀ hx0.ne', Nat.floor_natCast]; ring
    unfold inversionOp
    rw [sum_congr rfl hterm]
    have hprime : (Nat.primeCounting ⌊x⌋₊ : ℝ) =
        ∑ k ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) := by
      rw [sum_const, nsmul_eq_mul, mul_one, ← Nat.primesLE_card_eq_primeCounting]
      congr 2
      ext p
      simp only [mem_filter, mem_Ioc, Nat.mem_primesLE]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, h1⟩, h2⟩
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
    rw [hprime]
    calc ∑ k ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ)
        ≤ ∑ k ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime,
            (ArithmeticFunction.moebius k : ℝ) ^ 2 * (x / k) ^ θ := by
          refine sum_le_sum fun k hk => ?_
          obtain ⟨hk1, hkp⟩ := mem_filter.mp hk
          rw [ArithmeticFunction.moebius_apply_prime hkp]
          have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Ioc.mp hk1).1
          have hkx : (k : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Ioc.mp hk1).2).trans (Nat.floor_le hx0.le)
          have : 1 ≤ (x / k) ^ θ := Real.one_le_rpow ((one_le_div hk0).mpr hkx) hθ
          norm_num; exact this
      _ ≤ ∑ k ∈ Ioc 0 ⌊x⌋₊, (ArithmeticFunction.moebius k : ℝ) ^ 2 * (x / k) ^ θ :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k hk _ => by
            have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Ioc.mp hk).1
            exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) θ)

/-- **No size bound survives inversion**: for `θ ≥ 0` and `θ' < 1` there is no `C` with
`|I_x(E)| ≤ C x^{θ'}` for all `x ≥ 1` and all `E` with `|E(y)| ≤ y^θ`. -/
theorem not_inversion_bounded {θ θ' : ℝ} (hθ : 0 ≤ θ) (hθ' : θ' < 1) :
    ¬ ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ E : ℝ → ℝ, (∀ y : ℝ, 0 < y → |E y| ≤ y ^ θ) →
      |inversionOp E x| ≤ C * x ^ θ' := by
  rintro ⟨C, hC⟩
  -- `π(x) ≥ ((x − 1) log 2 − log(x + 2)) / log x` is eventually larger than `C x^{θ'}`
  set b := (θ' + 1) / 2
  have hb : θ' < b := by simp only [b]; linarith
  have hb1 : b < 1 := by simp only [b]; linarith
  have hlogo : (fun x : ℝ => Real.log x) =o[atTop] fun x => x ^ (1 - b) :=
    isLittleO_log_rpow_atTop (by linarith)
  have h1 := eventually_mul_rpow_lt_rpow hb C
  have h2 := hlogo.def (c := Real.log 2 / 8) (by positivity)
  have h3 := (isLittleO_log_rpow_atTop (r := 1) one_pos).def (c := Real.log 2 / 8) (by positivity)
  obtain ⟨x, ⟨⟨⟨h1x, h2x⟩, h3x⟩, hx4⟩, hx5⟩ := (((h1.and h2).and h3).and
    (eventually_ge_atTop (8 : ℝ))).and (eventually_ge_atTop (exp 1)) |>.exists
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨E, hE, hEbig⟩ := exists_inversion_amplification hθ hx1.le
  have hpi := Chebyshev.pi_ge' hx1
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hl1 : 1 ≤ Real.log x := by rw [← Real.log_exp 1]; exact Real.log_le_log (exp_pos 1) hx5
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper := (le_abs_self _).trans (hC x hx1.le E hE)
  -- `log x ≤ (log 2/8) x^{1−b}` and `log (x + 2) ≤ log (2x) ≤ log 2 + (log 2/8) x`
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlx,
    abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at h2x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlx, Real.rpow_one, abs_of_pos hx0] at h3x
  have hx2 : Real.log (x + 2) ≤ Real.log 2 + Real.log 2 / 8 * x := by
    calc Real.log (x + 2) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ Real.log 2 + Real.log 2 / 8 * x := by linarith
  -- assemble: `π(x) ≥ (log 2/2) x / log x ≥ 4 x^b`, while `π(x) ≤ C x^{θ'} < x^b`
  have hsplit : x = x ^ b * x ^ (1 - b) := by rw [← Real.rpow_add hx0]; simp
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  have hnum : Real.log 2 / 2 * x ≤ (x - 1) * Real.log 2 - Real.log (x + 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hx4 hl2.le]
  have hpi2 : Real.log 2 / 2 * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) :=
    le_trans (div_le_div_of_nonneg_right hnum hlx.le) hpi
  have hbig : 4 * x ^ b ≤ Real.log 2 / 2 * x / Real.log x := by
    rw [le_div_iff₀ hlx]
    calc 4 * x ^ b * Real.log x ≤ 4 * x ^ b * (Real.log 2 / 8 * x ^ (1 - b)) := by gcongr
      _ = Real.log 2 / 2 * (x ^ b * x ^ (1 - b)) := by ring
      _ = Real.log 2 / 2 * x := by rw [← hsplit]
  linarith

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
