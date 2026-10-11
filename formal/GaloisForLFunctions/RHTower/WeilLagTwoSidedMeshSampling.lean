import GaloisForLFunctions.RHTower.WeilLagDenseSampling
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.RHTower.Sieve.AdaptiveGallagherBrunTitchmarsh
import GaloisForLFunctions.RHTower.WeilLagPrimeQuadraticMesh

/-!
# Lag sampling at the square-root scale: the squares decide the Riemann hypothesis

The integer lags `a_n = Φ(log n) = E(n)/√n` have Lipschitz scale `√n`:

`|a_m − a_n| ≤ 3620 (1 + (m − n)/√n)`  for `2 ≤ n ≤ m ≤ 2n` (`abs_integerLag_sub_le_sqrt`).

**Inputs.**
* Mertens' first theorem `|Σ_{d≤n} Λ(d)/d − log n| ≤ log 4 + 4` and Chebyshev's `ψ(x) ≤ (log 4 + 4)x`
  give `|E(n)| ≤ 20n`.
* Brun–Titchmarsh bounds the primes in `(n, n + H]` by `292 H'/log H'` with `H' = max(H, √n)`.
* A prime power `p^k`, `k ≥ 2`, in `(n, 2n]` is determined by `p ≤ √(2n)`, because `p^{k+1} ≥ 2p^k`.
  So the prime powers in the window weigh at most `θ(√(2n)) ≤ 6√(2n)`.
* Together, `ψ(n + H) − ψ(n) ≤ 1168(H + √n) + 6√(2n)` (`psi_window_le_sqrt`).

**Theorem** (`riemannHypothesis_iff_integerLag_bddBelow_of_sqrt_gaps`). If `A ⊆ ℕ` meets every
window `[n − K√n, n]` for large `n`, then the Riemann hypothesis holds iff the lags along `A` are
bounded below, and iff they are bounded above. In particular RH holds iff the lags at the perfect
squares are bounded below (`riemannHypothesis_iff_integerLag_sq_bddBelow`). This extends the syndetic
sampling theorem of `WeilLagDenseSampling` from bounded gaps to gaps of size `O(√n)`.

**Lower interpolation on quadratic meshes** (`integerLag_bddBelow_of_quadraticMesh`). The exact
lag chord balance `√k a_k − u√n a_n − v√m a_m = (log defect) − (prime charge) − (trivial-zero deficit)`
(`sqrt_integerLag_chord_exact`) has a nonnegative log defect and a deficit at most `1`. The prime
charge is at most `(ψ(m) − ψ(n))(m − n)/n`, which the window bound makes `O(√n)` whenever
`(m − n)² ≤ C n√n`. Hence `a_k ≥ min(0, a_n, a_m) − B` on every quadratic lag mesh. Together with
the upper chord interpolation `integerLag_bddAbove_of_quadraticMesh`, the lag criterion is
symmetric on meshes of gap `O(n^{3/4})`: RH holds iff the lags along the mesh are bounded below, iff
they are bounded above (`riemannHypothesis_iff_integerLag_bddBelow_of_quadraticMesh`,
`riemannHypothesis_iff_integerLag_bddAbove_of_quadraticMesh`). This supersedes the square-root
sampling theorems above, which remain as the two-sided Lipschitz form.
-/

open Real Filter
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## The bracket is linear -/

theorem log_four_add_four_le_six : Real.log 4 + 4 ≤ 6 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

theorem abs_mertensSum_sub_log_le {k : ℕ} (hk : 1 ≤ k) :
    |mertensSum k - Real.log k| ≤ 6 :=
  (Mertens.mertens_first k hk).trans log_four_add_four_le_six

theorem psi_nat_le_six_mul (k : ℕ) : Chebyshev.psi k ≤ 6 * k :=
  (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg k)).trans
    (mul_le_mul_of_nonneg_right log_four_add_four_le_six (Nat.cast_nonneg k))

theorem psi_nat_nonneg (k : ℕ) : 0 ≤ Chebyshev.psi k := by
  rw [Chebyshev.psi_eq_sum_Icc]
  exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- **The lag bracket is linear:** `|E(k)| ≤ 20k`. -/
theorem abs_lagBracket_le_linear {k : ℕ} (hk : 2 ≤ k) : |lagBracket k| ≤ 20 * k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hψ := psi_nat_le_six_mul k
  have hψ0 := psi_nat_nonneg k
  have hM := abs_mertensSum_sub_log_le (by omega : 1 ≤ k)
  have hγ : eulerMascheroniConstant ≤ 1 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds; linarith
  have hγ0 : 0 ≤ eulerMascheroniConstant := by have := eulerMascheroniConstant_gt; linarith
  have hS0 : 0 ≤ trivialZeroSeriesReal k := trivialZeroSeriesReal_nonneg hk1
  have hS1 : trivialZeroSeriesReal k ≤ 1 := trivialZeroSeriesReal_le_one hk1
  have hlog2π : Real.log (2 * Real.pi) ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
    have := Real.pi_lt_d2
    linarith
  have hlog2π0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hdev : |mertensSum k - Real.log k + eulerMascheroniConstant| ≤ 7 := by
    rw [abs_le] at hM ⊢; constructor <;> linarith [hM.1, hM.2]
  have hkdev : |(k : ℝ) * (mertensSum k - Real.log k + eulerMascheroniConstant)| ≤ 7 * k := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < k)]
    nlinarith
  unfold lagBracket
  rw [abs_le]
  have h1 := (abs_le.mp hkdev).1
  have h2 := (abs_le.mp hkdev).2
  constructor <;> nlinarith

/-! ## Chebyshev's function on a square-root window -/

/-- The prime powers `p^k`, `k ≥ 2`, in `(n, 2n]` have pairwise distinct smallest prime factors,
all at most `√(2n)`; so their von Mangoldt weight is at most `ψ(√(2n)) ≤ 6√(2n)`. -/
theorem sum_vonMangoldt_window_not_prime_le {n m : ℕ} (hnm : m ≤ 2 * n) :
    ∑ k ∈ Finset.Ioc n m with ¬ k.Prime, vonMangoldt k ≤ 6 * Real.sqrt (2 * n) := by
  classical
  set S := (Finset.Ioc n m).filter fun k => ¬ k.Prime ∧ IsPrimePow k with hS
  set s := Nat.sqrt (2 * n) with hs
  have hrestrict : ∑ k ∈ Finset.Ioc n m with ¬ k.Prime, vonMangoldt k =
      ∑ k ∈ S, Real.log (k.minFac) := by
    rw [hS]
    simp only [Finset.sum_filter, ArithmeticFunction.vonMangoldt_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp_all
  -- structure of the elements of `S`
  have hstruct : ∀ k ∈ S, ∃ p j, p.Prime ∧ 2 ≤ j ∧ p ^ j = k := by
    intro k hk
    rw [hS, Finset.mem_filter] at hk
    obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff k).mp hk.2.2
    refine ⟨p, j, hp, ?_, rfl⟩
    by_contra hj2
    have : j = 1 := by omega
    subst this
    exact hk.2.1 (by simpa using hp)
  have hwin : ∀ k ∈ S, n < k ∧ k ≤ 2 * n := by
    intro k hk
    rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hk
    exact ⟨hk.1.1, le_trans hk.1.2 hnm⟩
  have hinj : Set.InjOn Nat.minFac (S : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    obtain ⟨p₁, j₁, hp₁, hj₁, rfl⟩ := hstruct k₁ hk₁
    obtain ⟨p₂, j₂, hp₂, hj₂, rfl⟩ := hstruct k₂ hk₂
    rw [Nat.Prime.pow_minFac hp₁ (by omega), Nat.Prime.pow_minFac hp₂ (by omega)] at heq
    subst heq
    have w₁ := hwin _ hk₁
    have w₂ := hwin _ hk₂
    have hp2 : 2 ≤ p₁ := hp₁.two_le
    rcases lt_trichotomy j₁ j₂ with h | h | h
    · exfalso
      have : p₁ ^ (j₁ + 1) ≤ p₁ ^ j₂ := Nat.pow_le_pow_right hp₁.pos h
      rw [pow_succ] at this
      nlinarith [w₁.1, w₂.2]
    · rw [h]
    · exfalso
      have : p₁ ^ (j₂ + 1) ≤ p₁ ^ j₁ := Nat.pow_le_pow_right hp₁.pos h
      rw [pow_succ] at this
      nlinarith [w₂.1, w₁.2]
  have himage : S.image Nat.minFac ⊆ (Finset.Icc 1 s).filter Nat.Prime := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q, j, hq, hj, rfl⟩ := hstruct k hk
    rw [Nat.Prime.pow_minFac hq (by omega)]
    have hw := hwin _ hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq.one_lt.le, ?_⟩, hq⟩
    rw [hs, Nat.le_sqrt]
    have : q ^ 2 ≤ q ^ j := Nat.pow_le_pow_right hq.pos hj
    nlinarith [hw.2]
  rw [hrestrict, ← Finset.sum_image (f := fun p : ℕ => Real.log (p : ℝ)) hinj]
  calc ∑ p ∈ S.image Nat.minFac, Real.log p
      ≤ ∑ p ∈ (Finset.Icc 1 s).filter Nat.Prime, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg himage fun p hp _ =>
          Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
    _ ≤ ∑ d ∈ Finset.Icc 1 s, vonMangoldt d := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun d _ => ?_
        split_ifs with hd
        · rw [ArithmeticFunction.vonMangoldt_apply_prime hd]
        · exact ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ (Real.log 4 + 4) * s := Mertens.sum_vonMangoldt_Icc_le s
    _ ≤ 6 * Real.sqrt (2 * n) := by
        have h1 : (s : ℝ) ≤ Real.sqrt (2 * n) := by
          rw [hs]
          have := Real.nat_sqrt_le_real_sqrt (a := 2 * n)
          simpa using this
        exact mul_le_mul log_four_add_four_le_six h1 (Nat.cast_nonneg _) (by norm_num)

/-- **Brun–Titchmarsh on a window of length at least `√n`.** -/
theorem sum_vonMangoldt_window_prime_le {n H : ℕ} (hn : 2 ≤ n) (hH : H ≤ n) :
    ∑ k ∈ Finset.Ioc n (n + H) with k.Prime, vonMangoldt k ≤ 1168 * (H + Real.sqrt n) := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set H' : ℝ := max (H : ℝ) (Real.sqrt n) with hH'
  have hsqrt1 : 1 < Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hH'1 : 1 < H' := lt_of_lt_of_le hsqrt1 (le_max_right _ _)
  have hH'0 : 0 < H' := by linarith
  have hlogH' : Real.log n / 2 ≤ Real.log H' := by
    have h1 : Real.log (Real.sqrt n) = Real.log n / 2 := by
      rw [Real.log_sqrt hn0.le]
    rw [← h1]
    exact Real.log_le_log (Real.sqrt_pos.mpr hn0) (le_max_right _ _)
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hlog2n : Real.log (2 * n) ≤ 4 * Real.log H' := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
    linarith
  -- each prime term is at most `log 2n`
  have hterm : ∀ k ∈ (Finset.Ioc n (n + H)).filter Nat.Prime, vonMangoldt k ≤ Real.log (2 * n) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ioc] at hk
    rw [ArithmeticFunction.vonMangoldt_apply_prime hk.2]
    exact Real.log_le_log (by exact_mod_cast hk.2.pos) (by exact_mod_cast (by omega : k ≤ 2 * n))
  -- the count of primes
  have hcount : (((Finset.Ioc n (n + H)).filter Nat.Prime).card : ℝ) ≤ 292 * H' / Real.log H' := by
    have hbt := Sieve.primesBetween_le_div_log (a := (n : ℝ) + 1) (H := H') (by positivity) hH'1
    refine le_trans ?_ hbt
    unfold BrunTitchmarsh.primesBetween
    have hsub : (Finset.Ioc n (n + H)).filter Nat.Prime ⊆
        (Finset.Icc ⌈(n : ℝ) + 1⌉₊ ⌊(n : ℝ) + 1 + H'⌋₊).filter Nat.Prime := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Ioc] at hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hk.2⟩
      · rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
        omega
      · apply Nat.le_floor
        have : (H : ℝ) ≤ H' := le_max_left _ _
        have hk2 : (k : ℝ) ≤ n + H := by exact_mod_cast hk.1.2
        linarith
    exact_mod_cast Finset.card_le_card hsub
  rw [Finset.sum_filter, ← Finset.sum_filter]
  calc ∑ k ∈ (Finset.Ioc n (n + H)).filter Nat.Prime, vonMangoldt k
      ≤ ∑ _k ∈ (Finset.Ioc n (n + H)).filter Nat.Prime, Real.log (2 * n) :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Ioc n (n + H)).filter Nat.Prime).card : ℝ) * Real.log (2 * n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (292 * H' / Real.log H') * (4 * Real.log H') := by
        have hlp := Real.log_pos hH'1
        refine mul_le_mul hcount hlog2n (Real.log_nonneg (by linarith)) (by positivity)
    _ = 1168 * H' := by
        have : Real.log H' ≠ 0 := (Real.log_pos hH'1).ne'
        field_simp
        ring
    _ ≤ 1168 * (H + Real.sqrt n) := by
        have : H' ≤ H + Real.sqrt n := max_le (by linarith [Real.sqrt_nonneg (n : ℝ)])
          (by linarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)])
        linarith

/-- **Chebyshev's function on a window:** `ψ(n + H) − ψ(n) ≤ 1168(H + √n) + 6√(2n)` for `H ≤ n`. -/
theorem psi_window_le_sqrt {n H : ℕ} (hn : 2 ≤ n) (hH : H ≤ n) :
    Chebyshev.psi ((n + H : ℕ) : ℝ) - Chebyshev.psi n ≤
      1168 * (H + Real.sqrt n) + 6 * Real.sqrt (2 * n) := by
  rw [psi_sub_psi_eq (by omega : n ≤ n + H),
    ← Finset.sum_filter_add_sum_filter_not _ (fun k => k.Prime)]
  exact add_le_add (sum_vonMangoldt_window_prime_le hn hH)
    (sum_vonMangoldt_window_not_prime_le (by omega))

/-! ## The square-root Lipschitz law -/

theorem mertensSum_sub_le_psi_div {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    mertensSum m - mertensSum n ≤ (Chebyshev.psi m - Chebyshev.psi n) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mertensSum_sub_eq hnm, psi_sub_psi_eq hnm, Finset.sum_div]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_Ioc.mp hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hn0
    (by exact_mod_cast hk'.1.le)

/-- The bracket moves by `O(g + √n)` over a gap `g = m − n`. -/
theorem abs_lagBracket_sub_le_sqrt {n m : ℕ} (hn2 : 2 ≤ n) (hnm : n ≤ m) (hm2n : m ≤ 2 * n) :
    |lagBracket m - lagBracket n| ≤ 3600 * (((m - n : ℕ) : ℝ) + Real.sqrt n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hm2n' : (m : ℝ) ≤ 2 * n := by exact_mod_cast hm2n
  have hm0 : (0 : ℝ) < m := by linarith
  set g : ℝ := ((m - n : ℕ) : ℝ) with hg
  have hg_eq : g = (m : ℝ) - n := by rw [hg]; push_cast [Nat.cast_sub hnm]; ring
  have hg0 : 0 ≤ g := by rw [hg_eq]; linarith
  have hsn1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn1
  have hs2 : Real.sqrt (2 * n) ≤ 2 * Real.sqrt n := by
    rw [Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  -- the window bound
  have hW : Chebyshev.psi m - Chebyshev.psi n ≤ 1168 * g + 1180 * Real.sqrt n := by
    have h := psi_window_le_sqrt (n := n) (H := m - n) hn2 (by omega)
    rw [show n + (m - n) = m by omega] at h
    rw [hg]
    nlinarith
  have hψ0 := psi_sub_psi_nonneg hnm
  have hM0 := mertensSum_sub_nonneg hnm
  have hMψ := mertensSum_sub_le_psi_div (by omega) hnm
  have hdevn : |mertensSum n - Real.log n + eulerMascheroniConstant| ≤ 7 := by
    have hM := abs_mertensSum_sub_log_le (by omega : 1 ≤ n)
    have hγ : eulerMascheroniConstant ≤ 1 := by
      have := Real.eulerMascheroniConstant_lt_two_thirds; linarith
    have hγ0 : 0 ≤ eulerMascheroniConstant := by have := eulerMascheroniConstant_gt; linarith
    rw [abs_le] at hM ⊢; constructor <;> linarith [hM.1, hM.2]
  have hlogdiff : Real.log m - Real.log n ≤ g / n := by
    rw [← Real.log_div hm0.ne' hn0.ne', hg_eq]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m / n by positivity)
    have e : (m : ℝ) / n - 1 = ((m : ℝ) - n) / n := by field_simp
    linarith
  have hlogdiff0 : 0 ≤ Real.log m - Real.log n := by
    have := Real.log_le_log hn0 hnm'; linarith
  have hSm0 : 0 ≤ trivialZeroSeriesReal m := trivialZeroSeriesReal_nonneg (by linarith)
  have hSn1 : trivialZeroSeriesReal n ≤ 1 := trivialZeroSeriesReal_le_one hn1
  have hSanti : trivialZeroSeriesReal m ≤ trivialZeroSeriesReal n :=
    trivialZeroSeriesReal_anti hn1 hnm'
  have hdecomp : lagBracket m - lagBracket n
      = ((m : ℝ) - n) - (Chebyshev.psi m - Chebyshev.psi n)
        + m * (mertensSum m - mertensSum n)
        + ((m : ℝ) - n) * (mertensSum n - Real.log n + eulerMascheroniConstant)
        - m * (Real.log m - Real.log n)
        + (trivialZeroSeriesReal m - trivialZeroSeriesReal n) := by
    unfold lagBracket; ring
  rw [hdecomp, ← hg_eq]
  have hB : (m : ℝ) * (mertensSum m - mertensSum n) ≤ 2 * (Chebyshev.psi m - Chebyshev.psi n) := by
    calc (m : ℝ) * (mertensSum m - mertensSum n)
        ≤ m * ((Chebyshev.psi m - Chebyshev.psi n) / n) := mul_le_mul_of_nonneg_left hMψ hm0.le
      _ = (m / n) * (Chebyshev.psi m - Chebyshev.psi n) := by field_simp
      _ ≤ 2 * (Chebyshev.psi m - Chebyshev.psi n) := by
          apply mul_le_mul_of_nonneg_right _ hψ0
          rw [div_le_iff₀ hn0]; linarith
  have hB0 : 0 ≤ (m : ℝ) * (mertensSum m - mertensSum n) := mul_nonneg hm0.le hM0
  have hC : |g * (mertensSum n - Real.log n + eulerMascheroniConstant)| ≤ 7 * g := by
    rw [abs_mul, abs_of_nonneg hg0]; nlinarith
  have hD : (m : ℝ) * (Real.log m - Real.log n) ≤ 2 * g := by
    calc (m : ℝ) * (Real.log m - Real.log n) ≤ m * (g / n) :=
          mul_le_mul_of_nonneg_left hlogdiff hm0.le
      _ = (m / n) * g := by field_simp
      _ ≤ 2 * g := by
          apply mul_le_mul_of_nonneg_right _ hg0
          rw [div_le_iff₀ hn0]; linarith
  have hD0 : 0 ≤ (m : ℝ) * (Real.log m - Real.log n) := mul_nonneg hm0.le hlogdiff0
  rw [abs_le]
  have hC1 := (abs_le.mp hC).1
  have hC2 := (abs_le.mp hC).2
  constructor <;> nlinarith

/-- **Square-root Lipschitz law for the integer lags.** For `2 ≤ n ≤ m ≤ 2n`,
`|a_m − a_n| ≤ 3620 (1 + (m − n)/√n)`. -/
theorem abs_integerLag_sub_le_sqrt {n m : ℕ} (hn2 : 2 ≤ n) (hnm : n ≤ m) (hm2n : m ≤ 2 * n) :
    |integerLag m - integerLag n| ≤ 3620 * (1 + ((m - n : ℕ) : ℝ) / Real.sqrt n) := by
  have hm2 : 2 ≤ m := le_trans hn2 hnm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hm2n' : (m : ℝ) ≤ 2 * n := by exact_mod_cast hm2n
  have hm0 : (0 : ℝ) < m := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsnm : Real.sqrt n ≤ Real.sqrt m := Real.sqrt_le_sqrt hnm'
  set g : ℝ := ((m - n : ℕ) : ℝ) with hg
  have hg_eq : g = (m : ℝ) - n := by rw [hg]; push_cast [Nat.cast_sub hnm]; ring
  have hg0 : 0 ≤ g := by rw [hg_eq]; linarith
  have hEm := abs_lagBracket_le_linear hm2
  have hEd := abs_lagBracket_sub_le_sqrt hn2 hnm hm2n
  rw [← hg] at hEd
  have hinv := inv_sqrt_sub_inv_sqrt_le hn1 hnm'
  have hinv0 : 0 ≤ 1 / Real.sqrt n - 1 / Real.sqrt m := by
    have := one_div_le_one_div_of_le hsn hsnm; linarith
  rw [integerLag_eq_lagBracket hm2, integerLag_eq_lagBracket hn2]
  have hdecomp : lagBracket m / Real.sqrt m - lagBracket n / Real.sqrt n
      = -(lagBracket m * (1 / Real.sqrt n - 1 / Real.sqrt m))
        + (lagBracket m - lagBracket n) / Real.sqrt n := by
    field_simp
    ring
  rw [hdecomp]
  have ht1 : |lagBracket m * (1 / Real.sqrt n - 1 / Real.sqrt m)| ≤ 20 * (g / Real.sqrt n) := by
    rw [abs_mul, abs_of_nonneg hinv0]
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    calc |lagBracket m| * (1 / Real.sqrt n - 1 / Real.sqrt m)
        ≤ (20 * m) * ((m - n) / (2 * (n * Real.sqrt n))) := mul_le_mul hEm hinv hinv0 (by positivity)
      _ = 10 * (m / n) * (g / Real.sqrt n) := by rw [hg_eq]; field_simp; ring
      _ ≤ 10 * 2 * (g / Real.sqrt n) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [div_le_iff₀ hn0]; linarith
      _ = 20 * (g / Real.sqrt n) := by ring
  have ht2 : |(lagBracket m - lagBracket n) / Real.sqrt n| ≤ 3600 * (g / Real.sqrt n) + 3600 := by
    rw [abs_div, abs_of_pos hsn, div_le_iff₀ hsn]
    have : (3600 * (g / Real.sqrt n) + 3600) * Real.sqrt n = 3600 * (g + Real.sqrt n) := by
      field_simp
    rw [this]
    exact hEd
  have hgs : 0 ≤ g / Real.sqrt n := by positivity
  calc |-(lagBracket m * (1 / Real.sqrt n - 1 / Real.sqrt m))
        + (lagBracket m - lagBracket n) / Real.sqrt n|
      ≤ |lagBracket m * (1 / Real.sqrt n - 1 / Real.sqrt m)|
        + |(lagBracket m - lagBracket n) / Real.sqrt n| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ 20 * (g / Real.sqrt n) + (3600 * (g / Real.sqrt n) + 3600) := add_le_add ht1 ht2
    _ ≤ 3620 * (1 + g / Real.sqrt n) := by nlinarith

/-! ## Sampling at the square-root scale -/

/-- A set meeting every window `[n − K√n, n]` for large `n` gives samples `k` with `2 ≤ k ≤ n ≤ 2k`
and `(n − k)/√k ≤ 2K`. -/
theorem sqrt_samples_of_gaps {A : Set ℕ} {K : ℝ} {N₀ : ℕ} (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ ((n : ℝ) - k) ≤ K * Real.sqrt n) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧ k ≤ n ∧ n ≤ 2 * k ∧
      ((n - k : ℕ) : ℝ) / Real.sqrt k ≤ 2 * K := by
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, (4 * K ^ 2 + 4 : ℝ) ≤ N₂ := exists_nat_ge _
  refine ⟨max N₀ N₂, fun n hn => ?_⟩
  obtain ⟨k, hkA, hkn, hgk⟩ := hgap n (le_trans (le_max_left _ _) hn)
  have hnN : (4 * K ^ 2 + 4 : ℝ) ≤ n :=
    hN₂.trans (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hn0 : (0 : ℝ) < n := by nlinarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  -- `K√n ≤ n/2`
  have hKs : K * Real.sqrt n ≤ n / 2 := by
    have h2 : 2 * K ≤ Real.sqrt n := by
      rw [show 2 * K = Real.sqrt ((2 * K) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    nlinarith
  have hk_ge : (n : ℝ) / 2 ≤ k := by linarith
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := by nlinarith
    exact_mod_cast this
  have hn2k : n ≤ 2 * k := by
    have : (n : ℝ) ≤ 2 * k := by linarith
    exact_mod_cast this
  refine ⟨k, hkA, hk2, hkn, hn2k, ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by push_cast [Nat.cast_sub hkn]; ring
  rw [hcast, div_le_iff₀ hsk]
  -- `√n ≤ 2√k` since `n ≤ 2k ≤ 4k`
  have hsn2 : Real.sqrt n ≤ 2 * Real.sqrt k := by
    have : Real.sqrt n ≤ Real.sqrt (4 * k) := Real.sqrt_le_sqrt (by
      have : (n : ℝ) ≤ 2 * k := by exact_mod_cast hn2k
      linarith)
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    exact this
  nlinarith

/-- **Upper bounds transfer from square-root-dense samples.** -/
theorem integerLag_le_of_sqrt_samples {A : Set ℕ} {M K : ℝ} {N₁ : ℕ}
    (hA : ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M)
    (hdense : ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧ k ≤ n ∧ n ≤ 2 * k ∧
      ((n - k : ℕ) : ℝ) / Real.sqrt k ≤ K) :
    ∃ M' : ℝ, ∀ n : ℕ, 2 ≤ n → integerLag n ≤ M' := by
  classical
  set B : ℝ := (Finset.range (N₁ + 2)).sup' ⟨0, by simp⟩ fun n => integerLag n with hB
  refine ⟨max B (M + 3620 * (1 + K)), fun n hn => ?_⟩
  rcases lt_or_ge n N₁ with hlt | hge
  · exact le_max_of_le_left (Finset.le_sup' (fun n => integerLag n)
      (Finset.mem_range.mpr (by omega)))
  · refine le_max_of_le_right ?_
    obtain ⟨k, hkA, hk2, hkn, hn2k, hgap⟩ := hdense n hge
    have hd := abs_integerLag_sub_le_sqrt hk2 hkn hn2k
    have := (abs_le.mp hd).2
    have h3 : 3620 * (1 + ((n - k : ℕ) : ℝ) / Real.sqrt k) ≤ 3620 * (1 + K) := by linarith
    linarith [hA k hkA hk2]

/-- **Lower bounds transfer from square-root-dense samples.** -/
theorem le_integerLag_of_sqrt_samples {A : Set ℕ} {M K : ℝ} {N₁ : ℕ}
    (hA : ∀ k ∈ A, 2 ≤ k → M ≤ integerLag k)
    (hdense : ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧ k ≤ n ∧ n ≤ 2 * k ∧
      ((n - k : ℕ) : ℝ) / Real.sqrt k ≤ K) :
    ∃ M' : ℝ, ∀ n : ℕ, 2 ≤ n → M' ≤ integerLag n := by
  classical
  set B : ℝ := (Finset.range (N₁ + 2)).inf' ⟨0, by simp⟩ fun n => integerLag n with hB
  refine ⟨min B (M - 3620 * (1 + K)), fun n hn => ?_⟩
  rcases lt_or_ge n N₁ with hlt | hge
  · exact min_le_of_left_le (Finset.inf'_le (fun n => integerLag n)
      (Finset.mem_range.mpr (by omega)))
  · refine min_le_of_right_le ?_
    obtain ⟨k, hkA, hk2, hkn, hn2k, hgap⟩ := hdense n hge
    have hd := abs_integerLag_sub_le_sqrt hk2 hkn hn2k
    have := (abs_le.mp hd).1
    have h3 : 3620 * (1 + ((n - k : ℕ) : ℝ) / Real.sqrt k) ≤ 3620 * (1 + K) := by linarith
    linarith [hA k hkA hk2]

/-- **Lag criterion at the square-root scale.** If `A` meets every window `[n − K√n, n]` for large
`n`, the Riemann hypothesis holds iff the lags along `A` are bounded above. -/
theorem riemannHypothesis_iff_integerLag_bddAbove_of_sqrt_gaps {A : Set ℕ} {K : ℝ} {N₀ : ℕ}
    (hK : 0 ≤ K) (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ ((n : ℝ) - k) ≤ K * Real.sqrt n) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddAbove.mp h
    exact ⟨M, fun k _ hk => hM k hk⟩
  · rintro ⟨M, hM⟩
    obtain ⟨N₁, hdense⟩ := sqrt_samples_of_gaps hK hgap
    exact riemannHypothesis_iff_integerLag_bddAbove.mpr (integerLag_le_of_sqrt_samples hM hdense)

/-- **Lag criterion at the square-root scale, lower form.** -/
theorem riemannHypothesis_iff_integerLag_bddBelow_of_sqrt_gaps {A : Set ℕ} {K : ℝ} {N₀ : ℕ}
    (hK : 0 ≤ K) (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ ((n : ℝ) - k) ≤ K * Real.sqrt n) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ k ∈ A, 2 ≤ k → M ≤ integerLag k := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddBelow.mp h
    exact ⟨M, fun k _ hk => hM k hk⟩
  · rintro ⟨M, hM⟩
    obtain ⟨N₁, hdense⟩ := sqrt_samples_of_gaps hK hgap
    exact riemannHypothesis_iff_integerLag_bddBelow.mpr (le_integerLag_of_sqrt_samples hM hdense)

/-- The perfect squares meet every window `[n − 2√n, n]`. -/
theorem sq_gap (n : ℕ) : ∃ k ∈ {k : ℕ | ∃ j, k = j ^ 2}, k ≤ n ∧ ((n : ℝ) - k) ≤ 2 * Real.sqrt n := by
  refine ⟨Nat.sqrt n ^ 2, ⟨Nat.sqrt n, rfl⟩, Nat.sqrt_le' n, ?_⟩
  have hlt := Nat.lt_succ_sqrt' n
  have hle : n ≤ Nat.sqrt n ^ 2 + 2 * Nat.sqrt n := by
    rw [Nat.succ_eq_add_one] at hlt
    nlinarith
  have hs : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hle' : (n : ℝ) ≤ ((Nat.sqrt n ^ 2 : ℕ) : ℝ) + 2 * (Nat.sqrt n : ℕ) := by exact_mod_cast hle
  linarith

/-- **The squares decide the Riemann hypothesis:** RH holds iff the Weil lags `a_{j²}` are bounded
above. -/
theorem riemannHypothesis_iff_integerLag_sq_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ j : ℕ, 2 ≤ j → integerLag (j ^ 2) ≤ M := by
  rw [riemannHypothesis_iff_integerLag_bddAbove_of_sqrt_gaps (A := {k : ℕ | ∃ j, k = j ^ 2})
    (K := 2) (N₀ := 0) (by norm_num) fun n _ => sq_gap n]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun j hj => hM _ ⟨j, rfl⟩ (by nlinarith)⟩
  · rintro ⟨M, hM⟩
    refine ⟨M, fun k ⟨j, hj⟩ hk => ?_⟩
    subst hj
    have hj2 : 2 ≤ j := by
      by_contra h
      push Not at h
      interval_cases j <;> simp at hk
    exact hM j hj2

/-- **The squares decide the Riemann hypothesis, lower form.** -/
theorem riemannHypothesis_iff_integerLag_sq_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ j : ℕ, 2 ≤ j → M ≤ integerLag (j ^ 2) := by
  rw [riemannHypothesis_iff_integerLag_bddBelow_of_sqrt_gaps (A := {k : ℕ | ∃ j, k = j ^ 2})
    (K := 2) (N₀ := 0) (by norm_num) fun n _ => sq_gap n]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun j hj => hM _ ⟨j, rfl⟩ (by nlinarith)⟩
  · rintro ⟨M, hM⟩
    refine ⟨M, fun k ⟨j, hj⟩ hk => ?_⟩
    subst hj
    have hj2 : 2 ≤ j := by
      by_contra h
      push Not at h
      interval_cases j <;> simp at hk
    exact hM j hj2

/-! ## Lower interpolation on quadratic meshes -/

/-- Each prime atom strictly between `n` and `m` carries chord charge at most `(m − n)/n`, so the
total charge is at most `(ψ(m) − ψ(n))(m − n)/n`. -/
theorem lagPrimeChordCharge_le_psi {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {u v : ℝ}
    (hv : 0 ≤ v) (hu1 : u ≤ 1) :
    lagPrimeChordCharge m n m u v ≤
      (Chebyshev.psi m - Chebyshev.psi n) * (((m : ℝ) - n) / n) := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [psi_sub_psi_eq hnm, Finset.sum_mul]
  unfold lagPrimeChordCharge
  have hsplit : Finset.Icc 1 m = Finset.Icc 1 n ∪ Finset.Ioc n m := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Ioc n m) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hlow : ∑ j ∈ Finset.Icc 1 n, vonMangoldt j *
      min (u * max (1 - (n : ℝ) / j) 0) (v * max ((m : ℝ) / j - 1) 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := Finset.mem_Icc.mp hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj'.2
    have h1 : 1 - (n : ℝ) / j ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hj0]; linarith
    rw [max_eq_right h1, mul_zero, min_eq_left (by positivity), mul_zero]
  rw [hlow, zero_add]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_Ioc.mp hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hnj : (n : ℝ) ≤ j := by exact_mod_cast hj'.1.le
  have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj'.2
  refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
  have h1 : 0 ≤ 1 - (n : ℝ) / j := by
    rw [sub_nonneg, div_le_one hj0]; exact hnj
  calc min (u * max (1 - (n : ℝ) / j) 0) (v * max ((m : ℝ) / j - 1) 0)
      ≤ u * max (1 - (n : ℝ) / j) 0 := min_le_left _ _
    _ ≤ 1 - (n : ℝ) / j := by
        rw [max_eq_left h1]
        nlinarith
    _ = ((j : ℝ) - n) / j := by field_simp
    _ ≤ ((j : ℝ) - n) / n := div_le_div_of_nonneg_left (by linarith) hn0 hnj
    _ ≤ ((m : ℝ) - n) / n := div_le_div_of_nonneg_right (by linarith) hn0.le

/-- **Lower chord interpolation.** For `k = un + vm`, the lag at `k` is at least the endpoint floor
`min(0, a_n, a_m)` minus the prime charge and the trivial-zero deficit, divided by `√k`. -/
theorem integerLag_ge_endpoint_floor {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) (hmean : (k : ℝ) = u * n + v * m) :
    min 0 (min (integerLag n) (integerLag m)) -
        ((Chebyshev.psi m - Chebyshev.psi n) * (((m : ℝ) - n) / n) + 1) / Real.sqrt k ≤
      integerLag k := by
  have hk : 2 ≤ k := hn.trans hnk
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hexact := sqrt_integerLag_chord_exact hn hnk hkm hu hv huv hmean
  have hLD : 0 ≤ u * n * Real.log n + v * m * Real.log m - k * Real.log k := by
    have h := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr (Nat.cast_nonneg n))
      (Set.mem_Ici.mpr (Nat.cast_nonneg m)) hu hv huv
    simp only [smul_eq_mul] at h
    rw [hmean]
    linarith
  have hSD : u * trivialZeroSeriesReal n + v * trivialZeroSeriesReal m - trivialZeroSeriesReal k
      ≤ 1 := by
    have h1 := trivialZeroSeriesReal_le_one hn1
    have h2 := trivialZeroSeriesReal_le_one hm1
    have h3 := trivialZeroSeriesReal_nonneg hk1
    nlinarith
  have hPC := lagPrimeChordCharge_le_psi (u := u) (by omega) (hnk.trans hkm) hv (by linarith)
  set μ := min 0 (min (integerLag n) (integerLag m)) with hμ
  have hμ0 : μ ≤ 0 := min_le_left _ _
  have hμn : μ ≤ integerLag n := (min_le_right _ _).trans (min_le_left _ _)
  have hμm : μ ≤ integerLag m := (min_le_right _ _).trans (min_le_right _ _)
  have hsn := Real.sqrt_nonneg (n : ℝ)
  have hsm := Real.sqrt_nonneg (m : ℝ)
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by linarith)
  have hconc : u * Real.sqrt n + v * Real.sqrt m ≤ Real.sqrt k := by
    apply Real.le_sqrt_of_sq_le
    have hnn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
    have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (by linarith)
    have hamgm : 2 * (Real.sqrt n * Real.sqrt m) ≤ n + m := by
      nlinarith [sq_nonneg (Real.sqrt n - Real.sqrt m)]
    rw [hmean]
    have hv' : v = 1 - u := by linarith
    subst hv'
    nlinarith [mul_nonneg hu hv]
  have hend : μ * Real.sqrt k ≤
      u * (Real.sqrt n * integerLag n) + v * (Real.sqrt m * integerLag m) := by
    calc μ * Real.sqrt k ≤ μ * (u * Real.sqrt n + v * Real.sqrt m) :=
          mul_le_mul_of_nonpos_left hconc hμ0
      _ = u * (Real.sqrt n * μ) + v * (Real.sqrt m * μ) := by ring
      _ ≤ u * (Real.sqrt n * integerLag n) + v * (Real.sqrt m * integerLag m) :=
          add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμn hsn) hu)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμm hsm) hv)
  have hmain : μ * Real.sqrt k -
      ((Chebyshev.psi m - Chebyshev.psi n) * (((m : ℝ) - n) / n) + 1) ≤
        Real.sqrt k * integerLag k := by
    linarith
  have hdiv : μ - ((Chebyshev.psi m - Chebyshev.psi n) * (((m : ℝ) - n) / n) + 1) / Real.sqrt k =
      (μ * Real.sqrt k -
        ((Chebyshev.psi m - Chebyshev.psi n) * (((m : ℝ) - n) / n) + 1)) / Real.sqrt k := by
    field_simp
  rw [hdiv, div_le_iff₀ hsk]
  linarith

/-- The prime charge on a mesh step with `(m − n)² ≤ C n√n`, `m ≤ 2n`, is `O(√n)`. -/
theorem psi_window_mul_gap_le {n m : ℕ} {C : ℝ} (hn : 2 ≤ n) (hnm : n ≤ m) (hm2n : m ≤ 2 * n)
    (hgap : ((m : ℝ) - n) ^ 2 ≤ C * ((n : ℝ) * Real.sqrt n)) :
    (Chebyshev.psi m - Chebyshev.psi n) * (((m : ℝ) - n) / n) ≤
      (1168 * (C + 1) + 12) * Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hm2n' : (m : ℝ) ≤ 2 * n := by exact_mod_cast hm2n
  have hgnat : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := by push_cast [Nat.cast_sub hnm]; ring
  have hW : Chebyshev.psi m - Chebyshev.psi n ≤
      1168 * (((m : ℝ) - n) + Real.sqrt n) + 12 * Real.sqrt n := by
    have h := psi_window_le_sqrt (n := n) (H := m - n) hn (by omega)
    rw [show n + (m - n) = m by omega, hgnat] at h
    have hs2 : Real.sqrt (2 * n) ≤ 2 * Real.sqrt n := by
      rw [Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      nlinarith
    linarith
  have hgdiv : ((m : ℝ) - n) / n ≤ 1 := by rw [div_le_one hn0]; linarith
  have hgdiv0 : 0 ≤ ((m : ℝ) - n) / n := div_nonneg (by linarith) hn0.le
  have hgsq : ((m : ℝ) - n) * (((m : ℝ) - n) / n) ≤ C * Real.sqrt n := by
    rw [mul_div_assoc', div_le_iff₀ hn0]
    nlinarith
  calc (Chebyshev.psi m - Chebyshev.psi n) * (((m : ℝ) - n) / n)
      ≤ (1168 * (((m : ℝ) - n) + Real.sqrt n) + 12 * Real.sqrt n) * (((m : ℝ) - n) / n) :=
        mul_le_mul_of_nonneg_right hW hgdiv0
    _ = 1168 * (((m : ℝ) - n) * (((m : ℝ) - n) / n) + Real.sqrt n * (((m : ℝ) - n) / n)) +
        12 * (Real.sqrt n * (((m : ℝ) - n) / n)) := by ring
    _ ≤ 1168 * (C * Real.sqrt n + Real.sqrt n * 1) + 12 * (Real.sqrt n * 1) := by
        gcongr
    _ = (1168 * (C + 1) + 12) * Real.sqrt n := by ring

/-- **Lower bounds transfer along every quadratic lag mesh.** -/
theorem integerLag_bddBelow_of_quadraticMesh {S : Set ℕ} (hS : QuadraticLagMesh S) {M : ℝ}
    (hM : ∀ n ∈ S, M ≤ integerLag n) : ∃ B : ℝ, ∀ k : ℕ, 2 ≤ k → B ≤ integerLag k := by
  classical
  obtain ⟨C, hC, hmesh⟩ := hS
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, C ^ 2 + 2 ≤ (N₂ : ℝ) := exists_nat_ge _
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, (C + 2) * N₂ < (K₀ : ℝ) := exists_nat_gt _
  set B₀ : ℝ := 1168 * (C + 1) + 12 + 1 with hB₀
  set L : ℝ := (Finset.range (K₀ + 2)).inf' ⟨0, by simp⟩ fun n => integerLag n with hL
  refine ⟨min L (min 0 M - B₀), fun k hk => ?_⟩
  rcases lt_or_ge k K₀ with hlt | hge
  · exact min_le_of_left_le (Finset.inf'_le (fun n => integerLag n)
      (Finset.mem_range.mpr (by omega)))
  refine min_le_of_right_le ?_
  obtain ⟨n, hnS, m, hmS, hn2, hnk, hkm, hgap⟩ := hmesh k hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hsn1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ n))
  have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
  -- the bracketing point is large
  have hnN : (N₂ : ℝ) ≤ n := by
    by_contra hcon
    push Not at hcon
    have hsn_le : Real.sqrt n ≤ n := by nlinarith
    have h1 : ((k : ℝ) - n) ^ 2 ≤ C * ((N₂ : ℝ) * N₂) := by
      have : ((k : ℝ) - n) ^ 2 ≤ ((m : ℝ) - n) ^ 2 := by nlinarith
      have h2 : (n : ℝ) * Real.sqrt n ≤ (N₂ : ℝ) * N₂ := by nlinarith
      nlinarith
    have hK : (K₀ : ℝ) ≤ k := by exact_mod_cast hge
    have hN0 : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
    have hkn : (C + 1) * N₂ < (k : ℝ) - n := by linarith
    have h0 : 0 ≤ (C + 1) * N₂ := by positivity
    have hsq1 : ((C + 1) * N₂) ^ 2 < ((k : ℝ) - n) ^ 2 := by nlinarith
    have hsq2 : C * ((N₂ : ℝ) * N₂) ≤ ((C + 1) * N₂) ^ 2 := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ C ^ 2 + C + 1) (sq_nonneg (N₂ : ℝ))]
    linarith
  -- so the step is at most `n`
  have hm2n : m ≤ 2 * n := by
    have hCs : C ≤ Real.sqrt n := by
      rw [show C = Real.sqrt (C ^ 2) by rw [Real.sqrt_sq hC]]
      exact Real.sqrt_le_sqrt (by linarith)
    have h1 : ((m : ℝ) - n) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have : C * ((n : ℝ) * Real.sqrt n) ≤ (n : ℝ) ^ 2 := by
        calc C * ((n : ℝ) * Real.sqrt n) ≤ Real.sqrt n * ((n : ℝ) * Real.sqrt n) :=
              mul_le_mul_of_nonneg_right hCs (by positivity)
          _ = (n : ℝ) * (Real.sqrt n * Real.sqrt n) := by ring
          _ = (n : ℝ) ^ 2 := by rw [hsq]; ring
      linarith
    have : (m : ℝ) - n ≤ n := by nlinarith
    have : (m : ℝ) ≤ 2 * n := by linarith
    exact_mod_cast this
  have hpc := psi_window_mul_gap_le hn2 (hnk.trans hkm) hm2n hgap
  have hsk : Real.sqrt n ≤ Real.sqrt k := Real.sqrt_le_sqrt hnk'
  have hsk0 : 0 < Real.sqrt k := by linarith
  -- the interpolation weights
  rcases eq_or_lt_of_le (hnk.trans hkm) with hnm | hnm
  · have hkn : k = n := le_antisymm (hnm ▸ hkm) hnk
    subst hkn
    have := hM k hnS
    have : 0 ≤ B₀ := by positivity
    have : min 0 M ≤ M := min_le_right _ _
    linarith
  have hmn : (0 : ℝ) < (m : ℝ) - n := by
    have : (n : ℝ) < m := by exact_mod_cast hnm
    linarith
  set u : ℝ := ((m : ℝ) - k) / ((m : ℝ) - n) with hu
  set v : ℝ := ((k : ℝ) - n) / ((m : ℝ) - n) with hv
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hmn.le
  have hv0 : 0 ≤ v := div_nonneg (by linarith) hmn.le
  have huv : u + v = 1 := by rw [hu, hv, ← add_div]; field_simp; ring
  have hmean : (k : ℝ) = u * n + v * m := by rw [hu, hv]; field_simp; ring
  have hfloor := integerLag_ge_endpoint_floor hn2 hnk hkm hu0 hv0 huv hmean
  have hμ : min 0 M ≤ min 0 (min (integerLag n) (integerLag m)) :=
    min_le_min le_rfl (le_min (hM n hnS) (hM m hmS))
  have hratio : ((Chebyshev.psi m - Chebyshev.psi n) * (((m : ℝ) - n) / n) + 1) / Real.sqrt k
      ≤ B₀ := by
    rw [div_le_iff₀ hsk0]
    have : (1168 * (C + 1) + 12) * Real.sqrt n ≤
        (1168 * (C + 1) + 12) * Real.sqrt k :=
      mul_le_mul_of_nonneg_left hsk (by positivity)
    nlinarith
  linarith

/-- **Lag criterion along a quadratic mesh, lower form.** For every quadratic lag mesh `S` (gaps
`O(n^{3/4})`), the Riemann hypothesis holds iff the lags along `S` are bounded below. -/
theorem riemannHypothesis_iff_integerLag_bddBelow_of_quadraticMesh {S : Set ℕ}
    (hS : QuadraticLagMesh S) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ n ∈ S, 2 ≤ n → M ≤ integerLag n := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddBelow.mp h
    exact ⟨M, fun n _ hn => hM n hn⟩
  · rintro ⟨M, hM⟩
    -- the mesh only uses points `≥ 2`
    have hS2 : QuadraticLagMesh {n ∈ S | 2 ≤ n} := by
      obtain ⟨C, hC, hmesh⟩ := hS
      refine ⟨C, hC, fun k hk => ?_⟩
      obtain ⟨n, hnS, m, hmS, hn2, hnk, hkm, hgap⟩ := hmesh k hk
      exact ⟨n, ⟨hnS, hn2⟩, m, ⟨hmS, hn2.trans (hnk.trans hkm)⟩, hn2, hnk, hkm, hgap⟩
    obtain ⟨B, hB⟩ := integerLag_bddBelow_of_quadraticMesh hS2 (M := M)
      fun n hn => hM n hn.1 hn.2
    exact riemannHypothesis_iff_integerLag_bddBelow.mpr ⟨B, hB⟩

/-- **Lag criterion along a quadratic mesh, upper form.** -/
theorem riemannHypothesis_iff_integerLag_bddAbove_of_quadraticMesh {S : Set ℕ}
    (hS : QuadraticLagMesh S) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ n ∈ S, 2 ≤ n → integerLag n ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddAbove.mp h
    exact ⟨M, fun n _ hn => hM n hn⟩
  · rintro ⟨M, hM⟩
    have hS2 : QuadraticLagMesh {n ∈ S | 2 ≤ n} := by
      obtain ⟨C, hC, hmesh⟩ := hS
      refine ⟨C, hC, fun k hk => ?_⟩
      obtain ⟨n, hnS, m, hmS, hn2, hnk, hkm, hgap⟩ := hmesh k hk
      exact ⟨n, ⟨hnS, hn2⟩, m, ⟨hmS, hn2.trans (hnk.trans hkm)⟩, hn2, hnk, hkm, hgap⟩
    obtain ⟨B, hB⟩ := integerLag_bddAbove_of_quadraticMesh hS2 (M := M)
      fun n hn => hM n hn.1 hn.2
    exact riemannHypothesis_iff_integerLag_bddAbove.mpr ⟨B, hB⟩

end

end RHTower
