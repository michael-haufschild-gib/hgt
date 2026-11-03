import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateFamilyIsAnExponentialOfPointCounts
import GaloisForLFunctions.WindowTowerOfSpecZ.TheSymmetriesOfTheTower

/-!
# The window zeta operator is a plethystic exponential

The Adams operations of the Dirichlet ring are the power dilations `ψ^a = mPart a`
(`ψ^a f(m^a) = f(m)`, zero off `a`-th powers); they are ring endomorphisms. With the prime indicator
`P` and the prime part `P_log = Λ·1_{primes}` of the von Mangoldt function:

* **The logarithm of `ζ` is a plethystic sum** (`primePowerLog_sub_plethLog_mem`):
  `ℓ ≡ Σ_{a≤L} ψ^a(P)/a` on every window with `e^A < 2^{L+1}`, hence `ζ ≡ exp Σ_a ψ^a(P)/a`
  (`expTrunc_plethLog_sub_zeta_mem`): the window zeta operator is the plethystic exponential of the
  prime folds — Euler's product in the language of λ-rings.
* **The von Mangoldt function is a sum of Adams operations** (`vonMangoldt_sub_sum_mPart_mem`):
  `Λ ≡ Σ_{a≤L} ψ^a(P_log)`.
* **The tower recursion of the arithmetic operator** (`windowRepFun_vonMangoldt_eq_sum_dilate`): the
  Adams operations intertwine the window of length `A/a` with the window of length `A` through the
  dilation `D_a` and the Tate twist `(a − 1)/2`, so
  `ρ_A(Λ) = Σ_{a≤L} D_a ρ_{A/a}(P_log·n^{−(a−1)/2}) D_a^{−1}`:
  Weil's arithmetic operator on a window is the prime operator of the window plus the dilated,
  Tate-twisted prime operators of the windows `A/2, A/3, …` — the prime powers of the window are the
  primes of the shorter windows of the tower.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ

/-- The prime indicator `P`. -/
def primeIndicator : ArithmeticFunction ℝ := ⟨fun n => if n.Prime then 1 else 0, by simp [Nat.not_prime_zero]⟩

/-- The prime part of the von Mangoldt function, `P_log(p) = log p`. -/
def primeLog : ArithmeticFunction ℝ := ⟨fun n => if n.Prime then Real.log n else 0, by simp⟩

/-- The plethystic logarithm `Σ_{a≤L} ψ^a(f)/a`. -/
def plethLog (L : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ∑ a ∈ Finset.Icc 1 L, single 1 ((a : ℝ)⁻¹) * RHTower.mPart a f

/-- Two primes with equal powers are equal, with equal exponents. -/
theorem prime_pow_eq_prime_pow {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (ha : 1 ≤ a)
    (h : q ^ a = p ^ b) : q = p ∧ a = b := by
  have hqp : q = p := by
    have : q ∣ p ^ b := ⟨q ^ (a - 1), by rw [← h, ← pow_succ']; congr 1; omega⟩
    exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow this)
  subst hqp
  exact ⟨rfl, Nat.pow_right_injective hq.two_le h⟩

/-- `ψ^a(f)` at a prime power `p^b`, for `f` supported on the primes. -/
theorem mPart_apply_prime_pow {f : ArithmeticFunction ℝ} (hf : ∀ n, ¬ n.Prime → f n = 0)
    {a b p : ℕ} (ha : 1 ≤ a) (hp : p.Prime) :
    RHTower.mPart a f (p ^ b) = if a = b then f p else 0 := by
  split_ifs with hab
  · subst hab; exact RHTower.mPart_apply_pow (by omega) f p
  · rw [RHTower.mPart_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with hk
    · by_cases hkp : k.Prime
      · exact absurd (prime_pow_eq_prime_pow hp hkp ha hk.1).2 hab
      · exact hf k hkp
    · rfl

/-- `ψ^a(f)` vanishes off prime powers, for `f` supported on the primes. -/
theorem mPart_apply_of_not_isPrimePow {f : ArithmeticFunction ℝ} (hf : ∀ n, ¬ n.Prime → f n = 0)
    {a n : ℕ} (ha : 1 ≤ a) (hn : ¬ IsPrimePow n) : RHTower.mPart a f n = 0 := by
  rw [RHTower.mPart_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs with hk
  · by_cases hkp : k.Prime
    · exact absurd ((isPrimePow_nat_iff n).mpr ⟨k, a, hkp, ha, hk.1⟩) hn
    · exact hf k hkp
  · rfl

/-- `Σ_{a≤L} c_a ψ^a(f)(n)` collapses onto the exponent of `n = p^b` when `b ≤ L`. -/
theorem sum_mPart_apply_prime_pow {f : ArithmeticFunction ℝ} (hf : ∀ n, ¬ n.Prime → f n = 0)
    (c : ℕ → ℝ) {L b p : ℕ} (hp : p.Prime) (hb : 1 ≤ b) (hbL : b ≤ L) :
    ∑ a ∈ Finset.Icc 1 L, c a * RHTower.mPart a f (p ^ b) = c b * f p := by
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_Icc.mpr ⟨hb, hbL⟩) fun a ha hab => by
    rw [mPart_apply_prime_pow hf (Finset.mem_Icc.mp ha).1 hp, if_neg hab, mul_zero]]
  rw [mPart_apply_prime_pow hf hb hp, if_pos rfl]

theorem primeIndicator_of_not_prime {n : ℕ} (hn : ¬ n.Prime) : primeIndicator n = 0 := by
  simp [primeIndicator, hn]

theorem primeLog_of_not_prime {n : ℕ} (hn : ¬ n.Prime) : primeLog n = 0 := by
  simp [primeLog, hn]

/-- Exponents of prime powers below `2^{L+1}` are at most `L`. -/
theorem exponent_le_of_lt_two_pow {p b N L : ℕ} (hp : p.Prime) (hn : p ^ b ≤ N)
    (hNL : N < 2 ^ (L + 1)) : b ≤ L := by
  have h2 : 2 ^ b ≤ p ^ b := Nat.pow_le_pow_left hp.two_le b
  have : 2 ^ b < 2 ^ (L + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  omega

/-- A congruence version of a coefficientwise identity on `[1, N]`. -/
theorem sub_mem_truncIdeal_of_apply {N : ℕ} {f g : ArithmeticFunction ℝ}
    (h : ∀ n, 1 ≤ n → n ≤ N → f n = g n) : f - g ∈ truncIdeal N :=
  fun n h1 hn => by rw [sub_apply', h n h1 hn, sub_self]

/-- **The logarithm of `ζ` is a plethystic sum**: `ℓ ≡ Σ_{a≤L} ψ^a(P)/a` modulo `I_N`, `N < 2^{L+1}`. -/
theorem primePowerLog_sub_plethLog_mem {N L : ℕ} (hNL : N < 2 ^ (L + 1)) :
    primePowerLog - plethLog L primeIndicator ∈ truncIdeal N := by
  refine sub_mem_truncIdeal_of_apply fun n h1 hn => ?_
  rw [plethLog, finsetSum_apply]
  simp only [single_one_mul_apply]
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, b, hp, hb, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    rw [sum_mPart_apply_prime_pow (fun m hm => primeIndicator_of_not_prime hm) (fun a => (a : ℝ)⁻¹)
      hp hb (exponent_le_of_lt_two_pow hp hn hNL), primePowerLog_apply,
      ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp,
      Nat.cast_pow, Real.log_pow]
    simp only [primeIndicator, ArithmeticFunction.coe_mk, if_pos hp, mul_one]
    have hlog : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    field_simp
  · rw [primePowerLog_apply, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
    exact (Finset.sum_eq_zero fun a ha => by
      rw [mPart_apply_of_not_isPrimePow (fun m hm => primeIndicator_of_not_prime hm)
        (Finset.mem_Icc.mp ha).1 hpp, mul_zero]).symm

/-- **The von Mangoldt function is a sum of Adams operations**: `Λ ≡ Σ_{a≤L} ψ^a(P_log)`. -/
theorem vonMangoldt_sub_sum_mPart_mem {N L : ℕ} (hNL : N < 2 ^ (L + 1)) :
    ArithmeticFunction.vonMangoldt - ∑ a ∈ Finset.Icc 1 L, RHTower.mPart a primeLog ∈
      truncIdeal N := by
  refine sub_mem_truncIdeal_of_apply fun n h1 hn => ?_
  rw [finsetSum_apply]
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, b, hp, hb, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have := sum_mPart_apply_prime_pow (fun m hm => primeLog_of_not_prime hm) (fun _ => 1)
      hp hb (exponent_le_of_lt_two_pow hp hn hNL)
    simp only [one_mul] at this
    rw [this, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp [primeLog, hp]
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    exact (Finset.sum_eq_zero fun a ha =>
      mPart_apply_of_not_isPrimePow (fun m hm => primeLog_of_not_prime hm)
        (Finset.mem_Icc.mp ha).1 hpp).symm

/-- Truncated exponentials respect congruences modulo `I_N`. -/
theorem expTrunc_sub_mem_of_sub_mem {N L : ℕ} {g g' : ArithmeticFunction ℝ}
    (h : g - g' ∈ truncIdeal N) : expTrunc L g - expTrunc L g' ∈ truncIdeal N := by
  rw [← Ideal.Quotient.eq] at h ⊢
  simp only [expTrunc, map_sum, map_mul, map_pow, h]

/-- **The window zeta operator is the plethystic exponential of the primes**:
`ζ ≡ exp Σ_{a≤L} ψ^a(P)/a` on every window with `e^A < 2^{L+1}`. -/
theorem expTrunc_plethLog_sub_zeta_mem {N L : ℕ} (hNL : N < 2 ^ (L + 1)) :
    expTrunc L (plethLog L primeIndicator) - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ∈
      truncIdeal N := by
  have h1 := expTrunc_sub_mem_of_sub_mem (L := L) (primePowerLog_sub_plethLog_mem hNL)
  have h2 := expTrunc_sub_zeta_mem (N := N) hNL
  have := Submodule.sub_mem _ h2 h1
  rwa [sub_sub_sub_cancel_left] at this

/-! ### The tower recursion -/

theorem windowRepFun_sum {ι : Type*} (A : ℝ) (s : Finset ι) (f : ι → ArithmeticFunction ℝ)
    (H : ℝ → ℝ) (u : ℝ) :
    windowRepFun A (∑ i ∈ s, f i) H u = ∑ i ∈ s, windowRepFun A (f i) H u := by
  simp only [windowRepFun, finsetSum_apply, Finset.sum_div, Finset.sum_mul]
  exact Finset.sum_comm

/-- The window operator of `f` depends only on `f` modulo `I_{⌊e^A⌋}`. -/
theorem windowRepFun_congr {A : ℝ} {f g : ArithmeticFunction ℝ}
    (h : f - g ∈ truncIdeal (windowLevel A)) (H : ℝ → ℝ) : windowRepFun A f H = windowRepFun A g H := by
  funext u
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨h1, hN⟩ := Finset.mem_Icc.mp hn
  have := h n h1 hN
  rw [sub_apply', sub_eq_zero] at this
  rw [this]

theorem dilate_dilate_inv {r : ℝ} (hr : r ≠ 0) (H : ℝ → ℝ) : dilate r (dilate r⁻¹ H) = H := by
  funext u; simp only [dilate]; congr 1; field_simp

/-- **The tower recursion of Weil's arithmetic operator**:
`ρ_A(Λ) = Σ_{a≤L} D_a ρ_{A/a}(P_log·n^{−(a−1)/2}) D_a^{−1}` whenever `e^A < 2^{L+1}`. -/
theorem windowRepFun_vonMangoldt_eq_sum_dilate {A : ℝ} {L : ℕ} (hL : windowLevel A < 2 ^ (L + 1))
    (H : ℝ → ℝ) :
    windowRepFun A ArithmeticFunction.vonMangoldt H = fun u =>
      ∑ a ∈ Finset.Icc 1 L, dilate a (windowRepFun (A / a) (tateTwist ((a - 1) / 2) primeLog)
        (dilate (a : ℝ)⁻¹ H)) u := by
  funext u
  rw [windowRepFun_congr (vonMangoldt_sub_sum_mPart_mem hL) H, windowRepFun_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have h := windowRepFun_mPart_dilate (A := A / a) ha1 primeLog (dilate (a : ℝ)⁻¹ H)
  rw [dilate_dilate_inv ha0, show (a : ℝ) * (A / a) = A by field_simp] at h
  rw [h]

end GaloisForLFunctions.WindowTowerOfSpecZ
