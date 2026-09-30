import GaloisForLFunctions.RHTower.WeilPositivityLogDensityMaximality
import GaloisForLFunctions.RHTower.WeilAbsoluteConvergenceRigidity
import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments

/-!
# Weil positivity forces a harmonically dense prime deficit set

Let `lam` be full-cone Weil-positive and `d = lam − Λ`.

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_thin_prime_deficit`). Suppose
- the deviation off the primes is absolutely harmonic, `Σ_{n not prime} |d(n)|/n < ∞`, and
- the prime deficit set `S⁻ = {p : lam(p) < log p}` is harmonically thin,
  `Σ_{p ∈ S⁻} log p / p < ∞`.

Then `lam(n) = Λ(n)` for every `n ≥ 2`. Nothing is assumed about the size of the deficits
`log p − lam(p)` on `S⁻`, nor about the excesses on the other primes.

**General form** (`eq_vonMangoldt_of_weilPositiveFull_of_signMult_aligned`). Let `σ_s` be a
completely multiplicative sign with `Σ_{p : s(p) = −1} log p/p < ∞`. If `d` has the sign of `σ_s`
except on an absolutely harmonic part, then `lam = Λ`. The prime law is the case where `s` is the
deficit sign of `lam`.

**Proof.**
- **Toeplitz inequality.** Apply the multiplicative Toeplitz bound of Weil positivity to the signed
  Gibbs resonator `c(m) = σ(m) m^{−1/2}`, `m ≤ N`. Here `σ` is the completely multiplicative sign
  with `σ(p) = −1` exactly on `S⁻` (`exists_signed_toeplitz_le`):
  `2 Σ_{n≤N} lam(n) σ(n) H_N(n)/n ≤ (log N + C₀) H(N)`, where `H_N(n) = Σ_{m ≤ N/n} 1/m`.
- **The `Λ` part.** It is the critical Gibbs energy `(½ + o(1)) H(N) log N`, up to the prime powers
  of `S⁻`, which cost `≤ 2 H(N) Σ_{p^k, p ∈ S⁻} Λ(p^k)/p^k`.
- **The prime part.** Since `d(p) σ(p) = |d(p)|`, it contributes `Σ_p |d(p)| H_N(p)/p`.
- **Conclusion.** Hence `Σ_p |d(p)| H_N(p)/p = O(H(N))`. At `N = M²` every `p ≤ M` has
  `H_N(p) ≥ log M`, so `Σ_{p ≤ M} |d(p)|/p` is bounded. Then `Σ |d(n)|/n < ∞`, and absolute
  convergence rigidity at `s = 1` gives `lam = Λ`.
-/

noncomputable section

open Complex Finset Filter Topology
open scoped Real ComplexConjugate

namespace RHTower.WeilPrimeDeficit

open RHTower.CriticalGibbs ArithmeticFunction

/-! ## Completely multiplicative signs -/

/-- The completely multiplicative sign `σ_s(m) = Π_p s(p)^{v_p(m)}`. -/
def signMult (s : ℕ → ℝ) (m : ℕ) : ℝ := m.factorization.prod fun p k => s p ^ k

theorem signMult_mul (s : ℕ → ℝ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    signMult s (a * b) = signMult s a * signMult s b := by
  unfold signMult
  rw [Nat.factorization_mul ha hb]
  exact Finsupp.prod_add_index' (fun p => pow_zero _) (fun p k l => pow_add _ _ _)

theorem signMult_prime_pow (s : ℕ → ℝ) {p k : ℕ} (hp : p.Prime) :
    signMult s (p ^ k) = s p ^ k := by
  unfold signMult
  rw [hp.factorization_pow]
  exact Finsupp.prod_single_index (pow_zero _)

theorem signMult_prime (s : ℕ → ℝ) {p : ℕ} (hp : p.Prime) : signMult s p = s p := by
  simpa using signMult_prime_pow s (k := 1) hp

theorem signMult_sq {s : ℕ → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) (m : ℕ) :
    signMult s m ^ 2 = 1 := by
  unfold signMult Finsupp.prod
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [← pow_mul, mul_comm, pow_mul]
  rcases hs p with h | h <;> simp [h]

theorem abs_signMult {s : ℕ → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) (m : ℕ) :
    |signMult s m| = 1 := by
  have h : |signMult s m| ^ 2 = 1 := by rw [sq_abs]; exact signMult_sq hs m
  have h0 := abs_nonneg (signMult s m)
  nlinarith

/-! ## The signed Gibbs resonator -/

/-- `H_N(n) = Σ_{m ≤ N, nm ≤ N} 1/m`. -/
def partialHarm (N n : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 N, if n * m ≤ N then (1 : ℝ) / m else 0

theorem partialHarm_nonneg (N n : ℕ) : 0 ≤ partialHarm N n :=
  Finset.sum_nonneg fun m _ => by split_ifs <;> positivity

theorem partialHarm_le_harm (N n : ℕ) : partialHarm N n ≤ harm N := by
  unfold partialHarm harm
  refine Finset.sum_le_sum fun m _ => ?_
  split_ifs
  · exact le_rfl
  · positivity

/-- `H(N) ≤ 1 + log N`. -/
theorem harm_le_one_add_log (N : ℕ) : harm N ≤ 1 + Real.log N := by
  induction N with
  | zero => simp [harm]
  | succ N ih =>
    unfold harm at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hstep : 1 / ((N + 1 : ℕ) : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log N := by
      have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      have h := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / ((N + 1 : ℕ) : ℝ) by positivity)
      rw [Real.log_div hN0.ne' hpos.ne'] at h
      have e : (N : ℝ) / ((N + 1 : ℕ) : ℝ) - 1 = -(1 / ((N + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp; ring
      linarith
    linarith

/-- **The signed Toeplitz inequality.** For a Weil-positive `lam` and every completely
multiplicative sign `σ_s`, `2 Σ_{2 ≤ n ≤ N} lam(n) σ_s(n) H_N(n)/n ≤ (log N + C₀) H(N)`. -/
theorem exists_signed_toeplitz_le {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    ∃ C₀ : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ s : ℕ → ℝ, (∀ p, s p = 1 ∨ s p = -1) →
      2 * ∑ n ∈ Finset.Icc 2 N, lam n * signMult s n * partialHarm N n / n ≤
        (Real.log N + C₀) * harm N := by
  obtain ⟨C₀, hC⟩ := weil_multiplicativeToeplitz_bound hW
  refine ⟨C₀, fun N hN s hs => ?_⟩
  set c : ℕ → ℂ := fun m => if m ≤ N then ((signMult s m / Real.sqrt m : ℝ) : ℂ) else 0
    with hc
  have hcN : ∀ m, N < m → c m = 0 := fun m hm => by simp [hc, not_le.mpr hm]
  have h := hC N hN c hcN
  have hmass : ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 = harm N := by
    unfold harm
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    simp only [hc, if_pos hmN, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
      signMult_sq hs, Real.sq_sqrt hm0.le]
  have hinner : ∀ n ∈ Finset.Icc 2 N,
      (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re =
        signMult s n / Real.sqrt n * partialHarm N n := by
    intro n hn
    obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [Complex.re_sum, partialHarm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    by_cases hnm : n * m ≤ N
    · simp only [hc, if_pos hnm, if_pos hmN, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      rw [signMult_mul s (by omega) (by omega), Nat.cast_mul,
        Real.sqrt_mul hn0.le]
      have hsm := signMult_sq hs m
      have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
      field_simp
      rw [hsm, Real.sq_sqrt hm0.le]
      ring
    · simp only [hc, if_neg hnm, zero_mul, Complex.zero_re, mul_zero]
  have hlhs : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
      (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re =
      ∑ n ∈ Finset.Icc 2 N, lam n * signMult s n * partialHarm N n / n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hinner n hn]
    obtain ⟨hn2, -⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    rw [show lam n / Real.sqrt n * (signMult s n / Real.sqrt n * partialHarm N n) =
      lam n * signMult s n * partialHarm N n / (Real.sqrt n * Real.sqrt n) by ring, hsq]
  rw [hlhs, hmass] at h
  exact h

/-! ## The deficit sign and the deficit weight -/

/-- The deficit sign `s(p) = −1` if `lam(p) < Λ(p)`, and `1` otherwise. -/
def deficitSign (lam : ℕ → ℝ) (p : ℕ) : ℝ := if lam p < vonMangoldt p then -1 else 1

theorem deficitSign_cases (lam : ℕ → ℝ) (p : ℕ) :
    deficitSign lam p = 1 ∨ deficitSign lam p = -1 := by
  unfold deficitSign; split_ifs <;> simp

/-- The sign weight `F_s(n) = Λ(n)/n` when `s = −1` at the least prime factor of `n`. -/
def signWeight (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  if s n.minFac = -1 then (vonMangoldt n : ℝ) / n else 0

theorem signWeight_nonneg (s : ℕ → ℝ) (n : ℕ) : 0 ≤ signWeight s n := by
  unfold signWeight
  split_ifs
  · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
  · exact le_rfl

/-- `Λ(n)/n − 2F_s(n) ≤ Λ(n) σ_s(n)/n`: the sign costs only on the prime powers of `{s = −1}`. -/
theorem vonMangoldt_div_sub_le {s : ℕ → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1) (n : ℕ) :
    (vonMangoldt n : ℝ) / n - 2 * signWeight s n ≤ vonMangoldt n * signMult s n / n := by
  have hF := signWeight_nonneg s n
  by_cases hΛ : (vonMangoldt n : ℝ) = 0
  · rw [hΛ]; simp only [zero_div, zero_mul, zero_sub]; linarith
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  rw [signMult_prime_pow _ hp]
  have hΛ0 : 0 ≤ (vonMangoldt (p ^ k) : ℝ) / ((p ^ k : ℕ) : ℝ) :=
    div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
  unfold signWeight
  rw [hp.pow_minFac hk.ne']
  rcases hs p with h | h
  · rw [h, one_pow, mul_one, if_neg (by norm_num)]; linarith
  · rw [h, if_pos rfl]
    have hle : (-1 : ℝ) ≤ (-1) ^ k := by
      rcases neg_one_pow_eq_or ℝ k with hk' | hk' <;> simp [hk']
    have e : (vonMangoldt (p ^ k) : ℝ) * (-1) ^ k / ((p ^ k : ℕ) : ℝ) =
        (-1) ^ k * ((vonMangoldt (p ^ k) : ℝ) / ((p ^ k : ℕ) : ℝ)) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hle hΛ0]

/-- The proper prime powers are harmonically summable: `Σ_{n not prime} Λ(n)/n < ∞`. -/
theorem summable_nonprime_vonMangoldt_div :
    Summable fun n : ℕ => if n.Prime then 0 else (vonMangoldt n : ℝ) / n := by
  set g : ℕ → ℝ := fun n => if n.Prime then 0 else (vonMangoldt n : ℝ) / n with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [hg]; split_ifs
    · exact le_rfl
    · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
  refine summable_of_sum_range_le (c := 72) hg0 fun T => ?_
  have h := RHTower.sum_nonprime_vonMangoldt_rpow_le (δ := 1 / 2) (by norm_num) (by norm_num) T
  have e : ∑ n ∈ (Finset.Icc 1 T).filter (fun n => ¬ n.Prime),
      (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 + 1 / 2 : ℝ)) = ∑ n ∈ Finset.Icc 1 T, g n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hg]
    by_cases hp : n.Prime
    · simp [hp]
    · simp only [hp, not_false_eq_true, if_true, if_false]
      rw [show -((1 : ℝ) / 2 + 1 / 2) = -1 by norm_num, Real.rpow_neg_one, div_eq_mul_inv]
  have hsub : ∑ n ∈ Finset.range T, g n ≤ ∑ n ∈ Finset.Icc 1 T, g n := by
    have h' : ∑ n ∈ Finset.range T, g n ≤ ∑ n ∈ insert 0 (Finset.Icc 1 T), g n :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
        rw [Finset.mem_range] at hn; rw [Finset.mem_insert, Finset.mem_Icc]; omega)
        (fun n _ _ => hg0 n)
    rwa [Finset.sum_insert (by simp), show g 0 = 0 by simp [hg], zero_add] at h'
  rw [← e] at hsub
  linarith [show (36 : ℝ) / (1 / 2) = 72 by norm_num]

/-- The harmonic thinness of `{p : s(p) = −1}` makes the sign weight summable. -/
theorem summable_signWeight {s : ℕ → ℝ}
    (hthin : Summable fun p : ℕ => if p.Prime ∧ s p = -1 then Real.log p / p else 0) :
    Summable (signWeight s) := by
  refine Summable.of_nonneg_of_le (signWeight_nonneg s) (fun n => ?_)
    (hthin.add summable_nonprime_vonMangoldt_div)
  unfold signWeight
  by_cases hp : n.Prime
  · rw [hp.minFac_eq, vonMangoldt_apply_prime hp]
    by_cases hl : s n = -1
    · simp [hp, hl]
    · simp [hp, hl]
  · simp only [hp, false_and, if_false, zero_add]
    split_ifs <;> first | exact le_rfl | exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)

/-! ## The prime part of the deviation is absolutely harmonic -/

theorem gibbsEnergy_eq_sum_partialHarm (N : ℕ) :
    gibbsEnergy N = ∑ n ∈ Finset.Icc 2 N, (vonMangoldt n : ℝ) * partialHarm N n / n := by
  rw [← sum_vonMangoldt_pairs_eq_gibbsEnergy]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold partialHarm
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs
  · ring
  · simp

/-- `H_{M²}(n) ≥ H(M)` for `n ≤ M`. -/
theorem harm_le_partialHarm_sq {M n : ℕ} (hn : n ≤ M) : harm M ≤ partialHarm (M * M) n := by
  unfold harm partialHarm
  calc ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / m
      = ∑ m ∈ Finset.Icc 1 M, (if n * m ≤ M * M then (1 : ℝ) / m else 0) :=
        Finset.sum_congr rfl fun m hm => by
          rw [if_pos (Nat.mul_le_mul hn (Finset.mem_Icc.mp hm).2)]
    _ ≤ ∑ m ∈ Finset.Icc 1 (M * M), (if n * m ≤ M * M then (1 : ℝ) / m else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (Nat.le_mul_self M)) (fun m _ _ => by
            split_ifs <;> positivity)

/-- **The aligned part of a Weil-positive deviation is absolutely harmonic.** Let `σ_s` be a
completely multiplicative sign whose set `{p : s(p) = −1}` is harmonically thin. If the part of
`d = lam − Λ` whose sign disagrees with `σ_s` is absolutely harmonic, then so is the part whose
sign agrees with `σ_s`. -/
theorem summable_aligned_abs_div {lam : ℕ → ℝ} (hW : WeilPositive lam) {s : ℕ → ℝ}
    (hs : ∀ p, s p = 1 ∨ s p = -1)
    (hthin : Summable fun p : ℕ => if p.Prime ∧ s p = -1 then Real.log p / p else 0)
    (hA : Summable fun n : ℕ => if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then 0
      else |lam n - vonMangoldt n| / n) :
    Summable fun n : ℕ => if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
      |lam n - vonMangoldt n| / n else 0 := by
  obtain ⟨C₀, hC⟩ := exists_signed_toeplitz_le hW
  have hF := summable_signWeight hthin
  set A := ∑' n : ℕ, (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then 0
    else |lam n - vonMangoldt n| / n) with hAdef
  set B := ∑' n : ℕ, signWeight s n with hBdef
  have hA0 : 0 ≤ A := tsum_nonneg fun n => by split_ifs <;> positivity
  have hB0 : 0 ≤ B := tsum_nonneg fun n => signWeight_nonneg s n
  set γ := Real.eulerMascheroniConstant with hγ
  have hγ0 : 0 ≤ γ := by have := Real.one_half_lt_eulerMascheroniConstant; linarith
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp tendsto_gibbs_rayleigh) 1 (by norm_num)
  set K : ℝ := (|C₀| + γ + 1 + 4 * B + 2 * A) / 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set P : ℕ → ℝ := fun N => ∑ n ∈ Finset.Icc 2 N,
    (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
      |lam n - vonMangoldt n| * partialHarm N n / n else 0) with hPdef
  have key : ∀ N : ℕ, max N₁ 1 ≤ N → P N ≤ K * harm N := by
    intro N hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hT := hC N hN1 s hs
    have hH := harm_pos hN1
    have hclose := hN₁ N (le_trans (le_max_left _ _) hN)
    rw [Real.dist_eq, sub_zero] at hclose
    have hlow : Real.log N - γ - 1 ≤ 2 * gibbsEnergy N / harm N := by
      have := (abs_lt.mp hclose).1; linarith
    have hG : (Real.log N - γ - 1) * harm N ≤ 2 * gibbsEnergy N := by
      rw [le_div_iff₀ hH] at hlow; linarith
    have hterm : ∀ n ∈ Finset.Icc 2 N,
        (vonMangoldt n : ℝ) * partialHarm N n / n - 2 * signWeight s n * harm N +
          (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
            |lam n - vonMangoldt n| * partialHarm N n / n else 0) -
          (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then 0
            else |lam n - vonMangoldt n| / n) * harm N ≤
        lam n * signMult s n * partialHarm N n / n := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega)
      have hH0 := partialHarm_nonneg N n
      have hHle := partialHarm_le_harm N n
      have hFn := signWeight_nonneg s n
      have hΛ := vonMangoldt_div_sub_le hs n
      have e : lam n * signMult s n * partialHarm N n / n =
          (vonMangoldt n : ℝ) * signMult s n / n * partialHarm N n +
            (lam n - vonMangoldt n) * signMult s n * partialHarm N n / n := by ring
      rw [e]
      have h1 := mul_le_mul_of_nonneg_right hΛ hH0
      rw [sub_mul] at h1
      have e2 : (vonMangoldt n : ℝ) * partialHarm N n / n =
          (vonMangoldt n : ℝ) / n * partialHarm N n := by ring
      have h2 : 2 * signWeight s n * partialHarm N n ≤ 2 * signWeight s n * harm N :=
        mul_le_mul_of_nonneg_left hHle (by positivity)
      have h3 : (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
            |lam n - vonMangoldt n| * partialHarm N n / n else 0) -
          (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then 0
            else |lam n - vonMangoldt n| / n) * harm N ≤
          (lam n - vonMangoldt n) * signMult s n * partialHarm N n / n := by
        have habs := abs_signMult hs n
        by_cases hal : 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n
        · rw [if_pos hal, if_pos hal, zero_mul, sub_zero]
          have hsd : (lam n - vonMangoldt n) * signMult s n = |lam n - vonMangoldt n| := by
            rw [← abs_of_nonneg hal.2, abs_mul, habs, mul_one]
          rw [hsd]
        · rw [if_neg hal, if_neg hal, zero_sub]
          have hlow2 : -(|lam n - vonMangoldt n| * partialHarm N n / n) ≤
              (lam n - vonMangoldt n) * signMult s n * partialHarm N n / n := by
            rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right hn0]
            have := neg_abs_le ((lam n - vonMangoldt n) * signMult s n)
            rw [abs_mul, habs, mul_one] at this
            nlinarith
          have hmono : |lam n - vonMangoldt n| * partialHarm N n / n ≤
              |lam n - vonMangoldt n| / n * harm N := by
            rw [div_mul_eq_mul_div]
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hHle (abs_nonneg _)) hn0.le
          linarith
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← gibbsEnergy_eq_sum_partialHarm] at hsum
    have hFsum : ∑ n ∈ Finset.Icc 2 N, 2 * signWeight s n * harm N ≤ 2 * (B * harm N) := by
      have h := hF.sum_le_tsum (Finset.Icc 2 N) (fun n _ => signWeight_nonneg s n)
      have e : ∑ n ∈ Finset.Icc 2 N, 2 * signWeight s n * harm N =
          2 * ((∑ n ∈ Finset.Icc 2 N, signWeight s n) * harm N) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right h hH.le
      linarith
    have hAsum : ∑ n ∈ Finset.Icc 2 N,
        (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then 0
          else |lam n - vonMangoldt n| / n) * harm N ≤ A * harm N := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right
        (hA.sum_le_tsum _ fun n _ => by split_ifs <;> positivity) hH.le
    have hC0 : C₀ * harm N ≤ |C₀| * harm N := mul_le_mul_of_nonneg_right (le_abs_self C₀) hH.le
    have eT : (Real.log N + C₀) * harm N = Real.log N * harm N + C₀ * harm N := by ring
    have eG : (Real.log N - γ - 1) * harm N = Real.log N * harm N - γ * harm N - harm N := by ring
    have eK : K * harm N = (|C₀| * harm N + γ * harm N + harm N + 4 * (B * harm N) +
        2 * (A * harm N)) / 2 := by rw [hK]; ring
    rw [eK]
    show P N ≤ _
    simp only [hPdef]
    linarith
  -- Tauberian step at `N = M²`
  set M₀ : ℕ := max (max N₁ 1) 3 with hM₀
  have hbound : ∀ M : ℕ, M₀ ≤ M →
      ∑ n ∈ Finset.Icc 2 M, (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
        |lam n - vonMangoldt n| / n else 0) ≤ 3 * K := by
    intro M hM
    have hM3 : 3 ≤ M := le_trans (le_max_right _ _) hM
    have hMM : max N₁ 1 ≤ M * M :=
      le_trans (le_max_left _ _) (le_trans hM (Nat.le_mul_self M))
    have hkey := key (M * M) hMM
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hlogM : 1 ≤ Real.log M := by
      rw [Real.le_log_iff_exp_le hM0]
      have := Real.exp_one_lt_d9
      have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM3
      linarith
    have hharmM : Real.log M ≤ harm M := by
      have := log_succ_le_harm M
      have : Real.log M ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log hM0 (by linarith)
      linarith
    have hharmMM : harm (M * M) ≤ 1 + 2 * Real.log M := by
      have := harm_le_one_add_log (M * M)
      rw [Nat.cast_mul, Real.log_mul hM0.ne' hM0.ne'] at this
      linarith
    have hsub : Real.log M * ∑ n ∈ Finset.Icc 2 M,
        (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
          |lam n - vonMangoldt n| / n else 0) ≤ P (M * M) := by
      rw [Finset.mul_sum]
      calc ∑ n ∈ Finset.Icc 2 M, Real.log M *
            (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
              |lam n - vonMangoldt n| / n else 0)
          ≤ ∑ n ∈ Finset.Icc 2 M,
            (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
              |lam n - vonMangoldt n| * partialHarm (M * M) n / n else 0) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hnM := (Finset.mem_Icc.mp hn).2
            have hn0 : (0 : ℝ) < n := by
              exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega)
            split_ifs
            · have hH := (hharmM.trans (harm_le_partialHarm_sq hnM))
              calc Real.log M * (|lam n - vonMangoldt n| / n)
                  = |lam n - vonMangoldt n| / n * Real.log M := mul_comm _ _
                _ ≤ |lam n - vonMangoldt n| / n * partialHarm (M * M) n :=
                    mul_le_mul_of_nonneg_left hH (div_nonneg (abs_nonneg _) hn0.le)
                _ = |lam n - vonMangoldt n| * partialHarm (M * M) n / n := by ring
            · simp
        _ ≤ P (M * M) := by
            simp only [hPdef]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right (Nat.le_mul_self M)) (fun n _ _ => by
                split_ifs
                · exact div_nonneg (mul_nonneg (abs_nonneg _) (partialHarm_nonneg _ _))
                    (Nat.cast_nonneg _)
                · exact le_rfl)
    have hfin : Real.log M * ∑ n ∈ Finset.Icc 2 M,
        (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
          |lam n - vonMangoldt n| / n else 0) ≤ 3 * K * Real.log M := by
      calc _ ≤ P (M * M) := hsub
        _ ≤ K * harm (M * M) := hkey
        _ ≤ K * (1 + 2 * Real.log M) := mul_le_mul_of_nonneg_left hharmMM hK0
        _ ≤ 3 * K * Real.log M := by nlinarith
    have hlogpos : 0 < Real.log M := by linarith
    rw [mul_comm (Real.log M)] at hfin
    exact le_of_mul_le_mul_right hfin hlogpos
  refine summable_of_sum_range_le (c := 3 * K) (fun n => by split_ifs <;> positivity)
    fun T => ?_
  set M := max T M₀ with hMdef
  have hTM : T ≤ M + 1 := by omega
  calc ∑ n ∈ Finset.range T, (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
        |lam n - vonMangoldt n| / n else 0)
      ≤ ∑ n ∈ Finset.range (M + 1), (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
          |lam n - vonMangoldt n| / n else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hTM)
          (fun n _ _ => by split_ifs <;> positivity)
    _ = ∑ n ∈ Finset.Icc 2 M, (if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then
          |lam n - vonMangoldt n| / n else 0) := by
        refine (Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_).symm
        · rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
        · rw [Finset.mem_range] at hn
          rw [Finset.mem_Icc] at hn'
          have hn2 : n < 2 := by omega
          rw [if_neg (by intro h; omega)]
    _ ≤ 3 * K := hbound M (le_max_right _ _)

/-! ## The sign laws -/

/-- **Weil positivity rules out multiplicatively signed deviations.** Let `lam` be full-cone
Weil-positive and `σ_s` a completely multiplicative sign with `Σ_{p : s(p) = −1} log p/p < ∞`. If
`lam − Λ` has the sign of `σ_s` except on an absolutely harmonic part, then `lam(n) = Λ(n)` for
every `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_signMult_aligned {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {s : ℕ → ℝ} (hs : ∀ p, s p = 1 ∨ s p = -1)
    (hthin : Summable fun p : ℕ => if p.Prime ∧ s p = -1 then Real.log p / p else 0)
    (hA : Summable fun n : ℕ => if 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult s n then 0
      else |lam n - vonMangoldt n| / n) :
    ∀ n, 2 ≤ n → lam n = vonMangoldt n := by
  have hP := summable_aligned_abs_div (weilPositive_of_weilPositiveFull hW) hs hthin hA
  refine WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_summable_div hW ((hP.add hA).congr
    fun n => ?_)
  split_ifs <;> simp [div_eq_mul_inv]

/-- **Weil positivity forces a harmonically dense prime deficit set.** Let `lam` be full-cone
Weil-positive, with `Σ_{n not prime} |lam(n) − Λ(n)|/n < ∞` and
`Σ_{p prime, lam(p) < log p} log p / p < ∞`. Then `lam(n) = Λ(n)` for every `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_thin_prime_deficit {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hA : Summable fun n : ℕ => if n.Prime then 0 else |lam n - vonMangoldt n| / n)
    (hB : Summable fun p : ℕ => if p.Prime ∧ lam p < vonMangoldt p then Real.log p / p else 0) :
    ∀ n, 2 ≤ n → lam n = vonMangoldt n := by
  have hs := deficitSign_cases lam
  refine eq_vonMangoldt_of_weilPositiveFull_of_signMult_aligned hW hs
    (hB.congr fun p => ?_) (hA.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      fun n => ?_)
  · unfold deficitSign
    by_cases hl : lam p < vonMangoldt p
    · simp [hl]
    · have : ¬ ((1 : ℝ) = -1) := by norm_num
      simp [hl, this]
  · by_cases hp : n.Prime
    · have hal : 2 ≤ n ∧ 0 ≤ (lam n - vonMangoldt n) * signMult (deficitSign lam) n := by
        refine ⟨hp.two_le, ?_⟩
        rw [signMult_prime _ hp]
        unfold deficitSign
        split_ifs with hl
        · nlinarith
        · nlinarith
      rw [if_pos hal, if_pos hp]
    · rw [if_neg hp]
      split_ifs
      · positivity
      · exact le_rfl

/-- **Prime-supported deviations.** A full-cone Weil-positive `lam` that agrees with `Λ` on every
non-prime `n ≥ 2` and has a harmonically thin prime deficit set equals `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_prime_support {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hsupp : ∀ n, 2 ≤ n → ¬ n.Prime → lam n = vonMangoldt n)
    (hB : Summable fun p : ℕ => if p.Prime ∧ lam p < vonMangoldt p then Real.log p / p else 0) :
    ∀ n, 2 ≤ n → lam n = vonMangoldt n := by
  refine eq_vonMangoldt_of_weilPositiveFull_of_thin_prime_deficit hW
    (summable_of_ne_finset_zero (s := {1}) fun n hn => ?_) hB
  rw [Finset.mem_singleton] at hn
  split_ifs with hp
  · rfl
  · rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 0 := by omega
      simp
    · rw [hsupp n h hp, sub_self, abs_zero, zero_div]

end RHTower.WeilPrimeDeficit
