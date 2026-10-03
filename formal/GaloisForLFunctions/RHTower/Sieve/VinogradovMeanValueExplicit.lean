import GaloisForLFunctions.RHTower.Sieve.VinogradovChebyshevReservoir
import GaloisForLFunctions.RHTower.Sieve.VinogradovMeanValueExponentialDecay

/-!
# Vinogradov's mean value theorem with explicit constants

With the Chebyshev reservoir every prime of the moment recursion satisfies `p^k ≤ 16^k N`, and the
recursion closes with an explicit constant: for `k ≥ 3`, every `s` and every `N ≥ 1`,

`J_{s,k}(N) ≤ z^{kK} Λ^s 2^{s²/k} N^{2s - K + K(1 - 1/k)^{s/k}}`

where `K = k(k+1)/2`, `R = k(k² - k) + 1`, `z = max(2²⁴, 81R², k)` and `Λ = 4R² k! 16^{k²}`
(`card_vinogradovDiagonalSolution_le_explicit`).

For `s ≥ k² log k` the constant contributes `(z^{kK} Λ^s 2^{s²/k})^{1/s²} = O(1)` uniformly in `k`,
which is what a Weyl-sum estimate with growing degree needs.

Below the threshold `⌈N^{1/k}⌉ < z` the trivial bound `N^{2s} ≤ z^{kK} N^{λ(s)}` is used; above it
the recursion `exists_vinogradov_moment_chebyshev_recurrence` gives
`J_s ≤ 2(R² k! 2^{2(s-k)} 16^{k²} C_{s-k} + (k² - k)² C_{s-2}) N^{λ(s)}`, and the choice of `Λ`
makes each of the two terms at most a quarter of `z^{kK} Λ^s 2^{s²/k}`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The threshold `z = max(2²⁴, 81R², k)`. -/
def vinogradovExplicitThreshold (k : ℕ) : ℕ :=
  max (max (2 ^ 24) (81 * vinogradovChebyshevReservoirSize k ^ 2)) k

/-- The growth factor `Λ = 4R² k! 16^{k²}`. -/
def vinogradovExplicitGrowth (k : ℕ) : ℕ :=
  4 * vinogradovChebyshevReservoirSize k ^ 2 * k.factorial * 16 ^ (k * k)

/-- The explicit constant `z^{kK} Λ^s 2^{s²/k}`. -/
def vinogradovExplicitConstant (k s : ℕ) : ℝ :=
  (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2)) *
    (vinogradovExplicitGrowth k : ℝ) ^ s * (2 : ℝ) ^ ((s : ℝ) ^ 2 / k)

theorem one_le_vinogradovExplicitThreshold (k : ℕ) : 1 ≤ vinogradovExplicitThreshold k := by
  unfold vinogradovExplicitThreshold
  have : 1 ≤ 2 ^ 24 := Nat.one_le_two_pow
  omega

theorem vinogradovExplicitConstant_pos (k s : ℕ) : 0 < vinogradovExplicitConstant k s := by
  unfold vinogradovExplicitConstant
  have h1 : (1 : ℝ) ≤ vinogradovExplicitThreshold k := by
    exact_mod_cast one_le_vinogradovExplicitThreshold k
  have h2 : 0 < vinogradovExplicitGrowth k := by
    unfold vinogradovExplicitGrowth; positivity
  have h2' : (0 : ℝ) < vinogradovExplicitGrowth k := by exact_mod_cast h2
  positivity

theorem k_le_vinogradovExplicitGrowth (k : ℕ) : k ≤ vinogradovExplicitGrowth k := by
  unfold vinogradovExplicitGrowth
  have h1 : k ≤ k.factorial := Nat.self_le_factorial k
  have h2 : 1 ≤ 4 * vinogradovChebyshevReservoirSize k ^ 2 := by
    have : 1 ≤ vinogradovChebyshevReservoirSize k ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    omega
  have h3 : 1 ≤ 16 ^ (k * k) := Nat.one_le_pow _ _ (by norm_num)
  calc k ≤ k.factorial := h1
    _ = 1 * k.factorial * 1 := by ring
    _ ≤ 4 * vinogradovChebyshevReservoirSize k ^ 2 * k.factorial * 16 ^ (k * k) := by
        gcongr

/-- Prime power bound in the large regime: `p ≤ 4(⌈N^{1/k}⌉ + k)` and `k ≤ ⌈N^{1/k}⌉` give
`p^k ≤ 16^k N`. -/
theorem pow_le_sixteen_pow_mul_of_le_four_base {N k p : ℕ} (hk : k ≠ 0) (hN : N ≠ 0)
    (hkr : k ≤ vinogradovCeilRoot k N) (hp : p ≤ 4 * vinogradovChebyshevBase N k) :
    p ^ k ≤ 16 ^ k * N := by
  set r := vinogradovCeilRoot k N
  have hp8 : p ≤ 8 * r := by
    have : vinogradovChebyshevBase N k = r + k := rfl
    omega
  calc p ^ k ≤ (8 * r) ^ k := Nat.pow_le_pow_left hp8 k
    _ = 8 ^ k * r ^ k := mul_pow 8 r k
    _ ≤ 8 ^ k * (2 ^ k * N) := Nat.mul_le_mul_left _ (vinogradovCeilRoot_pow_le hk hN)
    _ = 16 ^ k * N := by rw [← mul_assoc, ← mul_pow]; norm_num

/-- In the large regime the reservoir primes are at most `N`. -/
theorem le_of_le_four_base {N k p : ℕ} (hk : 2 ≤ k) (hN : N ≠ 0)
    (hz : 2 ^ 24 ≤ vinogradovCeilRoot k N) (hkr : k ≤ vinogradovCeilRoot k N)
    (hp : p ≤ 4 * vinogradovChebyshevBase N k) : p ≤ N := by
  set r := vinogradovCeilRoot k N
  have hp8 : p ≤ 8 * r := by
    have : vinogradovChebyshevBase N k = r + k := rfl
    omega
  have hpred : (r - 1) ^ k < N := pred_vinogradovCeilRoot_pow_lt (by omega) hN
  have hsq : 8 * r ≤ (r - 1) ^ 2 := by
    have h1 : 16 ≤ r - 1 := by omega
    have h2 : 8 * r ≤ 16 * (r - 1) := by omega
    calc 8 * r ≤ 16 * (r - 1) := h2
      _ ≤ (r - 1) * (r - 1) := Nat.mul_le_mul_right _ h1
      _ = (r - 1) ^ 2 := (sq _).symm
  have hk2 : (r - 1) ^ 2 ≤ (r - 1) ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

theorem cast_mul_pred_div_two (k : ℕ) (hk : 1 ≤ k) :
    ((k * (k - 1) / 2 : ℕ) : ℝ) = (k * (k - 1) / 2 : ℝ) := by
  rw [Nat.cast_div (Nat.even_mul_pred_self k).two_dvd (by norm_num), Nat.cast_mul,
    Nat.cast_sub hk]
  norm_num

theorem cast_mul_succ_div_two (k : ℕ) :
    ((k * (k + 1) / 2 : ℕ) : ℝ) = (k * (k + 1) / 2 : ℝ) := by
  rw [Nat.cast_div (Nat.even_mul_succ_self k).two_dvd (by norm_num)]
  push_cast; ring

/-- One good term of the recursion: a prime `p` with `p M ≤ 2N`, `p^k ≤ 16^k N` and a bound
`J ≤ C M^{λ}` for the tail moment. -/
theorem vinogradov_good_term_le {k b p M N : ℕ} {J C lb e target : ℝ} (hk : 1 ≤ k)
    (hp : 1 ≤ p) (hN : 1 ≤ N) (hpM : p * M ≤ 2 * N) (hpk : p ^ k ≤ 16 ^ k * N)
    (hJ : J ≤ C * (M : ℝ) ^ lb) (hC : 0 ≤ C) (hlb0 : 0 ≤ lb) (hlb2 : lb ≤ 2 * b)
    (he : e = 2 * b + (k * (k - 1) / 2 : ℝ) - lb) (he0 : 0 ≤ e) (he_le : e ≤ (k * k : ℝ))
    (hexp : (k : ℝ) + lb + e / k = target) :
    (p : ℝ) ^ (2 * b) * ((N : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * J)) ≤
      (k.factorial : ℝ) * C * (2 : ℝ) ^ (2 * b) * (16 : ℝ) ^ (k * k) * (N : ℝ) ^ target := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hk0' : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hpowe : (p : ℝ) ^ (2 * b) * (p : ℝ) ^ (k * (k - 1) / 2) * (M : ℝ) ^ lb ≤
      (p : ℝ) ^ e * (2 * (N : ℝ)) ^ lb := by
    have h1 : (p : ℝ) ^ (2 * b) * (p : ℝ) ^ (k * (k - 1) / 2) = (p : ℝ) ^ e * (p : ℝ) ^ lb := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hp0, ← Real.rpow_add hp0,
        cast_mul_pred_div_two k hk, he]
      congr 1
      push_cast
      ring
    have h2 : (p : ℝ) ^ lb * (M : ℝ) ^ lb ≤ (2 * (N : ℝ)) ^ lb := by
      rw [← Real.mul_rpow hp0.le (by positivity)]
      apply Real.rpow_le_rpow (by positivity) _ hlb0
      exact_mod_cast hpM
    calc (p : ℝ) ^ (2 * b) * (p : ℝ) ^ (k * (k - 1) / 2) * (M : ℝ) ^ lb
        = (p : ℝ) ^ e * ((p : ℝ) ^ lb * (M : ℝ) ^ lb) := by rw [h1]; ring
      _ ≤ (p : ℝ) ^ e * (2 * (N : ℝ)) ^ lb :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hp0.le _)
  have hpe : (p : ℝ) ^ e ≤ (16 : ℝ) ^ (k * k) * (N : ℝ) ^ (e / k) := by
    have e1 : (p : ℝ) ^ e = ((p : ℝ) ^ k) ^ (e / k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      congr 1
      field_simp
    have hpkR : (p : ℝ) ^ k ≤ (16 : ℝ) ^ k * N := by exact_mod_cast hpk
    have h16 : ((16 : ℝ) ^ k) ^ (e / k) ≤ (16 : ℝ) ^ (k * k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [show (k : ℝ) * (e / k) = e by field_simp]
      push_cast
      exact he_le
    calc (p : ℝ) ^ e = ((p : ℝ) ^ k) ^ (e / k) := e1
      _ ≤ ((16 : ℝ) ^ k * N) ^ (e / k) :=
          Real.rpow_le_rpow (by positivity) hpkR (by positivity)
      _ = ((16 : ℝ) ^ k) ^ (e / k) * (N : ℝ) ^ (e / k) := Real.mul_rpow (by positivity) hN0.le
      _ ≤ (16 : ℝ) ^ (k * k) * (N : ℝ) ^ (e / k) :=
          mul_le_mul_of_nonneg_right h16 (Real.rpow_nonneg hN0.le _)
  have hNpow : (N : ℝ) ^ k * (N : ℝ) ^ lb * (N : ℝ) ^ (e / k) = (N : ℝ) ^ target := by
    rw [← hexp, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]
  have h2N : (2 * (N : ℝ)) ^ lb ≤ (2 : ℝ) ^ (2 * b) * (N : ℝ) ^ lb := by
    rw [Real.mul_rpow (by norm_num) hN0.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast; exact hlb2
  have hM0 : (0 : ℝ) ≤ (M : ℝ) ^ lb := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (p : ℝ) ^ (2 * b) * ((N : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * J))
      ≤ (p : ℝ) ^ (2 * b) * ((N : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) *
        (C * (M : ℝ) ^ lb))) := by gcongr
    _ = (k.factorial : ℝ) * C * (N : ℝ) ^ k *
        ((p : ℝ) ^ (2 * b) * (p : ℝ) ^ (k * (k - 1) / 2) * (M : ℝ) ^ lb) := by ring
    _ ≤ (k.factorial : ℝ) * C * (N : ℝ) ^ k * ((p : ℝ) ^ e * (2 * (N : ℝ)) ^ lb) :=
        mul_le_mul_of_nonneg_left hpowe (by positivity)
    _ ≤ (k.factorial : ℝ) * C * (N : ℝ) ^ k *
        (((16 : ℝ) ^ (k * k) * (N : ℝ) ^ (e / k)) * ((2 : ℝ) ^ (2 * b) * (N : ℝ) ^ lb)) := by
        gcongr
    _ = (k.factorial : ℝ) * C * (2 : ℝ) ^ (2 * b) * (16 : ℝ) ^ (k * k) *
        ((N : ℝ) ^ k * (N : ℝ) ^ lb * (N : ℝ) ^ (e / k)) := by ring
    _ = _ := by rw [hNpow]

/-- The good-term constant is at most a quarter of the next constant. -/
theorem vinogradovExplicitConstant_good_le {k : ℕ} (hk : 1 ≤ k) (b : ℕ) :
    (vinogradovChebyshevReservoirSize k : ℝ) ^ 2 * (k.factorial : ℝ) *
        vinogradovExplicitConstant k b * (2 : ℝ) ^ (2 * b) * (16 : ℝ) ^ (k * k) ≤
      vinogradovExplicitConstant k (k + b) / 4 := by
  unfold vinogradovExplicitConstant
  set z := vinogradovExplicitThreshold k
  set Λ := vinogradovExplicitGrowth k with hΛ
  have hz : (0 : ℝ) ≤ (z : ℝ) ^ (k * (k * (k + 1) / 2)) := by positivity
  have hΛ1 : (1 : ℝ) ≤ Λ := le_trans (show (1 : ℝ) ≤ k by exact_mod_cast hk)
    (show (k : ℝ) ≤ Λ by exact_mod_cast k_le_vinogradovExplicitGrowth k)
  have hΛdef : (Λ : ℝ) =
      4 * (vinogradovChebyshevReservoirSize k : ℝ) ^ 2 * (k.factorial : ℝ) *
        (16 : ℝ) ^ (k * k) := by
    rw [hΛ, vinogradovExplicitGrowth, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat]
  have hΛpow : (Λ : ℝ) ≤ (Λ : ℝ) ^ k := by
    calc (Λ : ℝ) = (Λ : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (Λ : ℝ) ^ k := pow_le_pow_right₀ hΛ1 hk
  have hk1 : (0 : ℝ) < k := by exact_mod_cast hk
  have h2exp : (2 : ℝ) ^ (2 * b) * (2 : ℝ) ^ ((b : ℝ) ^ 2 / k) ≤
      (2 : ℝ) ^ ((((k + b : ℕ) : ℝ)) ^ 2 / k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have e : (((k + b : ℕ) : ℝ)) ^ 2 / k = (b : ℝ) ^ 2 / k + ((k : ℝ) + 2 * b) := by
      field_simp
      push_cast
      ring
    rw [e]
    push_cast
    linarith
  rw [pow_add]
  have hb0 : (0 : ℝ) ≤ (Λ : ℝ) ^ b := by positivity
  calc (vinogradovChebyshevReservoirSize k : ℝ) ^ 2 * (k.factorial : ℝ) *
        ((z : ℝ) ^ (k * (k * (k + 1) / 2)) * (Λ : ℝ) ^ b * (2 : ℝ) ^ ((b : ℝ) ^ 2 / k)) *
        (2 : ℝ) ^ (2 * b) * (16 : ℝ) ^ (k * k)
      = ((vinogradovChebyshevReservoirSize k : ℝ) ^ 2 * (k.factorial : ℝ) * (16 : ℝ) ^ (k * k)) *
        (z : ℝ) ^ (k * (k * (k + 1) / 2)) * (Λ : ℝ) ^ b *
        ((2 : ℝ) ^ (2 * b) * (2 : ℝ) ^ ((b : ℝ) ^ 2 / k)) := by ring
    _ ≤ ((Λ : ℝ) / 4) * (z : ℝ) ^ (k * (k * (k + 1) / 2)) * (Λ : ℝ) ^ b *
        (2 : ℝ) ^ ((((k + b : ℕ) : ℝ)) ^ 2 / k) := by
        gcongr
        rw [hΛdef]; linarith
    _ ≤ ((Λ : ℝ) ^ k / 4) * (z : ℝ) ^ (k * (k * (k + 1) / 2)) * (Λ : ℝ) ^ b *
        (2 : ℝ) ^ ((((k + b : ℕ) : ℝ)) ^ 2 / k) := by gcongr
    _ = (z : ℝ) ^ (k * (k * (k + 1) / 2)) * ((Λ : ℝ) ^ k * (Λ : ℝ) ^ b) *
        (2 : ℝ) ^ ((((k + b : ℕ) : ℝ)) ^ 2 / k) / 4 := by ring

/-- The collision constant is at most a quarter of the next constant. -/
theorem vinogradovExplicitConstant_collision_le {k : ℕ} (hk : 2 ≤ k) (b : ℕ) :
    ((k * k - k : ℕ) : ℝ) ^ 2 * vinogradovExplicitConstant k (k - 2 + b) ≤
      vinogradovExplicitConstant k (k + b) / 4 := by
  have hgrow : (k * k - k) * 2 ≤ vinogradovExplicitGrowth k := by
    unfold vinogradovExplicitGrowth
    have hR : k * k - k ≤ vinogradovChebyshevReservoirSize k := by
      unfold vinogradovChebyshevReservoirSize
      have : k * k - k ≤ k * (k * k - k) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hR2 : vinogradovChebyshevReservoirSize k ≤ vinogradovChebyshevReservoirSize k ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    have hf : 1 ≤ k.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
    have h16 : 1 ≤ 16 ^ (k * k) := Nat.one_le_pow _ _ (by norm_num)
    calc (k * k - k) * 2 ≤ 4 * vinogradovChebyshevReservoirSize k ^ 2 * 1 * 1 := by omega
      _ ≤ 4 * vinogradovChebyshevReservoirSize k ^ 2 * k.factorial * 16 ^ (k * k) := by gcongr
  unfold vinogradovExplicitConstant
  set z := vinogradovExplicitThreshold k
  set Λ := vinogradovExplicitGrowth k with hΛ
  have hkkΛ : ((k * k - k : ℕ) : ℝ) * 2 ≤ (Λ : ℝ) := by exact_mod_cast hgrow
  have hkk : ((k * k - k : ℕ) : ℝ) ^ 2 * 4 ≤ (Λ : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ((k * k - k : ℕ) : ℝ) * 2 := by positivity
    nlinarith
  have hidx : k + b = (k - 2 + b) + 2 := by omega
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2exp : (2 : ℝ) ^ ((((k - 2 + b : ℕ) : ℝ)) ^ 2 / k) ≤
      (2 : ℝ) ^ ((((k + b : ℕ) : ℝ)) ^ 2 / k) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply div_le_div_of_nonneg_right _ hk0
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast (show k - 2 + b ≤ k + b by omega)
  have hΛs : (Λ : ℝ) ^ (k + b) = (Λ : ℝ) ^ (k - 2 + b) * (Λ : ℝ) ^ 2 := by
    rw [← pow_add, ← hidx]
  rw [hΛs]
  have hz : (0 : ℝ) ≤ (z : ℝ) ^ (k * (k * (k + 1) / 2)) := by positivity
  have hc0 : (0 : ℝ) ≤ (Λ : ℝ) ^ (k - 2 + b) := by positivity
  calc ((k * k - k : ℕ) : ℝ) ^ 2 *
        ((z : ℝ) ^ (k * (k * (k + 1) / 2)) * (Λ : ℝ) ^ (k - 2 + b) *
          (2 : ℝ) ^ ((((k - 2 + b : ℕ) : ℝ)) ^ 2 / k))
      ≤ ((Λ : ℝ) ^ 2 / 4) * ((z : ℝ) ^ (k * (k * (k + 1) / 2)) * (Λ : ℝ) ^ (k - 2 + b) *
          (2 : ℝ) ^ ((((k + b : ℕ) : ℝ)) ^ 2 / k)) := by
        gcongr
        linarith
    _ = (z : ℝ) ^ (k * (k * (k + 1) / 2)) * ((Λ : ℝ) ^ (k - 2 + b) * (Λ : ℝ) ^ 2) *
        (2 : ℝ) ^ ((((k + b : ℕ) : ℝ)) ^ 2 / k) / 4 := by ring

/-- The defect gap: `2s - λ(s) ≤ K`. -/
theorem two_mul_sub_vinogradovDecayExponent_le {k : ℕ} (hk : 2 ≤ k) (s : ℕ) :
    2 * (s : ℝ) - vinogradovDecayExponent k s ≤ (k * (k + 1) / 2 : ℝ) := by
  have hθ := Real.rpow_nonneg (rpow_one_sub_inv_pos (k := k) hk).le ((s : ℝ) / k)
  have hK0 : (0 : ℝ) ≤ k * (k + 1) / 2 := by positivity
  have hm := mul_nonneg hK0 hθ
  unfold vinogradovDecayExponent
  linarith

/-- **Vinogradov's mean value theorem with explicit constants.** -/
theorem card_vinogradovDiagonalSolution_le_explicit {k : ℕ} (hk : 3 ≤ k) (s N : ℕ)
    (hN : N ≠ 0) :
    (Fintype.card (VinogradovDiagonalSolution N s k) : ℝ) ≤
      vinogradovExplicitConstant k s * (N : ℝ) ^ vinogradovDecayExponent k s := by
  induction s using Nat.strong_induction_on generalizing N with
  | _ s ih =>
  have hk0 : k ≠ 0 := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hz1 : (1 : ℝ) ≤ vinogradovExplicitThreshold k := by
    exact_mod_cast one_le_vinogradovExplicitThreshold k
  have hΛk : (k : ℝ) ≤ vinogradovExplicitGrowth k := by
    exact_mod_cast k_le_vinogradovExplicitGrowth k
  have hΛ1 : (1 : ℝ) ≤ vinogradovExplicitGrowth k :=
    le_trans (by exact_mod_cast (by omega : 1 ≤ k)) hΛk
  have hlam_ge := le_vinogradovDecayExponent hk s
  have hCpos := vinogradovExplicitConstant_pos k s
  have hC_ge_z : (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2)) ≤
      vinogradovExplicitConstant k s := by
    unfold vinogradovExplicitConstant
    have h1 : (1 : ℝ) ≤ (vinogradovExplicitGrowth k : ℝ) ^ s := one_le_pow₀ hΛ1
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((s : ℝ) ^ 2 / k) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have h0 : (0 : ℝ) ≤ (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2)) := by
      positivity
    calc (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2))
        = (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2)) * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  -- small regime
  by_cases hsmall : vinogradovCeilRoot k N < vinogradovExplicitThreshold k
  · have hNz : N ≤ vinogradovExplicitThreshold k ^ k :=
      (le_vinogradovCeilRoot_pow hk0).trans (Nat.pow_le_pow_left hsmall.le k)
    have hNzR : (N : ℝ) ≤ (vinogradovExplicitThreshold k : ℝ) ^ k := by exact_mod_cast hNz
    have htriv : (Fintype.card (VinogradovDiagonalSolution N s k) : ℝ) ≤ (N : ℝ) ^ (2 * s) := by
      exact_mod_cast card_vinogradovDiagonalSolution_le_trivial N s k
    have hgap : 2 * (s : ℝ) - vinogradovDecayExponent k s ≤ ((k * (k + 1) / 2 : ℕ) : ℝ) := by
      rw [cast_mul_succ_div_two]
      exact two_mul_sub_vinogradovDecayExponent_le (by omega) s
    have hgap0 : 0 ≤ 2 * (s : ℝ) - vinogradovDecayExponent k s := by
      linarith [vinogradovDecayExponent_le hk s]
    have hsplit : (N : ℝ) ^ (2 * s) = (N : ℝ) ^ (2 * (s : ℝ) - vinogradovDecayExponent k s) *
        (N : ℝ) ^ vinogradovDecayExponent k s := by
      rw [← Real.rpow_add hN0, ← Real.rpow_natCast]
      congr 1; push_cast; ring
    have hrest : (N : ℝ) ^ (2 * (s : ℝ) - vinogradovDecayExponent k s) ≤
        (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2)) := by
      calc (N : ℝ) ^ (2 * (s : ℝ) - vinogradovDecayExponent k s)
          ≤ ((vinogradovExplicitThreshold k : ℝ) ^ k) ^
              (2 * (s : ℝ) - vinogradovDecayExponent k s) :=
            Real.rpow_le_rpow hN0.le hNzR hgap0
        _ ≤ ((vinogradovExplicitThreshold k : ℝ) ^ k) ^ (((k * (k + 1) / 2 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hz1) hgap
        _ = (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2)) := by
            rw [Real.rpow_natCast, ← pow_mul]
    calc (Fintype.card (VinogradovDiagonalSolution N s k) : ℝ)
        ≤ (N : ℝ) ^ (2 * (s : ℝ) - vinogradovDecayExponent k s) *
          (N : ℝ) ^ vinogradovDecayExponent k s := htriv.trans hsplit.le
      _ ≤ vinogradovExplicitConstant k s * (N : ℝ) ^ vinogradovDecayExponent k s :=
          mul_le_mul_of_nonneg_right (hrest.trans hC_ge_z) (by positivity)
  replace hsmall := le_of_not_gt hsmall
  -- base `s ≤ k`
  by_cases hsk : s ≤ k
  · have hJ : (Fintype.card (VinogradovDiagonalSolution N s k) : ℝ) ≤
        (s.factorial : ℝ) * (N : ℝ) ^ s := by
      exact_mod_cast card_vinogradovDiagonalSolution_le hsk
    have hfact : (s.factorial : ℝ) ≤ vinogradovExplicitConstant k s := by
      unfold vinogradovExplicitConstant
      have hsf : (s.factorial : ℝ) ≤ (vinogradovExplicitGrowth k : ℝ) ^ s := by
        have h1 : s.factorial ≤ s ^ s := Nat.factorial_le_pow s
        have h2 : (s : ℝ) ≤ vinogradovExplicitGrowth k := le_trans (by exact_mod_cast hsk) hΛk
        calc (s.factorial : ℝ) ≤ (s : ℝ) ^ s := by exact_mod_cast h1
          _ ≤ (vinogradovExplicitGrowth k : ℝ) ^ s := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 s
      have h1 : (1 : ℝ) ≤ (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2)) :=
        one_le_pow₀ hz1
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((s : ℝ) ^ 2 / k) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      calc (s.factorial : ℝ) ≤ (vinogradovExplicitGrowth k : ℝ) ^ s := hsf
        _ = 1 * (vinogradovExplicitGrowth k : ℝ) ^ s * 1 := by ring
        _ ≤ _ := by gcongr
    refine hJ.trans (mul_le_mul hfact ?_ (by positivity) hCpos.le)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hlam_ge
  replace hsk := lt_of_not_ge hsk
  obtain ⟨b, rfl⟩ : ∃ b, s = k + b := ⟨s - k, by omega⟩
  have hb : b ≠ 0 := by omega
  -- large regime
  have hthr := hsmall
  unfold vinogradovExplicitThreshold at hthr
  have hy24 : 2 ^ 24 ≤ vinogradovChebyshevBase N k := by
    show 2 ^ 24 ≤ vinogradovCeilRoot k N + k
    omega
  have hyR : 81 * vinogradovChebyshevReservoirSize k ^ 2 ≤ vinogradovChebyshevBase N k := by
    show 81 * vinogradovChebyshevReservoirSize k ^ 2 ≤ vinogradovCeilRoot k N + k
    omega
  have hkr : k ≤ vinogradovCeilRoot k N := by omega
  have hr24 : 2 ^ 24 ≤ vinogradovCeilRoot k N := by omega
  have hb2 : b < k + b := by omega
  have hc2 : k - 2 + b < k + b := by omega
  have hidx : k - 2 + b = (k + b) - 2 := by omega
  obtain ⟨P, hP, hrec⟩ := exists_vinogradov_moment_chebyshev_recurrence hk0 hb hN hy24 hyR
  have hrecR : (Fintype.card (VinogradovDiagonalSolution N (k + b) k) : ℝ) ≤
      2 * ((vinogradovChebyshevReservoirSize k : ℝ) * ∑ i, ((P i : ℕ) : ℝ) ^ (2 * b) *
          ((N : ℝ) ^ k * ((k.factorial : ℝ) * ((P i : ℕ) : ℝ) ^ (k * (k - 1) / 2) *
            (Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ P i) b k) : ℝ))) +
        ((k * k - k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ 2 *
          (Fintype.card (VinogradovDiagonalSolution N (k - 2 + b) k) : ℝ)) := by
    exact_mod_cast hrec
  have hlb0 : 0 ≤ vinogradovDecayExponent k b :=
    le_trans (Nat.cast_nonneg _) (le_vinogradovDecayExponent hk b)
  have hlb2 : vinogradovDecayExponent k b ≤ 2 * b := vinogradovDecayExponent_le hk b
  have he0 : 0 ≤ 2 * b + (k * (k - 1) / 2 : ℝ) - vinogradovDecayExponent k b := by
    have : (0 : ℝ) ≤ k * (k - 1) / 2 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      positivity
    linarith
  have he_le : 2 * b + (k * (k - 1) / 2 : ℝ) - vinogradovDecayExponent k b ≤ (k * k : ℝ) := by
    have h2 := two_mul_sub_vinogradovDecayExponent_le (k := k) (by omega) b
    have hsum : (k * (k + 1) / 2 : ℝ) + k * (k - 1) / 2 = k * k := by ring
    linarith
  have hexp := vinogradovDecayExponent_good hk b
  have hterm : ∀ i, ((P i : ℕ) : ℝ) ^ (2 * b) *
        ((N : ℝ) ^ k * ((k.factorial : ℝ) * ((P i : ℕ) : ℝ) ^ (k * (k - 1) / 2) *
          (Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ P i) b k) : ℝ))) ≤
      (k.factorial : ℝ) * vinogradovExplicitConstant k b * (2 : ℝ) ^ (2 * b) *
        (16 : ℝ) ^ (k * k) * (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
    intro i
    obtain ⟨hpprime, _, hple⟩ := hP i
    have hM0 : N ⌈/⌉ P i ≠ 0 := ceilDiv_ne_zero_of_ne_zero hN hpprime.pos
    have hpN : P i ≤ N := le_of_le_four_base (by omega) hN hr24 hkr hple
    have hpM : P i * (N ⌈/⌉ P i) ≤ 2 * N := by
      rw [Nat.ceilDiv_eq_add_pred_div]
      calc P i * ((N + P i - 1) / P i) ≤ N + P i - 1 := Nat.mul_div_le _ _
        _ ≤ 2 * N := by omega
    exact vinogradov_good_term_le (by omega) hpprime.one_lt.le
      (Nat.one_le_iff_ne_zero.mpr hN) hpM (pow_le_sixteen_pow_mul_of_le_four_base hk0 hN hkr hple)
      (ih b hb2 _ hM0) (vinogradovExplicitConstant_pos k b).le hlb0 hlb2 rfl he0 he_le hexp
  have hsum : (vinogradovChebyshevReservoirSize k : ℝ) * ∑ i, ((P i : ℕ) : ℝ) ^ (2 * b) *
        ((N : ℝ) ^ k * ((k.factorial : ℝ) * ((P i : ℕ) : ℝ) ^ (k * (k - 1) / 2) *
          (Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ P i) b k) : ℝ))) ≤
      (vinogradovChebyshevReservoirSize k : ℝ) ^ 2 * (k.factorial : ℝ) *
        vinogradovExplicitConstant k b * (2 : ℝ) ^ (2 * b) *
        (16 : ℝ) ^ (k * k) * (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
    have h := Finset.sum_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin (vinogradovChebyshevReservoirSize k)))) =>
        hterm i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    calc _ ≤ (vinogradovChebyshevReservoirSize k : ℝ) *
          ((vinogradovChebyshevReservoirSize k : ℝ) *
            ((k.factorial : ℝ) * vinogradovExplicitConstant k b *
          (2 : ℝ) ^ (2 * b) * (16 : ℝ) ^ (k * k) *
          (N : ℝ) ^ vinogradovDecayExponent k (k + b))) :=
          mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
      _ = _ := by ring
  have hcoll : ((k * k - k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ 2 *
        (Fintype.card (VinogradovDiagonalSolution N (k - 2 + b) k) : ℝ) ≤
      ((k * k - k : ℕ) : ℝ) ^ 2 * vinogradovExplicitConstant k (k - 2 + b) *
        (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
    have hJ := ih (k - 2 + b) hc2 N hN
    have hcol := vinogradovDecayExponent_collision hk (s := k + b) (by omega)
    rw [← hidx] at hcol
    have hN2 : (N : ℝ) ^ 2 * (N : ℝ) ^ vinogradovDecayExponent k (k - 2 + b) ≤
        (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
    calc ((k * k - k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ 2 *
          (Fintype.card (VinogradovDiagonalSolution N (k - 2 + b) k) : ℝ)
        ≤ ((k * k - k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ 2 *
          (vinogradovExplicitConstant k (k - 2 + b) *
            (N : ℝ) ^ vinogradovDecayExponent k (k - 2 + b)) := by gcongr
      _ = ((k * k - k : ℕ) : ℝ) ^ 2 * vinogradovExplicitConstant k (k - 2 + b) *
          ((N : ℝ) ^ 2 * (N : ℝ) ^ vinogradovDecayExponent k (k - 2 + b)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hN2
          (mul_nonneg (by positivity) (vinogradovExplicitConstant_pos k _).le)
  have hgoodC := vinogradovExplicitConstant_good_le (k := k) (by omega) b
  have hcollC := vinogradovExplicitConstant_collision_le (k := k) (by omega) b
  have hpow0 : (0 : ℝ) ≤ (N : ℝ) ^ vinogradovDecayExponent k (k + b) :=
    Real.rpow_nonneg hN0.le _
  calc (Fintype.card (VinogradovDiagonalSolution N (k + b) k) : ℝ)
      ≤ 2 * ((vinogradovChebyshevReservoirSize k : ℝ) ^ 2 * (k.factorial : ℝ) *
            vinogradovExplicitConstant k b *
            (2 : ℝ) ^ (2 * b) * (16 : ℝ) ^ (k * k) * (N : ℝ) ^ vinogradovDecayExponent k (k + b) +
          ((k * k - k : ℕ) : ℝ) ^ 2 * vinogradovExplicitConstant k (k - 2 + b) *
            (N : ℝ) ^ vinogradovDecayExponent k (k + b)) := by
        refine hrecR.trans ?_
        gcongr
    _ = 2 * ((vinogradovChebyshevReservoirSize k : ℝ) ^ 2 * (k.factorial : ℝ) *
            vinogradovExplicitConstant k b *
            (2 : ℝ) ^ (2 * b) * (16 : ℝ) ^ (k * k) +
          ((k * k - k : ℕ) : ℝ) ^ 2 * vinogradovExplicitConstant k (k - 2 + b)) *
          (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by ring
    _ ≤ 2 * (vinogradovExplicitConstant k (k + b) / 4 + vinogradovExplicitConstant k (k + b) / 4) *
          (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by gcongr
    _ = vinogradovExplicitConstant k (k + b) * (N : ℝ) ^ vinogradovDecayExponent k (k + b) := by
        ring

end

end RHTower.Sieve
