import GaloisForLFunctions.ShortIntervalPrimesInProgressions.UniformZeroCounts
import GaloisForLFunctions.RHTower.DirichletLUniformZeroFreeRegion
import GaloisForLFunctions.RHTower.SiegelZeroFree

/-!
# The Siegel–Walfisz theorem in short windows

For every `A, B > 0` and `H ≥ 0`, uniformly over primitive nonprincipal characters `χ` of modulus
`N ≤ (log x)^B` and windows `x/(log x)^H ≤ h ≤ x`,

`|ψ(x + h, χ) − ψ(x, χ)| ≤ h/(log x)^A` for `x ≥ x₀(A, B, H)` (`siegelWalfisz_window`).

* Every zero `ρ = β + iγ` of `Λ(s, χ)` has `1 − β ≥ min(c/log²(N(|γ|+3)), c_ε N^{−ε})`
  (`one_sub_re_ge`): the corpus's uniform zero-free region away from real zeros of real characters,
  and Siegel's theorem at those (`ε = 1/(2B)`).
* The window bound of `CharacterSumsInShortWindows` with `h' = h/(log x)^{A+2}` and the uniform
  zero sum of `UniformZeroCounts` with `T ≍ (log x)^{4H+4A+12}`: the zeros below height `T` cost
  `exp(−c log x/(log log x)²) + exp(−c_ε √log x)` each, the zeros above cost `(log x)^{−A−4}`.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

/-- **The trivial window.** `ψ(b) − ψ(a) ≤ (b − a + 1) log b` for `1 ≤ a ≤ b`. -/
theorem psi_sub_le_trivial {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Chebyshev.psi b - Chebyshev.psi a ≤ (b - a + 1) * Real.log b := by
  have hb : 1 ≤ b := ha.trans hab
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hsplit : Chebyshev.psi b - Chebyshev.psi a
      = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi, Chebyshev.psi, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
    ring
  rw [hsplit]
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb
  calc ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n
      ≤ ∑ _n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, Real.log b := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 := (Finset.mem_Ioc.mp hn)
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos ?_)
        calc (n : ℝ) ≤ ⌊b⌋₊ := by exact_mod_cast hn1.2
          _ ≤ b := Nat.floor_le (by linarith)
    _ = ((⌊b⌋₊ - ⌊a⌋₊ : ℕ) : ℝ) * Real.log b := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ (b - a + 1) * Real.log b := by
        refine mul_le_mul_of_nonneg_right ?_ hlogb
        rw [Nat.cast_sub hfl]
        have h1 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (by linarith)
        have h2 : a < ⌊a⌋₊ + 1 := Nat.lt_floor_add_one a
        linarith

/-- `localCountConst N ≤ 20 (7 + log N)`. -/
theorem localCountConst_le {N : ℕ} (hN : 1 ≤ N) : localCountConst N ≤ 20 * (7 + Real.log N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : (1 : ℝ) / 20 ≤ Real.log ((39 / 20 : ℝ) / (37 / 20)) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < (39 / 20) / (37 / 20) by norm_num)
    norm_num at h ⊢
    linarith
  have h162 : Real.log 162 ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    calc (162 : ℝ) ≤ 2.7182818283 ^ 6 := by norm_num
      _ ≤ Real.exp 1 ^ 6 := by gcongr
      _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
  have hnum : 0 ≤ Real.log (162 * N) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 162 * N by linarith)
    linarith
  unfold localCountConst
  rw [div_le_iff₀ (by linarith), Real.log_mul (by norm_num) (by linarith)]
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  nlinarith

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- A zero of `Λ(s, χ)` is a zero of `L(s, χ)`. -/
theorem LFunction_point_eq_zero (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (q : LZero χ) :
    χ.LFunction q.point = 0 := by
  have h := completedLFunction_point hχ q
  rw [completedLFunction_eq_mul (zero_re_mem hχ hprim q).1] at h
  exact (mul_eq_zero.mp h).resolve_left (gammaFactor_ne_zero (zero_re_mem hχ hprim q).1)

/-- **Where the zeros are.** With `c` from the uniform zero-free region and `c_S` from Siegel's
theorem at `ε`, every zero has `1 − β ≥ min(c/log²(N(|γ|+3)), c_S N^{−ε})`. -/
theorem one_sub_re_ge {c cS ε : ℝ}
    (hc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ β γ : ℝ,
      χ.LFunction (β + γ * I) = 0 →
        (χ ^ 2 = 1 ∧ γ = 0) ∨ β ≤ 1 - c / Real.log ((q : ℝ) * (|γ| + 3)) ^ 2)
    (hS : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
      ∀ σ : ℝ, 1 - cS * (N : ℝ) ^ (-ε) < σ → χ.LFunction σ ≠ 0)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (q : LZero χ) :
    min (c / Real.log ((N : ℝ) * (|q.point.im| + 3)) ^ 2) (cS * (N : ℝ) ^ (-ε))
      ≤ 1 - q.point.re := by
  have hL := LFunction_point_eq_zero hχ hprim q
  have hpt : q.point = (q.point.re : ℂ) + q.point.im * I := (Complex.re_add_im _).symm
  rw [hpt] at hL
  rcases hc N χ hχ q.point.re q.point.im hL with ⟨hsq, hγ⟩ | hβ
  · have hreal : χ.LFunction (q.point.re : ℂ) = 0 := by
      rw [hγ] at hL
      simpa using hL
    have : ¬ (1 - cS * (N : ℝ) ^ (-ε) < q.point.re) := fun hlt => hS N χ hsq hχ _ hlt hreal
    push Not at this
    exact (min_le_right _ _).trans (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

/-! ### Asymptotics -/

/-- `(log x)^n ≤ δ x` eventually. -/
theorem eventually_log_pow_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ n ≤ δ * x := by
  have h := (isLittleO_log_rpow_rpow_atTop (n : ℝ) (zero_lt_one' ℝ)).bound hδ
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_natCast, Real.rpow_one,
    abs_of_nonneg (pow_nonneg hl n), abs_of_nonneg (by linarith)] at hx
  exact hx

/-- The rate `exp(−L min(c/log²(6L^{B+K}), c_S L^{−1/2}))` of the zeros below height `L^K`. -/
def swRate (c cS : ℝ) (B K : ℕ) (L : ℝ) : ℝ :=
  Real.exp (-(L * min (c / Real.log (6 * L ^ (B + K)) ^ 2) (cS * L ^ (-(1 / 2 : ℝ)))))

theorem swRate_pos (c cS : ℝ) (B K : ℕ) (L : ℝ) : 0 < swRate c cS B K L := Real.exp_pos _

/-- **The rate beats every power.** `L^M · swRate ≤ 1` eventually. -/
theorem eventually_pow_mul_swRate_le {c cS : ℝ} (hc : 0 < c) (hcS : 0 < cS) (B K M : ℕ) :
    ∀ᶠ L : ℝ in atTop, L ^ M * swRate c cS B K L ≤ 1 := by
  set D : ℝ := ((B + K + 1 : ℕ) : ℝ) with hD
  have hD1 : (1 : ℝ) ≤ D := by rw [hD]; exact_mod_cast Nat.succ_pos _
  have h3 := (eventually_log_pow_le 3 (δ := c / ((M + 1) * D ^ 2)) (by positivity))
  have hhalf := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).bound
    (c := cS / (M + 1)) (by positivity)
  filter_upwards [h3, hhalf, eventually_ge_atTop (6 : ℝ)] with L hL3 hLh hL6
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have hlog6 : Real.log 6 ≤ Real.log L := Real.log_le_log (by norm_num) hL6
  have hpos6 : 0 < 6 * L ^ (B + K) := by positivity
  have hlogbig : Real.log (6 * L ^ (B + K)) ≤ D * Real.log L := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hD]
    push_cast
    nlinarith
  have hlogbig0 : 0 < Real.log (6 * L ^ (B + K)) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have : 0 < Real.log 6 := Real.log_pos (by norm_num)
    have : 0 ≤ ((B + K : ℕ) : ℝ) * Real.log L := by positivity
    linarith
  -- the two halves of the minimum dominate `M log L`
  have ha : (M : ℝ) * Real.log L ≤ L * (c / Real.log (6 * L ^ (B + K)) ^ 2) := by
    have hsq : Real.log (6 * L ^ (B + K)) ^ 2 ≤ D ^ 2 * Real.log L ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hlogbig0.le hlogbig 2
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    have : (M : ℝ) * Real.log L * (D ^ 2 * Real.log L ^ 2) ≤ L * c := by
      have h' : Real.log L ^ 3 * ((M + 1) * D ^ 2) ≤ c * L := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hL3
        linarith
      nlinarith [pow_pos hlogL 3, sq_nonneg D]
    calc (M : ℝ) * Real.log L * Real.log (6 * L ^ (B + K)) ^ 2
        ≤ (M : ℝ) * Real.log L * (D ^ 2 * Real.log L ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ L * c := this
  have hb : (M : ℝ) * Real.log L ≤ L * (cS * L ^ (-(1 / 2 : ℝ))) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogL,
      abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hLh
    have hsqrt : L * L ^ (-(1 / 2 : ℝ)) = L ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' hL0.le (by norm_num)]
      norm_num
    have : L * (cS * L ^ (-(1 / 2 : ℝ))) = cS * L ^ (1 / 2 : ℝ) := by
      rw [← hsqrt]; ring
    rw [this]
    have hrp : 0 < L ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hL0 _
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hLh
    nlinarith
  have hmin : (M : ℝ) * Real.log L ≤ L * min (c / Real.log (6 * L ^ (B + K)) ^ 2)
      (cS * L ^ (-(1 / 2 : ℝ))) := by
    rw [mul_min_of_nonneg _ _ hL0.le]
    exact le_min ha hb
  rw [swRate, ← Real.exp_log (pow_pos hL0 M), Real.log_pow, ← Real.exp_add]
  rw [Real.exp_le_one_iff]
  linarith

/-- The eventual inequalities of the Siegel–Walfisz window, as conditions on `x` alone. -/
theorem eventually_sw_conditions {c cS : ℝ} (hc : 0 < c) (hcS : 0 < cS) (A B H K : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ 2 ≤ Real.log x ∧ 30 * (Real.log x + 1) ≤ Real.log x ^ 2 ∧
      30 * (Real.log x + 1) * Real.log x ^ (A + H) ≤ x ∧
      480 * (7 + B * Real.log x) * (2 + K * Real.log x) * Real.log x ^ (K + A)
        * swRate c cS B K (Real.log x) ≤ 1 / 5 ∧
      51200 * (7 + B * Real.log x) ≤ Real.log x ^ 4 ∧
      180 * (Real.log x + 2) * Real.log x ^ (A + H) ≤ x ∧
      180 * Real.log x ^ (2 * A + 2 + 2 * H) ≤ x ^ 2 := by
  have hlog := Real.tendsto_log_atTop
  set L₀ : ℝ := 31 + 51200 * (7 + B) + 480 * (7 + B) * (2 + K) with hL₀
  have hpoly := hlog.eventually (eventually_ge_atTop L₀)
  have hrate := hlog.eventually (eventually_pow_mul_swRate_le hc hcS B K (K + A + 4))
  have hx1 := eventually_log_pow_le (A + H + 1) (δ := 1 / 540) (by norm_num)
  have hx2 := eventually_log_pow_le (2 * A + 2 + 2 * H) (δ := 1 / 180) (by norm_num)
  filter_upwards [hpoly, hrate, hx1, hx2, eventually_ge_atTop (2 : ℝ)] with x hL hR h1 h2 hx
  set L := Real.log x with hLdef
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hLbig : 31 ≤ L := by
    have : 0 ≤ 51200 * (7 + (B : ℝ)) + 480 * (7 + B) * (2 + K) := by positivity
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hpowAH : L ^ (A + H) * L = L ^ (A + H + 1) := by ring
  refine ⟨hx, by linarith, by nlinarith, ?_, ?_, ?_, ?_, ?_⟩
  · have : 30 * (L + 1) * L ^ (A + H) ≤ 60 * L ^ (A + H + 1) := by
      rw [← hpowAH]
      have : 0 < L ^ (A + H) := by positivity
      nlinarith
    linarith
  · -- the rate
    have hq : 480 * (7 + B * L) * (2 + K * L) ≤ L ^ 3 := by
      have hM : 480 * (7 + (B : ℝ)) * (2 + K) ≤ L := by
        have : 0 ≤ 31 + 51200 * (7 + (B : ℝ)) := by positivity
        linarith
      have e1 : 7 + B * L ≤ (7 + B) * L := by nlinarith
      have e2 : 2 + K * L ≤ (2 + K) * L := by nlinarith
      calc 480 * (7 + B * L) * (2 + K * L) ≤ 480 * ((7 + B) * L) * ((2 + K) * L) := by
            gcongr
        _ = (480 * (7 + B) * (2 + K)) * L ^ 2 := by ring
        _ ≤ L * L ^ 2 := by gcongr
        _ = L ^ 3 := by ring
    have hrpos := swRate_pos c cS B K L
    calc 480 * (7 + B * L) * (2 + K * L) * L ^ (K + A) * swRate c cS B K L
        ≤ L ^ 3 * L ^ (K + A) * swRate c cS B K L := by gcongr
      _ = (L ^ (K + A + 4) * swRate c cS B K L) / L := by
          field_simp
          ring
      _ ≤ 1 / L := div_le_div_of_nonneg_right hR hL0.le
      _ ≤ 1 / 5 := div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
  · have hM : 51200 * (7 + (B : ℝ)) ≤ L := by
      have : 0 ≤ 31 + 480 * (7 + (B : ℝ)) * (2 + K) := by positivity
      linarith
    have e1 : 7 + B * L ≤ (7 + B) * L := by nlinarith
    calc 51200 * (7 + B * L) ≤ 51200 * ((7 + B) * L) := by gcongr
      _ = (51200 * (7 + B)) * L := by ring
      _ ≤ L * L := by gcongr
      _ ≤ L ^ 4 := by nlinarith [pow_le_pow_right₀ hL1 (show 2 ≤ 4 by norm_num)]
  · have : 180 * (L + 2) * L ^ (A + H) ≤ 540 * L ^ (A + H + 1) := by
      rw [← hpowAH]
      have : 0 < L ^ (A + H) := by positivity
      nlinarith
    linarith
  · have hxx : x ≤ x ^ 2 := by nlinarith
    linarith

section Window

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **The zeros below height `L^K`.** -/
theorem rpow_re_sub_one_le_swRate {c cS : ℝ} (hc0 : 0 < c) (hcS0 : 0 < cS) {B K : ℕ}
    (hB : 1 ≤ B)
    (hc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ β γ : ℝ,
      χ.LFunction (β + γ * I) = 0 →
        (χ ^ 2 = 1 ∧ γ = 0) ∨ β ≤ 1 - c / Real.log ((q : ℝ) * (|γ| + 3)) ^ 2)
    (hS : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
      ∀ σ : ℝ, 1 - cS * (N : ℝ) ^ (-(1 / (2 * B) : ℝ)) < σ → χ.LFunction σ ≠ 0)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {x : ℝ} (hxpos : 0 < x) (hL1 : 1 ≤ Real.log x)
    (hN : (N : ℝ) ≤ Real.log x ^ B) {T : ℕ} (hTle : (T : ℝ) ≤ Real.log x ^ K + 1)
    (q : LZero χ) (hq : |q.point.im| ≤ T + 1) :
    x ^ (q.point.re - 1) ≤ swRate c cS B K (Real.log x) := by
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hLK1 : 1 ≤ L ^ K := one_le_pow₀ hL1
  have hz := one_sub_re_ge (c := c) (cS := cS) (ε := 1 / (2 * B)) hc hS hχ hprim q
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hcond : (N : ℝ) * (|q.point.im| + 3) ≤ 6 * L ^ (B + K) := by
    have h1 : |q.point.im| + 3 ≤ L ^ K + 5 := by linarith
    have h2 : L ^ K + 5 ≤ 6 * L ^ K := by linarith
    calc (N : ℝ) * (|q.point.im| + 3) ≤ L ^ B * (6 * L ^ K) :=
          mul_le_mul hN (h1.trans h2) (by positivity) (by positivity)
      _ = 6 * L ^ (B + K) := by ring
  have hcond3 : 3 ≤ (N : ℝ) * (|q.point.im| + 3) := by
    nlinarith [abs_nonneg q.point.im]
  have hlog1 : 0 < Real.log ((N : ℝ) * (|q.point.im| + 3)) := Real.log_pos (by linarith)
  have hlogle : Real.log ((N : ℝ) * (|q.point.im| + 3)) ≤ Real.log (6 * L ^ (B + K)) :=
    Real.log_le_log (by linarith) hcond
  have hm1 : c / Real.log (6 * L ^ (B + K)) ^ 2
      ≤ c / Real.log ((N : ℝ) * (|q.point.im| + 3)) ^ 2 :=
    div_le_div_of_nonneg_left hc0.le (by positivity) (pow_le_pow_left₀ hlog1.le hlogle 2)
  have hm2 : cS * L ^ (-(1 / 2 : ℝ)) ≤ cS * (N : ℝ) ^ (-(1 / (2 * B) : ℝ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hcS0.le
    have hNL : (L ^ B) ^ (-(1 / (2 * B) : ℝ)) ≤ (N : ℝ) ^ (-(1 / (2 * B) : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hN (by
        have : 0 ≤ 1 / (2 * (B : ℝ)) := by positivity
        linarith)
    have hpow : (L ^ B) ^ (-(1 / (2 * B) : ℝ)) = L ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1
      field_simp
    linarith
  have hmin : min (c / Real.log (6 * L ^ (B + K)) ^ 2) (cS * L ^ (-(1 / 2 : ℝ)))
      ≤ 1 - q.point.re := (min_le_min hm1 hm2).trans hz
  rw [Real.rpow_def_of_pos hxpos, swRate]
  refine Real.exp_le_exp.mpr ?_
  rw [← hLdef]
  have := mul_le_mul_of_nonneg_left hmin hL0.le
  linarith

end Window

/-- The zero sum of the window, in arithmetic form. -/
theorem zeroSum_le_of_bounds {Z C T' LT E Y' L : ℝ} {A B K : ℕ} (hL1 : 1 ≤ L)
    (hZ : Z ≤ 4 * C * (T' * LT * E + Y')) (hC : C ≤ 20 * (7 + B * L))
    (hTL : T' * LT ≤ 3 * L ^ K * (2 + K * L)) (hY : Y' ≤ 64 / L ^ (A + 4)) (hE0 : 0 ≤ E)
    (hin0 : 0 ≤ T' * LT * E + Y')
    (hC4 : 480 * (7 + B * L) * (2 + K * L) * L ^ (K + A) * E ≤ 1 / 5)
    (hC5 : 51200 * (7 + B * L) ≤ L ^ 4) :
    Z ≤ 1 / (5 * L ^ A) := by
  have hL0 : 0 < L := by linarith
  have hLA : 0 < L ^ A := by positivity
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : Z ≤ 4 * (20 * (7 + B * L)) * (3 * L ^ K * (2 + K * L) * E + 64 / L ^ (A + 4)) := by
    refine hZ.trans ?_
    have hin : T' * LT * E + Y' ≤ 3 * L ^ K * (2 + K * L) * E + 64 / L ^ (A + 4) :=
      add_le_add (mul_le_mul_of_nonneg_right hTL hE0) hY
    calc 4 * C * (T' * LT * E + Y') ≤ 4 * (20 * (7 + B * L)) * (T' * LT * E + Y') :=
          mul_le_mul_of_nonneg_right (by linarith) hin0
      _ ≤ _ := mul_le_mul_of_nonneg_left hin (by positivity)
  have hr1 : 4 * (20 * (7 + B * L)) * (3 * L ^ K * (2 + K * L) * E) ≤ 1 / (10 * L ^ A) := by
    rw [le_div_iff₀ (by positivity)]
    have e : 4 * (20 * (7 + B * L)) * (3 * L ^ K * (2 + K * L) * E) * (10 * L ^ A)
        = 5 * (480 * (7 + B * L) * (2 + K * L) * L ^ (K + A) * E) := by ring
    rw [e]
    linarith
  have hr2 : 4 * (20 * (7 + B * L)) * (64 / L ^ (A + 4)) ≤ 1 / (10 * L ^ A) := by
    rw [show 4 * (20 * (7 + B * L)) * (64 / L ^ (A + 4)) = 5120 * (7 + B * L) / L ^ (A + 4)
      by ring, div_le_div_iff₀ (by positivity) (by positivity)]
    have e : L ^ (A + 4) = L ^ A * L ^ 4 := by ring
    rw [e]
    nlinarith
  have : 1 / (10 * L ^ A) + 1 / (10 * L ^ A) = 1 / (5 * L ^ A) := by
    field_simp; ring
  nlinarith

/-- The window, in arithmetic form. -/
theorem window_le_of_bounds {W P1 P2 Z lg x h h' L : ℝ} {A H : ℕ} (hL1 : 1 ≤ L)
    (hhpos : 0 < h) (hh' : h' = h / L ^ (A + 2)) (hxh : x ≤ h * L ^ H)
    (hWb : W ≤ P1 + 2 * P2 + 2 * h * Z + 18 * (1 + lg) + 18 / h')
    (hP1 : P1 ≤ (h' + 1) * (L + 1)) (hP2 : P2 ≤ (h' + 1) * (L + 1)) (hZ : Z ≤ 1 / (5 * L ^ A))
    (hlg : lg ≤ L + 1) (hL30 : 30 * (L + 1) ≤ L ^ 2)
    (hC3 : 30 * (L + 1) * L ^ (A + H) ≤ x) (hC6 : 180 * (L + 2) * L ^ (A + H) ≤ x)
    (hC7 : 180 * L ^ (2 * A + 2 + 2 * H) ≤ x ^ 2) (hxpos : 0 < x) :
    W ≤ h / L ^ A := by
  have hL0 : 0 < L := by linarith
  have hLA : 0 < L ^ A := by positivity
  have hLH : 0 < L ^ H := by positivity
  set u := h / L ^ A with hu
  have hupos : 0 < u := by positivity
  have hS1 : P1 + 2 * P2 ≤ u / 5 := by
    have h1 : 3 * (h' * (L + 1)) ≤ u / 10 := by
      rw [hh', hu, show h / L ^ (A + 2) * (L + 1) = h / L ^ A * ((L + 1) / L ^ 2) by
        field_simp; ring]
      have : (L + 1) / L ^ 2 ≤ 1 / 30 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have hhA : 0 < h / L ^ A := by positivity
      nlinarith
    have h2 : 3 * (L + 1) ≤ u / 10 := by
      rw [hu, le_div_iff₀ (by norm_num), le_div_iff₀ hLA]
      have : 30 * (L + 1) * L ^ (A + H) ≤ h * L ^ H * L ^ A := by
        calc 30 * (L + 1) * L ^ (A + H) ≤ x := hC3
          _ ≤ h * L ^ H := hxh
          _ ≤ h * L ^ H * L ^ A := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
      have e : 30 * (L + 1) * L ^ (A + H) = 3 * (L + 1) * L ^ A * 10 * L ^ H := by ring
      rw [e] at this
      nlinarith
    nlinarith
  have hS2 : 2 * h * Z ≤ 2 * u / 5 := by
    calc 2 * h * Z ≤ 2 * h * (1 / (5 * L ^ A)) := mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = 2 * u / 5 := by rw [hu]; field_simp
  have hS3 : 18 * (1 + lg) ≤ u / 10 := by
    have : 18 * (1 + lg) ≤ 18 * (L + 2) := by linarith
    refine this.trans ?_
    rw [hu, le_div_iff₀ (by norm_num), le_div_iff₀ hLA]
    have h1 : 180 * (L + 2) * L ^ (A + H) ≤ h * L ^ H := hC6.trans hxh
    have e : 180 * (L + 2) * L ^ (A + H) = 18 * (L + 2) * 10 * L ^ A * L ^ H := by ring
    rw [e] at h1
    nlinarith
  have hS4 : 18 / h' ≤ u / 10 := by
    have hhsq : x ^ 2 ≤ h ^ 2 * L ^ (2 * H) := by
      calc x ^ 2 ≤ (h * L ^ H) ^ 2 := pow_le_pow_left₀ hxpos.le hxh 2
        _ = h ^ 2 * L ^ (2 * H) := by ring
    have h1 : 180 * L ^ (2 * A + 2 + 2 * H) ≤ h ^ 2 * L ^ (2 * H) := hC7.trans hhsq
    have e : L ^ (2 * A + 2 + 2 * H) = L ^ (2 * A + 2) * L ^ (2 * H) := by ring
    rw [e] at h1
    have hLH2 : 0 < L ^ (2 * H) := by positivity
    have h2 : 180 * L ^ (2 * A + 2) ≤ h ^ 2 := by nlinarith
    rw [hh', hu, div_div_eq_mul_div, div_div, div_le_div_iff₀ hhpos (by positivity)]
    have e2 : 18 * L ^ (A + 2) * (L ^ A * 10) = 180 * L ^ (2 * A + 2) := by ring
    rw [e2]
    nlinarith
  linarith

theorem log_five_le_two : Real.log 5 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := Real.exp_one_gt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith

/-- The height `T = ⌈L^K⌉`. -/
theorem ceil_pow_bounds {L : ℝ} (hL1 : 1 ≤ L) (K : ℕ) :
    L ^ K ≤ (⌈L ^ K⌉₊ : ℝ) ∧ (⌈L ^ K⌉₊ : ℝ) ≤ L ^ K + 1 ∧ 1 ≤ ⌈L ^ K⌉₊ := by
  have hLK1 : 1 ≤ L ^ K := one_le_pow₀ hL1
  have hge : L ^ K ≤ (⌈L ^ K⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨hge, (Nat.ceil_lt_add_one (by positivity)).le, ?_⟩
  have : (1 : ℝ) ≤ ⌈L ^ K⌉₊ := hLK1.trans hge
  exact_mod_cast this

/-- `(T + 1) log(T + 3) ≤ 3L^K(2 + KL)` for `T ≤ L^K + 1`. -/
theorem height_log_le {L T : ℝ} (hL1 : 1 ≤ L) (K : ℕ) (hT0 : 0 ≤ T) (hTle : T ≤ L ^ K + 1) :
    (T + 1) * Real.log (T + 3) ≤ 3 * L ^ K * (2 + K * L) := by
  have hL0 : 0 < L := by linarith
  have hLK1 : 1 ≤ L ^ K := one_le_pow₀ hL1
  have hlog3 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have h1 : T + 1 ≤ 3 * L ^ K := by linarith
  have h2 : Real.log (T + 3) ≤ 2 + K * L := by
    have : T + 3 ≤ 5 * L ^ K := by linarith
    calc Real.log (T + 3) ≤ Real.log (5 * L ^ K) := Real.log_le_log (by positivity) this
      _ = Real.log 5 + K * Real.log L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      _ ≤ 2 + K * L := by
          have := Real.log_le_sub_one_of_pos hL0
          have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
          have := log_five_le_two
          nlinarith
  calc (T + 1) * Real.log (T + 3) ≤ 3 * L ^ K * Real.log (T + 3) :=
        mul_le_mul_of_nonneg_right h1 hlog3
    _ ≤ 3 * L ^ K * (2 + K * L) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `8Y/√T ≤ 64/L^{A+4}` for `Y = 8x²/(h·h/L^{A+2})`, `x ≤ hL^H`, `T ≥ L^{2(2H+2A+6)}`. -/
theorem weight_over_sqrt_le {x h L T : ℝ} {A H : ℕ} (hxpos : 0 < x) (hhpos : 0 < h)
    (hL1 : 1 ≤ L) (hxh : x ≤ h * L ^ H) (hT : L ^ (2 * (2 * H + 2 * A + 6)) ≤ T) :
    8 * (8 * x ^ 2 / (h * (h / L ^ (A + 2)))) / Real.sqrt T ≤ 64 / L ^ (A + 4) := by
  have hL0 : 0 < L := by linarith
  have hYb : 8 * x ^ 2 / (h * (h / L ^ (A + 2))) ≤ 8 * L ^ (2 * H + A + 2) := by
    rw [div_le_iff₀ (by positivity)]
    have hx2' : x ^ 2 ≤ h ^ 2 * L ^ (2 * H) := by
      calc x ^ 2 ≤ (h * L ^ H) ^ 2 := pow_le_pow_left₀ hxpos.le hxh 2
        _ = h ^ 2 * L ^ (2 * H) := by ring
    have : 8 * L ^ (2 * H + A + 2) * (h * (h / L ^ (A + 2))) = 8 * (h ^ 2 * L ^ (2 * H)) := by
      field_simp
      ring
    rw [this]
    linarith
  have hsqrtT : L ^ (2 * H + 2 * A + 6) ≤ Real.sqrt T := by
    rw [Real.le_sqrt (by positivity) (le_trans (by positivity) hT)]
    calc (L ^ (2 * H + 2 * A + 6)) ^ 2 = L ^ (2 * (2 * H + 2 * A + 6)) := by ring
      _ ≤ T := hT
  have hsq0 : 0 < Real.sqrt T := lt_of_lt_of_le (by positivity) hsqrtT
  rw [div_le_div_iff₀ hsq0 (by positivity)]
  calc 8 * (8 * x ^ 2 / (h * (h / L ^ (A + 2)))) * L ^ (A + 4)
      ≤ 8 * (8 * L ^ (2 * H + A + 2)) * L ^ (A + 4) := by gcongr
    _ = 64 * L ^ (2 * H + 2 * A + 6) := by ring
    _ ≤ 64 * Real.sqrt T := by gcongr

/-- The trivial windows of the squeeze. -/
theorem psi_windows_le {x h h' : ℝ} (hx : 2 ≤ x) (hh' : 0 < h') (hh'h : 2 * h' ≤ h)
    (hhx : h ≤ x) :
    Chebyshev.psi (x + h') - Chebyshev.psi x ≤ (h' + 1) * (Real.log x + 1) ∧
      Chebyshev.psi (x + h) - Chebyshev.psi (x + h - h') ≤ (h' + 1) * (Real.log x + 1) := by
  have hxpos : 0 < x := by linarith
  have hlog2x : Real.log (2 * x) ≤ Real.log x + 1 := by
    rw [Real.log_mul (by norm_num) hxpos.ne']
    have := Real.log_two_lt_d9
    linarith
  constructor
  · have h1 := psi_sub_le_trivial (a := x) (b := x + h') (by linarith) (by linarith)
    have hl : Real.log (x + h') ≤ Real.log x + 1 :=
      (Real.log_le_log (by linarith) (by linarith)).trans hlog2x
    rw [show x + h' - x + 1 = h' + 1 by ring] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hl (by linarith))
  · have h1 := psi_sub_le_trivial (a := x + h - h') (b := x + h) (by linarith) (by linarith)
    have hl : Real.log (x + h) ≤ Real.log x + 1 :=
      (Real.log_le_log (by linarith) (by linarith)).trans hlog2x
    rw [show x + h - (x + h - h') + 1 = h' + 1 by ring] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hl (by linarith))

theorem localCountConst_le_poly {N B : ℕ} (hN1 : 1 ≤ N) {L : ℝ} (hL1 : 1 ≤ L)
    (hN : (N : ℝ) ≤ L ^ B) : localCountConst N ≤ 20 * (7 + B * L) := by
  have h1 := localCountConst_le hN1
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have h2 : Real.log N ≤ B * L := by
    calc Real.log N ≤ Real.log (L ^ B) := Real.log_le_log hN0 hN
      _ = B * Real.log L := Real.log_pow _ _
      _ ≤ B * L := by
          have := Real.log_le_sub_one_of_pos hL0
          have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
          nlinarith
  linarith

/-- **Siegel–Walfisz in short windows.** For `A, H ∈ ℕ` and `B ≥ 1` there is `x₀` such that for
`x ≥ x₀`, every primitive nonprincipal `χ` of modulus `N ≤ (log x)^B` and every
`x/(log x)^H ≤ h ≤ x`: `|ψ(x + h, χ) − ψ(x, χ)| ≤ h/(log x)^A`. -/
theorem siegelWalfisz_window (A B H : ℕ) (hB : 1 ≤ B) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      χ.IsPrimitive → (N : ℝ) ≤ Real.log x ^ B → ∀ h : ℝ, x / Real.log x ^ H ≤ h → h ≤ x →
        ‖psiChi χ (x + h) - psiChi χ x‖ ≤ h / Real.log x ^ A := by
  obtain ⟨c, hc0, hc⟩ := RHTower.uniform_zero_free_region
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  obtain ⟨cS, hcS0, hS⟩ := RHTower.siegel_zero_free (ε := 1 / (2 * B)) (by positivity)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (eventually_sw_conditions hc0 hcS0 A B H (2 * (2 * H + 2 * A + 6)))
  refine ⟨x₀, fun x hx N _ χ hχ hprim hN h hh1 hh2 => ?_⟩
  obtain ⟨hx2, hL2, hL30, hC3, hC4, hC5, hC6, hC7⟩ := hx₀ x hx
  have hxpos : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  have hLH : 0 < Real.log x ^ H := by positivity
  have hhpos : 0 < h := lt_of_lt_of_le (by positivity) hh1
  have hxh : x ≤ h * Real.log x ^ H := by rwa [div_le_iff₀ hLH] at hh1
  have hLA2 : 2 ≤ Real.log x ^ (A + 2) :=
    hL2.trans ((pow_one _).symm.le.trans (pow_le_pow_right₀ hL1 (by omega)))
  have hh'pos : 0 < h / Real.log x ^ (A + 2) := by positivity
  have hh'h : 2 * (h / Real.log x ^ (A + 2)) ≤ h := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨hTge, hTle, hT1⟩ := ceil_pow_bounds hL1 (2 * (2 * H + 2 * A + 6))
  have hE0 := (swRate_pos c cS B (2 * (2 * H + 2 * A + 6)) (Real.log x)).le
  have hZ := tsum_zeroShortWeight_le_uniform hχ hprim (x := x)
    (Y := 8 * x ^ 2 / (h * (h / Real.log x ^ (A + 2))))
    (E := swRate c cS B (2 * (2 * H + 2 * A + 6)) (Real.log x)) (by linarith) (by positivity) hE0
    hT1 fun q hq => rpow_re_sub_one_le_swRate hc0 hcS0 hB hc hS hχ hprim hxpos hL1 hN hTle q hq
  have hW := norm_psiChi_window_le_uniform hχ hprim hx2 hh'pos hh'h hh2
  obtain ⟨hP1, hP2⟩ := psi_windows_le hx2 hh'pos hh'h hh2
  have hlog2x : Real.log (2 * x) ≤ Real.log x + 1 := by
    rw [Real.log_mul (by norm_num) hxpos.ne']
    have := Real.log_two_lt_d9
    linarith
  have hZ' := zeroSum_le_of_bounds (A := A) (B := B) (K := 2 * (2 * H + 2 * A + 6)) hL1 hZ
    (localCountConst_le_poly (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) hL1 hN)
    (height_log_le hL1 _ (Nat.cast_nonneg _) hTle)
    (weight_over_sqrt_le hxpos hhpos hL1 hxh hTge) hE0
    (by have := Real.log_nonneg (show (1 : ℝ) ≤ (⌈Real.log x ^ (2 * (2 * H + 2 * A + 6))⌉₊ : ℝ)
          + 3 by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (⌈Real.log x ^ (2 * (2 * H + 2 * A + 6))⌉₊ : ℝ))])
        positivity) hC4 hC5
  exact window_le_of_bounds hL1 hhpos rfl hxh hW hP1 hP2 hZ' hlog2x hL30 hC3 hC6 hC7 hxpos

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
