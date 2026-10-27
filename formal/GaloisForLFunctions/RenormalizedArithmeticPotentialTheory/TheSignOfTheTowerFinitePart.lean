import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsTheTowerForm
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheTowerFormOfAPrime
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The sign of the tower finite part

On the `p`-adic valuation classes the finite part of the horizon renormalization is the tower form
of `p` (`TheFinitePartIsTheTowerForm`). In normalized class coordinates `b_j` it enters Weil's form
with the sign of the prime sum reversed:

    F_p(b) = 2γ_p |b|² + log p (|b|² − K_q(b)),   q = p^{−1/2},   γ_p = γ + log p/(p − 1)

(`towerFinitePart`), where `K_q` is the Kac–Murdock–Szegő form (AIT). This file decides its sign.

* **The tower deficit** (`towerDeficit`, `localEuler_sub_eq`):
  `γ_p − log p · q/(1 − q) = −d_p` with `d_p = √p log p/(p − 1) − γ`.
* **Lower bound** (`towerFinitePart_ge`): `F_p(b) ≥ −2 d_p |b|²` on every depth, from the
  Kac–Murdock–Szegő bound `K_q ≤ (1 + q)/(1 − q)`.
* **The uniform class profile is extremal** (`kmsForm_one`, `towerFinitePart_one`):
  `F_p(1_N) = −2N d_p + 2q log p (1 − q^N)/(1 − q)²`.
* **The sign law** (`towerFinitePart_add_nonneg_iff`, `towerFinitePart_nonneg_iff`):
  `F_p + c |·|² ≥ 0` on every depth iff `c ≥ 2 d_p`. So the prime finite part is nonnegative on all
  classes of `p` iff `√p log p ≤ γ (p − 1)`, and otherwise another place must pay exactly `2 d_p`.
* **Small and large primes** (`towerDeficit_two_pos`, `towerDeficit_nonpos`): `d_2 > 0`, and
  `d_p ≤ 0` for `p ≥ 2^16`. (Numerically `d_p ≤ 0` exactly for `p ≥ 47`.)

The sign of the prime finite part is local at each prime and decided by one number: Euler's
constant against `√p log p/(p − 1)`, the top of the tower form of `p`. At large primes the prime
place pays for its own classes; at the small primes the deficit `2 d_p` is what the archimedean and
polar places must supply.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticIntersectionTheory

local notation "γ" => Real.eulerMascheroniConstant

variable {p : ℕ}

/-- The **tower deficit** `d_p = √p log p/(p − 1) − γ`. -/
def towerDeficit (p : ℕ) : ℝ := Real.sqrt p * Real.log p / ((p : ℝ) - 1) - γ

/-- The **tower finite part** on the first `N` classes of `p` in normalized coordinates, as it
enters Weil's form: `2γ_p |b|² + log p (|b|² − K_q(b))`, `q = p^{−1/2}`. -/
def towerFinitePart (p N : ℕ) (b : ℕ → ℝ) : ℝ :=
  2 * localEuler p * ∑ j ∈ range N, b j ^ 2 +
    Real.log p * (∑ j ∈ range N, b j ^ 2 - kmsForm (1 / Real.sqrt p) N b)

theorem localEuler_sub_eq_aux (g L s : ℝ) (hs : 1 < s) :
    g + L / (s ^ 2 - 1) - L * (1 / s / (1 - 1 / s)) = -(s * L / (s ^ 2 - 1) - g) := by
  have h1 : s - 1 ≠ 0 := by linarith
  have h2 : s ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : s ≠ 0 := by linarith
  field_simp
  ring

/-- `γ_p − log p · q/(1 − q) = −d_p` for `q = p^{−1/2}`. -/
theorem localEuler_sub_eq (hp : p.Prime) :
    localEuler p - Real.log p * (1 / Real.sqrt p / (1 - 1 / Real.sqrt p)) = -towerDeficit p := by
  have hs1 : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast hp.one_lt)
  unfold localEuler towerDeficit
  rw [show (p : ℝ) - 1 = Real.sqrt p ^ 2 - 1 by rw [Real.sq_sqrt (Nat.cast_nonneg _)]]
  exact localEuler_sub_eq_aux _ _ _ hs1

/-- **Lower bound**: `F_p(b) ≥ −2 d_p |b|²` on every depth. -/
theorem towerFinitePart_ge (hp : p.Prime) (N : ℕ) (b : ℕ → ℝ) :
    -2 * towerDeficit p * ∑ j ∈ range N, b j ^ 2 ≤ towerFinitePart p N b := by
  have hE := localEuler_sub_eq hp
  unfold towerFinitePart
  set q := 1 / Real.sqrt p
  have hq0 : 0 ≤ q := inv_sqrt_prime_nonneg p
  have hq1 : q < 1 := inv_sqrt_prime_lt_one hp
  have hK := kmsForm_upper hq0 hq1.le N b
  set S := ∑ j ∈ range N, b j ^ 2
  have hL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  -- `K_q ≤ (1 + q)/(1 − q) |b|²`, so `|b|² − K_q ≥ −(2q/(1 − q)) |b|²`
  have hK' : S - kmsForm q N b ≥ -2 * (q / (1 - q)) * S := by
    have h : -2 * (q / (1 - q)) * S = S - (1 + q) / (1 - q) * S := by
      field_simp [(by linarith : (1 : ℝ) - q ≠ 0)]
      ring
    rw [h, ge_iff_le, sub_le_sub_iff_left, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    linarith
  have h1 := mul_le_mul_of_nonneg_left hK' hL
  have hd : towerDeficit p = -(localEuler p - Real.log p * (q / (1 - q))) := by rw [hE]; ring
  rw [hd]
  linarith

/-- `Σ_{i < N} q^{N − i} = q(1 − q^N)/(1 − q)`. -/
theorem sum_range_pow_sub {q : ℝ} (hq : q ≠ 1) (N : ℕ) :
    ∑ i ∈ range N, q ^ (N - i) = q * (1 - q ^ N) / (1 - q) := by
  have h : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  induction N with
  | zero => simp
  | succ N ih =>
    have hshift : ∑ i ∈ range N, q ^ (N + 1 - i) = q * ∑ i ∈ range N, q ^ (N - i) := by
      rw [mul_sum]
      exact sum_congr rfl fun i hi => by
        rw [show N + 1 - i = N - i + 1 by have := mem_range.mp hi; omega, pow_succ]; ring
    rw [Finset.sum_range_succ, hshift, ih, Nat.add_sub_cancel_left, pow_one]
    field_simp
    ring

/-- One more class adds its diagonal and its couplings to the lower classes. -/
theorem kmsForm_one_succ (q : ℝ) (N : ℕ) :
    kmsForm q (N + 1) (fun _ => 1) =
      kmsForm q N (fun _ => 1) + 1 + 2 * ∑ i ∈ range N, q ^ (N - i) := by
  have e1 : ∑ i ∈ range N, kmsEntry q i N = ∑ i ∈ range N, q ^ (N - i) :=
    sum_congr rfl fun i hi => by
      have h := (mem_range.mp hi).le
      simp [kmsEntry, max_eq_right h, min_eq_left h]
  have e2 : ∑ j ∈ range N, kmsEntry q N j = ∑ i ∈ range N, q ^ (N - i) :=
    sum_congr rfl fun j hj => by
      have h := (mem_range.mp hj).le
      simp [kmsEntry, max_eq_left h, min_eq_right h]
  unfold kmsForm
  simp only [Finset.sum_range_succ, sum_add_distrib, one_mul, mul_one, e1, e2, kmsEntry_self]
  ring

/-- **The tower form on the uniform profile**:
`K_q(1_N) = N(1 + q)/(1 − q) − 2q(1 − q^N)/(1 − q)²`. -/
theorem kmsForm_one {q : ℝ} (hq : q ≠ 1) (N : ℕ) :
    kmsForm q N (fun _ => 1) = N * (1 + q) / (1 - q) - 2 * q * (1 - q ^ N) / (1 - q) ^ 2 := by
  have h : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  induction N with
  | zero => simp [kmsForm]
  | succ N ih =>
    rw [kmsForm_one_succ, ih, sum_range_pow_sub hq]
    push_cast
    field_simp
    ring

/-- **The uniform class profile is extremal**:
`F_p(1_N) = −2N d_p + 2q log p (1 − q^N)/(1 − q)²`. -/
theorem towerFinitePart_one (hp : p.Prime) (N : ℕ) :
    towerFinitePart p N (fun _ => 1) = -2 * N * towerDeficit p +
      2 * (1 / Real.sqrt p) * Real.log p * (1 - (1 / Real.sqrt p) ^ N) /
        (1 - 1 / Real.sqrt p) ^ 2 := by
  have hE := localEuler_sub_eq hp
  have hq1 := inv_sqrt_prime_lt_one hp
  unfold towerFinitePart
  rw [kmsForm_one hq1.ne N]
  set q := 1 / Real.sqrt p
  have hd : towerDeficit p = -(localEuler p - Real.log p * (q / (1 - q))) := by rw [hE]; ring
  rw [hd]
  simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  have h : 1 - q ≠ 0 := by linarith
  field_simp
  ring

/-- **The sign law**: `F_p + c |·|² ≥ 0` on every depth iff `c ≥ 2 d_p`. -/
theorem towerFinitePart_add_nonneg_iff (hp : p.Prime) (c : ℝ) :
    (∀ (N : ℕ) (b : ℕ → ℝ), 0 ≤ towerFinitePart p N b + c * ∑ j ∈ range N, b j ^ 2) ↔
      2 * towerDeficit p ≤ c := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hq0 : 0 ≤ 1 / Real.sqrt p := inv_sqrt_prime_nonneg p
    have hq1 : 1 / Real.sqrt p < 1 := inv_sqrt_prime_lt_one hp
    have hL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    -- test the uniform profile at a depth `N` beyond `B/(2d_p − c)`
    have hone := fun N => h N (fun _ => 1)
    simp only [towerFinitePart_one hp, one_pow, sum_const, card_range, nsmul_eq_mul,
      mul_one] at hone
    set q := 1 / Real.sqrt p
    set d := towerDeficit p
    set B := 2 * q * Real.log p / (1 - q) ^ 2
    obtain ⟨N, hN⟩ := exists_nat_gt (B / (2 * d - c))
    have h1 := hone N
    have h2 : 2 * q * Real.log p * (1 - q ^ N) / (1 - q) ^ 2 ≤ B :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_right (by positivity)
        (by linarith [pow_nonneg hq0 N])) (by positivity)
    have h3 : B < N * (2 * d - c) := (div_lt_iff₀ (by linarith)).mp hN
    linarith
  · intro hc N b
    have h := towerFinitePart_ge hp N b
    have hS : 0 ≤ ∑ j ∈ range N, b j ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    nlinarith

/-- **The prime finite part is nonnegative on all classes of `p` iff `√p log p ≤ γ (p − 1)`.** -/
theorem towerFinitePart_nonneg_iff (hp : p.Prime) :
    (∀ (N : ℕ) (b : ℕ → ℝ), 0 ≤ towerFinitePart p N b) ↔ towerDeficit p ≤ 0 := by
  have h := towerFinitePart_add_nonneg_iff hp 0
  simp only [zero_mul, add_zero] at h
  rw [h]
  constructor <;> intro h' <;> linarith

/-- **At `p = 2` the prime finite part is indefinite**: `d_2 = √2 log 2 − γ > 0`. -/
theorem towerDeficit_two_pos : 0 < towerDeficit 2 := by
  have h1 : (1.4 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 := Real.log_two_gt_d9
  have h3 := Real.eulerMascheroniConstant_lt_two_thirds
  unfold towerDeficit
  norm_num
  nlinarith [mul_pos (by linarith : (0 : ℝ) < Real.sqrt 2 - 1.4)
    (by linarith : (0 : ℝ) < Real.log 2 - 0.6931471803)]

/-- **Large primes pay for their classes**: `d_p ≤ 0` for `p ≥ 2^16`. -/
theorem towerDeficit_nonpos (hp : 65536 ≤ p) : towerDeficit p ≤ 0 := by
  have hp' : (65536 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  -- write `√p` and the bound on `log p` in `s = p^{1/4}`
  set s := (p : ℝ) ^ ((1 : ℝ) / 4) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hp0 _
  have hs4 : s ^ 4 = p := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have hsq : Real.sqrt p = s ^ 2 := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlog : Real.log p ≤ 4 * s := by
    have h := Real.log_le_rpow_div hp0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [← hs] at h
    linarith [show s / (1 / 4) = 4 * s by ring]
  have hs16 : 16 ≤ s := by
    rw [← pow_le_pow_iff_left₀ (by norm_num) hs0.le (by norm_num : (4 : ℕ) ≠ 0), hs4]
    linarith
  have h5 : 1 ≤ s ^ 3 * (s - 8) := by
    have : (16 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs16 3
    nlinarith
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  unfold towerDeficit
  rw [hsq, sub_nonpos, div_le_iff₀ (by linarith)]
  -- `s² log p ≤ 4 s³ ≤ (s⁴ − 1)/2 ≤ γ (p − 1)`
  nlinarith [mul_le_mul_of_nonneg_left hlog (sq_nonneg s),
    mul_le_mul_of_nonneg_right hγ.le (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
