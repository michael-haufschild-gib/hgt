import GaloisForLFunctions.PrimeExponentialSums.DyadicPrimeSums
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheConductorEnergyKeepsALogarithmicReserve

/-!
# The primes of a dyadic interval are equidistributed off the major arcs

**Theorem** (`exists_off_major_arcs`). For every `0 < η ≤ 1` there are `Q₀` and `W > 0` such that
for all large `N` and every `β` at distance more than `W/N` from every rational `a/q`, `q ≤ Q₀`:

`|Σ_{N < p ≤ 2N} e(pβ)| ≤ η · #{N < p ≤ 2N}`.

Proof. With `L = log N`, `K = (2L)^14`, Dirichlet gives `β = m + a/q + θ`, `(a, q) = 1`,
`q ≤ N/K`, `|θ|N ≤ K`.

* `q ≥ K`: then `|θ|N ≤ 1`, and the minor-arc bound is `O(N/L²) + O(√N log N)`.
* `q < K`: the major-arc expansion leaves `|S_N(θ)|/φ(q)` plus `O(N/L²)`.
  - `q > Q₀ = ⌈32/η²⌉`: `q ≤ 2φ(q)²` gives `1/φ(q) ≤ η/4`.
  - `q ≤ Q₀`: the hypothesis gives `|θ| > W/N` with `W = 8/η`, and the principal oscillation
    is at most `1/(2|θ|L) + O(N/L²) ≤ ηN/(16L) + O(N/L²)`.

Finally `#{N < p ≤ 2N} ≥ N/(4L)`.
-/

open Finset ArithmeticFunction Filter
open GaloisForLFunctions.LogarithmicChowla

namespace GaloisForLFunctions.PrimeExponentialSums

noncomputable section
set_option autoImplicit false

/-- `(log N)^m √N ≤ c N` for all large `N`. -/
theorem eventually_log_pow_mul_sqrt_le (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ m * Real.sqrt N ≤ c * N := by
  have h := (isLittleO_log_rpow_rpow_atTop (m : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound hc
  have h' : ∀ᶠ x : ℝ in atTop, Real.log x ^ m * Real.sqrt x ≤ c * x := by
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_natCast, abs_of_nonneg (pow_nonneg hl m),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hx
    calc Real.log x ^ m * Real.sqrt x ≤ c * Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg x)
      _ = c * x := by rw [mul_assoc, Real.mul_self_sqrt (by linarith)]
  exact tendsto_natCast_atTop_atTop.eventually h'

/-- Bookkeeping on the minor arcs: `3N/L · (2 + 2π)/L + 3TY ≤ ηN/(8L)`. -/
theorem minor_remainder_le {η N L S T Y : ℝ} (hη : 0 < η) (hL1 : 1 ≤ L) (hLη : 432 ≤ η * L)
    (hN : 0 ≤ N) (hS : 0 ≤ S) (hT : T ≤ 2 * S) (hY0 : 0 ≤ Y) (hY : Y ≤ 2 * L)
    (hLP : L ^ 17 * S ≤ η / 288 * N) :
    3 * N / L * ((2 + 2 * Real.pi) / L) + 3 * T * Y ≤ η / 8 * N / L := by
  have hL0 : 0 < L := by linarith
  have hpi := Real.pi_lt_d2
  have h1 : 3 * N / L * ((2 + 2 * Real.pi) / L) ≤ η / 16 * N / L := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hL0]
    have key : 3 * (2 + 2 * Real.pi) ≤ η * L / 16 := by linarith
    calc 3 * N * (2 + 2 * Real.pi) * L = 3 * (2 + 2 * Real.pi) * (N * L) := by ring
      _ ≤ η * L / 16 * (N * L) := mul_le_mul_of_nonneg_right key (by positivity)
      _ = η / 16 * N * (L * L) := by ring
  have h2 : 3 * T * Y ≤ η / 16 * N / L := by
    rw [le_div_iff₀ hL0]
    have hTY : 3 * T * Y ≤ 3 * (2 * S) * (2 * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hT (by norm_num)) hY hY0 (by positivity)
    have hL2 : L ^ 2 ≤ L ^ 17 := pow_le_pow_right₀ hL1 (by norm_num)
    have hL2S : L ^ 2 * S ≤ η / 288 * N := (mul_le_mul_of_nonneg_right hL2 hS).trans hLP
    calc 3 * T * Y * L ≤ 3 * (2 * S) * (2 * L) * L := mul_le_mul_of_nonneg_right hTY hL0.le
      _ = 12 * (L ^ 2 * S) := by ring
      _ ≤ 12 * (η / 288 * N) := mul_le_mul_of_nonneg_left hL2S (by norm_num)
      _ ≤ η / 16 * N := by nlinarith [mul_nonneg hη.le hN]
  calc _ ≤ η / 16 * N / L + η / 16 * N / L := add_le_add h1 h2
    _ = η / 8 * N / L := by ring

/-- Bookkeeping on the major arcs:
`4CN/L^33 · G/L + K (N/L^33 · G/L + 3TY) ≤ ηN/(8L)` with `G = 2 + 2πK`. -/
theorem major_remainder_le {η N L S T Y K C : ℝ} (hL1 : 1 ≤ L) (hK1 : 1 ≤ K)
    (hKL : K ≤ L ^ 15) (hC : 0 ≤ C) (hLC : 864 * C ≤ η * L) (hLη : 216 ≤ η * L) (hN : 0 ≤ N)
    (hS : 0 ≤ S) (hT0 : 0 ≤ T) (hT : T ≤ 2 * S) (hY0 : 0 ≤ Y) (hY : Y ≤ 2 * L)
    (hLP : L ^ 17 * S ≤ η / 288 * N) :
    4 * C * N / L ^ 33 * ((2 + 2 * Real.pi * K) / L) +
        K * (N / L ^ 33 * ((2 + 2 * Real.pi * K) / L) + 3 * T * Y) ≤ η / 8 * N / L := by
  have hL0 : 0 < L := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hG : 2 + 2 * Real.pi * K ≤ 9 * K := by nlinarith
  have hGL : 2 + 2 * Real.pi * K ≤ 9 * L ^ 15 := by linarith
  -- the prime number theorem remainder
  have h1 : 4 * C * N / L ^ 33 * ((2 + 2 * Real.pi * K) / L) ≤ η / 24 * N / L := by
    have step : 4 * C * N / L ^ 33 * ((2 + 2 * Real.pi * K) / L)
        ≤ 4 * C * N / L ^ 33 * (9 * L ^ 15 / L) := by gcongr
    refine step.trans ?_
    have e : 4 * C * N / L ^ 33 * (9 * L ^ 15 / L) = 36 * C * N / L ^ 19 := by
      rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [e, div_le_div_iff₀ (by positivity) hL0]
    have h36 : 36 * C ≤ η * L / 24 := by linarith
    calc 36 * C * N * L ≤ 36 * C * N * L ^ 18 :=
          mul_le_mul_of_nonneg_left (le_self_pow₀ hL1 (by norm_num)) (by positivity)
      _ = 36 * C * (N * L ^ 18) := by ring
      _ ≤ η * L / 24 * (N * L ^ 18) := mul_le_mul_of_nonneg_right h36 (by positivity)
      _ = η / 24 * N * L ^ 19 := by ring
  -- the Siegel–Walfisz remainder
  have h2 : K * (N / L ^ 33 * ((2 + 2 * Real.pi * K) / L)) ≤ η / 24 * N / L := by
    have h2a : K * (N / L ^ 33 * ((2 + 2 * Real.pi * K) / L))
        ≤ K * (N / L ^ 33 * (9 * K / L)) := by gcongr
    have e2 : K * (N / L ^ 33 * (9 * K / L)) = 9 * N * (K * K) / L ^ 34 := by
      rw [div_mul_div_comm, mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
      ring
    have hKK : K * K ≤ L ^ 30 := by
      calc K * K ≤ L ^ 15 * L ^ 15 := mul_le_mul hKL hKL hK0 (by positivity)
        _ = L ^ 30 := by ring
    have h2b : 9 * N * (K * K) / L ^ 34 ≤ 9 * N * L ^ 30 / L ^ 34 := by gcongr
    have e3 : 9 * N * L ^ 30 / L ^ 34 = 9 * N / L ^ 4 := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    have h2c : 9 * N / L ^ 4 ≤ η / 24 * N / L := by
      rw [div_le_div_iff₀ (by positivity) hL0]
      have h9 : 9 ≤ η * L / 24 := by linarith
      calc 9 * N * L ≤ 9 * N * L ^ 3 :=
            mul_le_mul_of_nonneg_left (le_self_pow₀ hL1 (by norm_num)) (by positivity)
        _ = 9 * (N * L ^ 3) := by ring
        _ ≤ η * L / 24 * (N * L ^ 3) := mul_le_mul_of_nonneg_right h9 (by positivity)
        _ = η / 24 * N * L ^ 4 := by ring
    calc _ ≤ K * (N / L ^ 33 * (9 * K / L)) := h2a
      _ = 9 * N * (K * K) / L ^ 34 := e2
      _ ≤ 9 * N * L ^ 30 / L ^ 34 := h2b
      _ = 9 * N / L ^ 4 := e3
      _ ≤ η / 24 * N / L := h2c
  -- the prime powers
  have h3 : K * (3 * T * Y) ≤ η / 24 * N / L := by
    rw [le_div_iff₀ hL0]
    have hTY : 3 * T * Y ≤ 12 * (S * L) := by
      have := mul_le_mul (mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 3)) hY hY0
        (by positivity)
      linarith
    calc K * (3 * T * Y) * L ≤ L ^ 15 * (12 * (S * L)) * L :=
          mul_le_mul_of_nonneg_right (mul_le_mul hKL hTY (by positivity) (by positivity)) hL0.le
      _ = 12 * (L ^ 17 * S) := by ring
      _ ≤ 12 * (η / 288 * N) := mul_le_mul_of_nonneg_left hLP (by norm_num)
      _ = η / 24 * N := by ring
  rw [mul_add]
  calc _ ≤ η / 24 * N / L + (η / 24 * N / L + η / 24 * N / L) := add_le_add h1 (add_le_add h2 h3)
    _ = η / 8 * N / L := by ring

/-- `1/φ(q) ≤ η/4` once `q > 32/η²`, by `q ≤ 2φ(q)²`. -/
theorem inv_totient_le {η : ℝ} (hη : 0 < η) {q : ℕ} (hq : 32 / η ^ 2 < q) :
    1 / (q.totient : ℝ) ≤ η / 4 := by
  have hsq : (q : ℝ) ≤ 2 * (q.totient : ℝ) ^ 2 := by
    exact_mod_cast RenormalizedArithmeticPotentialTheory.nat_le_two_mul_totient_sq q
  have hφ0 : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have h32 : 32 < η ^ 2 * q := by
    rwa [div_lt_iff₀ (by positivity), mul_comm] at hq
  have h16 : 16 < (η * q.totient) ^ 2 := by nlinarith
  have h4 : 4 < η * q.totient := by
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonneg hη.le hφ0]
  have hφpos : (0 : ℝ) < q.totient := by
    by_contra h
    have : (q.totient : ℝ) = 0 := le_antisymm (not_lt.mp h) hφ0
    rw [this, mul_zero] at h4
    linarith
  rw [div_le_div_iff₀ hφpos (by norm_num)]
  linarith

/-- `√(2N) ≤ 2√N`. -/
theorem sqrt_two_mul_le (N : ℝ) (hN : 0 ≤ N) : Real.sqrt (2 * N) ≤ 2 * Real.sqrt N := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt hN]
  linarith

/-- **The primes of a dyadic interval off the major arcs.** For every `0 < η ≤ 1` there are
`Q₀` and `W > 0` such that for all large `N` and every `β` with `|β − a/q| > W/N` for all
`a ∈ ℤ`, `1 ≤ q ≤ Q₀`: `|Σ_{N < p ≤ 2N} e(pβ)| ≤ η · #{N < p ≤ 2N}`. -/
theorem exists_off_major_arcs {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ Q₀ : ℕ, ∃ W : ℝ, 0 < W ∧ ∀ᶠ N : ℕ in atTop, ∀ β : ℝ,
      (∀ q ∈ Icc 1 Q₀, ∀ a : ℤ, W / N < |β - a / q|) →
        ‖∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * β)‖
          ≤ η * ((Ioc N (2 * N)).filter Nat.Prime).card := by
  obtain ⟨C, hC0, hprin⟩ := exists_principal_dyadic 33
  refine ⟨⌈32 / η ^ 2⌉₊, 8 / η, by positivity, ?_⟩
  filter_upwards [eventually_minor_dyadic, eventually_major_dyadic 33, eventually_card_primes_ge,
    hprin, tendsto_log_nat.eventually_ge_atTop (2 ^ 14),
    (tendsto_log_nat.const_mul_atTop hη).eventually_ge_atTop (864 * C + 432),
    eventually_log_pow_mul_sqrt_le 17 (c := η / 288) (by positivity), eventually_ge_atTop 3]
    with N hmin hmaj hcard hpr hL14 hLη hLP hN3
  intro β hβ
  set cnt := ((Ioc N (2 * N)).filter Nat.Prime).card with hcnt
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL14
  have hL0 : 0 < L := by linarith
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hS0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hS1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by linarith)
  have hT0 : 0 ≤ Real.sqrt (2 * N) := Real.sqrt_nonneg _
  have hT := sqrt_two_mul_le N hN0
  have hY := log_two_mul_le (N := N) hL1
  have hY0 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hNL : (N : ℝ) / L ≤ 4 * cnt := by
    rw [div_le_iff₀ hL0]
    linarith
  have hcnt0 : (0 : ℝ) ≤ cnt := Nat.cast_nonneg _
  -- the scale `K = (2L)^14`
  set K := (2 * L) ^ 14 with hKdef
  have hK1 : 1 ≤ K := one_le_pow₀ (by linarith)
  have hK0 : 0 < K := by linarith
  have hKL : K ≤ L ^ 15 := two_mul_pow_le hL14
  have hKN : 2 * K ≤ N := by
    have h1 : L ^ 15 ≤ L ^ 17 := pow_le_pow_right₀ hL1 (by norm_num)
    have h2 : L ^ 17 ≤ L ^ 17 * Real.sqrt N := le_mul_of_one_le_right (by positivity) hS1
    have h3 : η / 288 * N ≤ N / 288 := by
      have := mul_le_mul_of_nonneg_right hη1 hN0
      linarith
    linarith
  -- Dirichlet approximation with denominators up to `N/K`
  set Qd := ⌊(N : ℝ) / K⌋₊ with hQddef
  have hQd : 0 < Qd := Nat.floor_pos.mpr (by rw [le_div_iff₀ hK0]; linarith)
  have hQd1 : (N : ℝ) / K < Qd + 1 := Nat.lt_floor_add_one _
  have hQdle : (Qd : ℝ) ≤ N / K := Nat.floor_le (by positivity)
  obtain ⟨m, a, q, hq1, hqQ, hcop, happ⟩ := exists_coprime_approx β hQd
  set θ := β - m - a / q with hθdef
  have hsum : ∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * β)
      = ∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * ((a : ℝ) / q + θ)) :=
    sum_congr rfl fun p _ => ex_natCast_mul_of_eq_add_int p m (by rw [hθdef]; ring)
  have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hden0 : (0 : ℝ) < q * ((Qd : ℝ) + 1) := by positivity
  have hθ1 : |θ| * (q * ((Qd : ℝ) + 1)) ≤ 1 := (le_div_iff₀ hden0).mp happ
  have hθK : |θ| * N ≤ K := by
    have hden : (N : ℝ) / K ≤ q * ((Qd : ℝ) + 1) :=
      hQd1.le.trans (le_mul_of_one_le_left (by positivity) hq1r)
    have h := (mul_le_mul_of_nonneg_left hden (abs_nonneg θ)).trans hθ1
    have e : |θ| * N = |θ| * (N / K) * K := by field_simp
    rw [e]
    exact mul_le_of_le_one_left hK0.le h
  rw [hsum]
  by_cases hminor : K ≤ q
  · -- minor arcs
    have hqK : (q : ℝ) ≤ N / K := (Nat.cast_le.mpr hqQ).trans hQdle
    have hθN : |θ| * N ≤ 1 := by
      have hNq : (N : ℝ) ≤ q * ((Qd : ℝ) + 1) := by
        have e : (N : ℝ) = K * (N / K) := by field_simp
        rw [e]
        exact mul_le_mul hminor hQd1.le (by positivity) (by positivity)
      exact (mul_le_mul_of_nonneg_left hNq (abs_nonneg θ)).trans hθ1
    refine (hmin a q hcop hminor hqK θ hθN).trans ?_
    have hrem := minor_remainder_le hη hL1 (by linarith) hN0 hS0 hT hY0 hY hLP
    calc _ ≤ η / 8 * N / L := hrem
      _ = η / 8 * (N / L) := by ring
      _ ≤ η / 8 * (4 * cnt) := mul_le_mul_of_nonneg_left hNL (by positivity)
      _ ≤ η * cnt := by linarith [mul_nonneg hη.le hcnt0]
  · -- major arcs
    rw [not_le] at hminor
    have h := hmaj a q hcop hq1 hminor.le θ
    refine h.trans ?_
    have hD : (2 * L) ^ 14 * (N / L ^ 33 * ((2 + 2 * Real.pi * |θ| * N) / L) +
          3 * Real.sqrt (2 * N) * Real.log (2 * N))
        ≤ K * (N / L ^ 33 * ((2 + 2 * Real.pi * K) / L) +
          3 * Real.sqrt (2 * N) * Real.log (2 * N)) := by
      have hG : 2 + 2 * Real.pi * |θ| * N ≤ 2 + 2 * Real.pi * K := by
        have := mul_le_mul_of_nonneg_left hθK (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
        linarith
      gcongr
    have hrem := major_remainder_le (C := C) hL1 hK1 hKL hC0 (by linarith) (by linarith) hN0
      hS0 hT0 hT hY0 hY hLP
    have hPC0 : 0 ≤ 4 * C * N / L ^ 33 * ((2 + 2 * Real.pi * K) / L) := by positivity
    have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    by_cases hQ0 : q ≤ ⌈32 / η ^ 2⌉₊
    · -- small denominators: the hypothesis keeps `θ` away from zero
      have hβq := hβ q (mem_Icc.mpr ⟨hq1, hQ0⟩) (a + m * q)
      have e : β - (((a + m * q : ℤ) : ℝ)) / q = θ := by
        rw [hθdef]
        push_cast
        field_simp
        ring
      rw [e] at hβq
      have hW : 0 < 8 / η / N := by positivity
      have hθpos : 0 < |θ| := hW.trans hβq
      have hθ0 : θ ≠ 0 := abs_pos.mp hθpos
      have hNpos : (0 : ℝ) < N := by linarith
      have hθ2 : |θ| ≤ 1 / 2 := by
        have : |θ| * N ≤ 1 / 2 * N := by linarith
        exact le_of_mul_le_mul_right this hNpos
      have hP := hpr θ hθ0 hθ2
      have hinv : 1 / (2 * |θ|) * (1 / L) ≤ η / 16 * N / L := by
        have h1 : 1 / (2 * |θ|) ≤ η / 16 * N := by
          rw [div_le_iff₀ (by positivity)]
          have h8 : 8 / η < |θ| * N := by rwa [div_lt_iff₀ (by positivity)] at hβq
          have h8' : 8 < η * (|θ| * N) := by
            rwa [div_lt_iff₀ hη, mul_comm] at h8
          linarith
        calc 1 / (2 * |θ|) * (1 / L) ≤ η / 16 * N * (1 / L) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = η / 16 * N / L := by ring
      have hP' : ‖∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * θ)‖
          ≤ 4 * C * N / L ^ 33 * ((2 + 2 * Real.pi * K) / L) + η / 16 * N / L := by
        refine hP.trans (add_le_add ?_ hinv)
        have hG : 2 + 2 * Real.pi * |θ| * N ≤ 2 + 2 * Real.pi * K := by
          have := mul_le_mul_of_nonneg_left hθK (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
          linarith
        gcongr
      have hdiv : ‖∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * θ)‖ / q.totient
          ≤ ‖∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * θ)‖ :=
        div_le_self (norm_nonneg _) hφ1
      calc _ ≤ (4 * C * N / L ^ 33 * ((2 + 2 * Real.pi * K) / L) + η / 16 * N / L) +
            K * (N / L ^ 33 * ((2 + 2 * Real.pi * K) / L) +
              3 * Real.sqrt (2 * N) * Real.log (2 * N)) := add_le_add (hdiv.trans hP') hD
        _ ≤ η / 8 * N / L + η / 16 * N / L := by linarith
        _ = 3 * η / 16 * (N / L) := by ring
        _ ≤ 3 * η / 16 * (4 * cnt) := mul_le_mul_of_nonneg_left hNL (by positivity)
        _ ≤ η * cnt := by linarith [mul_nonneg hη.le hcnt0]
    · -- large denominators: `1/φ(q) ≤ η/4`
      rw [not_le] at hQ0
      have hq32 : 32 / η ^ 2 < q := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hQ0)
      have hinv := inv_totient_le hη hq32
      have htriv : ‖∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * θ)‖ ≤ cnt := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_ex, sum_const, nsmul_eq_mul, mul_one, hcnt]
      have hdiv : ‖∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * θ)‖ / q.totient
          ≤ η / 4 * cnt := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul hinv htriv (norm_nonneg _) (by positivity)
      calc _ ≤ η / 4 * cnt + K * (N / L ^ 33 * ((2 + 2 * Real.pi * K) / L) +
              3 * Real.sqrt (2 * N) * Real.log (2 * N)) := add_le_add hdiv hD
        _ ≤ η / 4 * cnt + η / 8 * N / L := by linarith
        _ = η / 4 * cnt + η / 8 * (N / L) := by ring
        _ ≤ η / 4 * cnt + η / 8 * (4 * cnt) := by gcongr
        _ ≤ η * cnt := by linarith [mul_nonneg hη.le hcnt0]

end

end GaloisForLFunctions.PrimeExponentialSums
