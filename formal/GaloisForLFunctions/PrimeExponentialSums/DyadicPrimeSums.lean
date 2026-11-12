import GaloisForLFunctions.PrimeExponentialSums.MajorArcs
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount

/-!
# Exponential sums over the primes of a dyadic interval

Write `S_N(β) = Σ_{N < p ≤ 2N} e(pβ)`, `L = log N`, `K = (2L)^14`.

* **Dirichlet in lowest terms** (`exists_coprime_approx`): `β = m + a/q + θ` with `m ∈ ℤ`,
  `(a, q) = 1`, `1 ≤ q ≤ Q`, `|θ| ≤ 1/(q(Q+1))`.
* **Minor arcs** (`eventually_minor_dyadic`): for `K ≤ q ≤ N/K` and `|θ|N ≤ 1`,
  `|S_N(a/q + θ)| ≤ 3N/L · (2 + 2π)/L + 3√(2N) log 2N` — Vinogradov at the exact rational
  `a/q` for every window `(N, t]`, then Abel summation against `e(nθ)/log n`.
* **Major arcs** (`eventually_major_dyadic`): for `q ≤ K`,
  `|S_N(a/q + θ)| ≤ |S_N(θ)|/φ(q) + K (N/L^A · (2 + 2π|θ|N)/L + 3√(2N) log 2N)` — character
  expansion and Siegel–Walfisz.
* **The principal oscillation** (`exists_principal_dyadic`): for `0 < |θ| ≤ 1/2`,
  `|S_N(θ)| ≤ 4CN/L^A · (2 + 2π|θ|N)/L + 1/(2|θ|L)` — the prime number theorem with a log-power
  error and geometric sums.
* **Counting** (`eventually_card_primes_ge`): `N ≤ 4L · #{N < p ≤ 2N}`.
-/

open Finset ArithmeticFunction Filter
open GaloisForLFunctions.LogarithmicChowla

namespace GaloisForLFunctions.PrimeExponentialSums

noncomputable section
set_option autoImplicit false

/-- **Dirichlet approximation in lowest terms.** For `Q ≥ 1` every `β` lies within `1/(q(Q+1))`
of `m + a/q` with `m ∈ ℤ`, `1 ≤ q ≤ Q` and `a` prime to `q`. -/
theorem exists_coprime_approx (β : ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ m : ℤ, ∃ a q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ Nat.Coprime a q ∧
      |β - m - a / q| ≤ 1 / (q * ((Q : ℝ) + 1)) := by
  set β₀ := β - ⌊β⌋ with hβ₀
  have hβ0 : 0 ≤ β₀ := sub_nonneg.mpr (Int.floor_le β)
  obtain ⟨j, k, hk0, hkQ, hjk⟩ := Real.exists_int_int_abs_mul_sub_le β₀ hQ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (0 : ℝ) < Q + 1 := by positivity
  have hj0 : 0 ≤ j := by
    have h1 : (k : ℝ) * β₀ - j ≤ 1 / (Q + 1) := (abs_le.mp hjk).2
    have h2 : 1 / ((Q : ℝ) + 1) < 1 := by rw [div_lt_one hQ1]; linarith
    have h3 : (0 : ℝ) ≤ k * β₀ := mul_nonneg (by exact_mod_cast hk0.le) hβ0
    have h4 : ((-1 : ℤ) : ℝ) < j := by push_cast; linarith
    have h5 : (-1 : ℤ) < j := by exact_mod_cast h4
    omega
  set J := j.toNat with hJdef
  set Kn := k.toNat with hKdef
  have hJ : ((J : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
  have hK : ((Kn : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0.le
  have hKpos : 0 < Kn := by omega
  have hKQ : Kn ≤ Q := by omega
  set g := Nat.gcd J Kn with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hKpos
  have hJg : J / g * g = J := Nat.div_mul_cancel (Nat.gcd_dvd_left J Kn)
  have hKg : Kn / g * g = Kn := Nat.div_mul_cancel (Nat.gcd_dvd_right J Kn)
  have hq1 : 1 ≤ Kn / g := Nat.div_pos (Nat.gcd_le_right _ hKpos) hg
  refine ⟨⌊β⌋, J / g, Kn / g, hq1, (Nat.div_le_self _ _).trans hKQ,
    Nat.coprime_div_gcd_div_gcd hg, ?_⟩
  have hqpos : (0 : ℝ) < (Kn / g : ℕ) := by exact_mod_cast hq1
  have hKr : (0 : ℝ) < Kn := by exact_mod_cast hKpos
  have hfrac : ((J / g : ℕ) : ℝ) / (Kn / g : ℕ) = (J : ℝ) / Kn := by
    rw [div_eq_div_iff hqpos.ne' hKr.ne']
    have e : (J / g) * Kn = J * (Kn / g) := by
      calc (J / g) * Kn = (J / g) * ((Kn / g) * g) := by rw [hKg]
        _ = ((J / g) * g) * (Kn / g) := by ring
        _ = J * (Kn / g) := by rw [hJg]
    exact_mod_cast e
  rw [hfrac]
  have hjk' : |(Kn : ℝ) * β₀ - J| ≤ 1 / (Q + 1) := by
    have e1 : (Kn : ℝ) = (k : ℝ) := by exact_mod_cast hK
    have e2 : (J : ℝ) = (j : ℝ) := by exact_mod_cast hJ
    rw [e1, e2]
    exact hjk
  have hrw : β - (⌊β⌋ : ℝ) - J / Kn = ((Kn : ℝ) * β₀ - J) / Kn := by
    rw [sub_div, mul_div_cancel_left₀ _ hKr.ne']
  rw [hrw, abs_div, abs_of_pos hKr, div_le_div_iff₀ hKr (by positivity)]
  have hqK : ((Kn / g : ℕ) : ℝ) ≤ Kn := by exact_mod_cast Nat.div_le_self _ _
  calc |(Kn : ℝ) * β₀ - J| * ((Kn / g : ℕ) * ((Q : ℝ) + 1))
      ≤ 1 / (Q + 1) * (Kn * ((Q : ℝ) + 1)) :=
        mul_le_mul hjk' (mul_le_mul_of_nonneg_right hqK hQ1.le) (by positivity) (by positivity)
    _ = 1 * Kn := by field_simp

/-- An integer shift of the frequency does not change `e(pβ)`. -/
theorem ex_natCast_mul_of_eq_add_int (p : ℕ) {β x : ℝ} (m : ℤ) (h : β = x + m) :
    ex (p * β) = ex (p * x) := by
  rw [h, mul_add, show (p : ℝ) * m = ((p * m : ℤ) : ℝ) by push_cast; ring, ex_add_int]

/-- `e(p a/q) e(pθ) = e(p(a/q + θ))`. -/
theorem ex_mul_ex_eq (p : ℕ) (x θ : ℝ) : ex (p * x) * ex (p * θ) = ex (p * (x + θ)) := by
  rw [← ex_add, mul_add]

theorem one_le_log_of_three_le {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1)
    (by have := Real.exp_one_lt_d9; have : (3 : ℝ) ≤ N := by exact_mod_cast hN
        linarith)

/-- `Σ_{N < n ≤ t} a(n) = Σ_{n ≤ t} a(n) − Σ_{n ≤ N} a(n)`. -/
theorem sum_Ioc_eq_sub_Icc (f : ℕ → ℂ) {N t : ℕ} (hNt : N ≤ t) :
    ∑ n ∈ Ioc N t, f n = ∑ n ∈ Icc 1 t, f n - ∑ n ∈ Icc 1 N, f n := by
  have hsplit : Icc 1 t = Icc 1 N ∪ Ioc N t := by
    ext n
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 N) (Ioc N t) := by
    rw [disjoint_left]
    intro n h1 h2
    simp only [mem_Icc, mem_Ioc] at h1 h2
    omega
  rw [hsplit, sum_union hdisj]
  ring

/-- **Minor arcs on a dyadic interval.** For all large `N`, with `L = log N` and
`K = (2L)^14`: every `a/q` in lowest terms with `K ≤ q ≤ N/K` and every `|θ| ≤ 1/N` give
`|Σ_{N < p ≤ 2N} e(p(a/q + θ))| ≤ 3N/L · (2 + 2π)/L + 3√(2N) log 2N`. -/
theorem eventually_minor_dyadic :
    ∀ᶠ N : ℕ in atTop, ∀ a q : ℕ, Nat.Coprime a q → (2 * Real.log N) ^ 14 ≤ q →
      (q : ℝ) ≤ N / (2 * Real.log N) ^ 14 → ∀ θ : ℝ, |θ| * N ≤ 1 →
        ‖∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * ((a : ℝ) / q + θ))‖
          ≤ 3 * N / Real.log N * ((2 + 2 * Real.pi) / Real.log N) +
            3 * Real.sqrt (2 * N) * Real.log (2 * N) := by
  obtain ⟨N₀, hmin⟩ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q : ℕ, Real.log N ^ 14 ≤ q →
      (q : ℝ) ≤ N / Real.log N ^ 14 → ∀ ζ : ℂ, IsPrimitiveRoot ζ q →
        ‖∑ n ∈ Icc 1 N, ((vonMangoldt n : ℝ) : ℂ) * ζ ^ n‖ ≤ N / Real.log N ^ 1 :=
    norm_sum_vonMangoldt_pow_le_minor 1
  filter_upwards [eventually_ge_atTop (max N₀ 3)] with N hN
  intro a q hcop hKq hqK θ hθ
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN3 : 3 ≤ N := (le_max_right _ _).trans hN
  have hL1 := one_le_log_of_three_le hN3
  set L := Real.log N with hL
  have hL0 : 0 < L := by linarith
  have hK1 : 1 ≤ (2 * L) ^ 14 := one_le_pow₀ (by linarith)
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := hK1.trans hKq
    exact_mod_cast this
  have hq0 : q ≠ 0 := by omega
  -- the primitive root `ζ = e(a/q)`
  have hζ : IsPrimitiveRoot (ex ((a : ℝ) / q)) q := by
    have h := Complex.isPrimitiveRoot_exp_of_coprime a q hq0 hcop
    have e : ex ((a : ℝ) / q) = Complex.exp (2 * Real.pi * Complex.I * (a / q)) := by
      rw [ex, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
    rw [e]
    exact h
  -- Vinogradov at every window end `t ∈ [N, 2N]`
  have hend : ∀ t : ℕ, N ≤ t → t ≤ 2 * N →
      ‖∑ n ∈ Icc 1 t, ((vonMangoldt n : ℝ) : ℂ) * ex ((a : ℝ) / q) ^ n‖ ≤ t / L := by
    intro t hNt ht2
    have htr : (N : ℝ) ≤ t := by exact_mod_cast hNt
    have ht2r : (t : ℝ) ≤ 2 * N := by exact_mod_cast ht2
    have hN3r : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    have hlogt : L ≤ Real.log t := Real.log_le_log (by linarith) htr
    have hlogt2 : Real.log t ≤ 2 * L :=
      (Real.log_le_log (by linarith) ht2r).trans (log_two_mul_le hL1)
    have hlogt0 : 0 < Real.log t := lt_of_lt_of_le hL0 hlogt
    have hpow : Real.log t ^ 14 ≤ (2 * L) ^ 14 := pow_le_pow_left₀ hlogt0.le hlogt2 14
    have h := hmin t (hN0.trans hNt) q (hpow.trans hKq)
      (hqK.trans (div_le_div₀ (by positivity) htr (by positivity) hpow)) _ hζ
    refine h.trans ?_
    rw [pow_one]
    exact div_le_div_of_nonneg_left (by positivity) hL0 hlogt
  have hwin : ∀ t, N ≤ t → t ≤ 2 * N →
      ‖∑ n ∈ Ioc N t, (vonMangoldt n : ℂ) * (fun n => ex ((a : ℝ) / q) ^ n) n‖
        ≤ 3 * N / L := by
    intro t hNt ht2
    rw [sum_Ioc_eq_sub_Icc _ hNt]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hend t hNt ht2
    have h2 := hend N le_rfl (by omega)
    have ht2r : (t : ℝ) ≤ 2 * N := by exact_mod_cast ht2
    calc _ ≤ (t : ℝ) / L + N / L := add_le_add h1 h2
      _ ≤ 2 * N / L + N / L := by gcongr
      _ = 3 * N / L := by ring
  have hbr := norm_sum_primes_le_of_windows (fun n => ex ((a : ℝ) / q) ^ n)
    (fun n => by rw [norm_pow, norm_ex, one_pow]) (by omega : 2 ≤ N) (by omega : N ≤ 2 * N) θ hwin
  have hrw : ∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, (fun n => ex ((a : ℝ) / q) ^ n) p * ex (p * θ)
      = ∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * ((a : ℝ) / q + θ)) :=
    sum_congr rfl fun p _ => by dsimp only; rw [← ex_nat_mul, ex_mul_ex_eq]
  rw [hrw] at hbr
  have hcast : ((2 * N : ℕ) : ℝ) - N = N := by push_cast; ring
  rw [hcast] at hbr
  have hc2 : ((2 * N : ℕ) : ℝ) = 2 * N := by push_cast; ring
  have hpow : (Chebyshev.psi ((2 * N : ℕ) : ℝ) - Chebyshev.theta ((2 * N : ℕ) : ℝ)) / Real.log 2
      ≤ 3 * Real.sqrt (2 * N) * Real.log (2 * N) := by
    calc _ ≤ 3 * Real.sqrt ((2 * N : ℕ) : ℝ) * Real.log ((2 * N : ℕ) : ℝ) :=
          psi_sub_theta_div_log_two_le (by omega)
      _ = 3 * Real.sqrt (2 * N) * Real.log (2 * N) := by rw [hc2]
  refine hbr.trans (add_le_add ?_ hpow)
  have hθN : 2 * Real.pi * |θ| * N ≤ 2 * Real.pi := by
    calc 2 * Real.pi * |θ| * N = 2 * Real.pi * (|θ| * N) := by ring
      _ ≤ 2 * Real.pi * 1 := mul_le_mul_of_nonneg_left hθ (by positivity)
      _ = 2 * Real.pi := mul_one _
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact div_le_div_of_nonneg_right (by linarith) hL0.le

/-- `(2L)^14 ≤ L^15` once `L ≥ 2^14`. -/
theorem two_mul_pow_le {L : ℝ} (hL : 2 ^ 14 ≤ L) : (2 * L) ^ 14 ≤ L ^ 15 := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  calc (2 * L) ^ 14 = 2 ^ 14 * L ^ 14 := mul_pow _ _ _
    _ ≤ L * L ^ 14 := mul_le_mul_of_nonneg_right hL (by positivity)
    _ = L ^ 15 := by ring

/-- `(log N)^n ≤ δ N` for all large `N`. -/
theorem eventually_log_nat_pow_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ n ≤ δ * N :=
  tendsto_natCast_atTop_atTop.eventually
    (ShortIntervalPrimesInProgressions.eventually_log_pow_le n hδ)

theorem tendsto_log_nat : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- **Major arcs on a dyadic interval.** For all large `N`, with `L = log N`: every `a/q` in
lowest terms with `q ≤ (2L)^14` and every `θ` give
`|Σ_{N < p ≤ 2N} e(p(a/q + θ))| ≤ |Σ_{N < p ≤ 2N} e(pθ)|/φ(q) + (2L)^14 D`,
`D = N/L^A · (2 + 2π|θ|N)/L + 3√(2N) log 2N`. -/
theorem eventually_major_dyadic (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ a q : ℕ, Nat.Coprime a q → 1 ≤ q → (q : ℝ) ≤ (2 * Real.log N) ^ 14 →
      ∀ θ : ℝ,
        ‖∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * ((a : ℝ) / q + θ))‖
          ≤ ‖∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * θ)‖ / q.totient +
            (2 * Real.log N) ^ 14 *
              (N / Real.log N ^ A * ((2 + 2 * Real.pi * |θ| * N) / Real.log N) +
                3 * Real.sqrt (2 * N) * Real.log (2 * N)) := by
  obtain ⟨N₀, hchar⟩ := exists_norm_sum_primes_char_le A 15 (by norm_num)
  filter_upwards [eventually_ge_atTop (max N₀ 1), tendsto_log_nat.eventually_ge_atTop (2 ^ 14),
    eventually_log_nat_pow_le 15 (δ := 1 / 2) (by norm_num)] with N hN hL hLN
  intro a q hcop hq1 hqK θ
  haveI : NeZero q := ⟨by omega⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hKL := two_mul_pow_le hL
  have hqL : (q : ℝ) ≤ Real.log N ^ 15 := hqK.trans hKL
  have hqN : q < N := by
    have : (q : ℝ) < N := by linarith
    exact_mod_cast this
  set S := (Ioc N (2 * N)).filter Nat.Prime with hSdef
  have hS : ∀ n ∈ S, IsUnit (n : ZMod q) := by
    intro n hn
    obtain ⟨hnI, hnp⟩ := mem_filter.mp hn
    have hqn : q < n := lt_trans hqN (mem_Ioc.mp hnI).1
    exact (ZMod.isUnit_iff_coprime n q).mpr ((Nat.Prime.coprime_iff_not_dvd hnp).mpr
      fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))
  have hL0 : 0 ≤ Real.log N := le_trans (by norm_num) hL
  have hl2 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hD0 : 0 ≤ N / Real.log N ^ A * ((2 + 2 * Real.pi * |θ| * N) / Real.log N) +
      3 * Real.sqrt (2 * N) * Real.log (2 * N) := by positivity
  have hmain := norm_sum_addPhase_le (ZMod.unitOfCoprime a hcop) S hS (fun n => ex (n * θ)) hD0
    (fun χ hχ => hchar N hN0 q χ hχ hqL hqN θ (2 * N) (by omega) le_rfl)
  have hlhs : ∑ p ∈ S, addPhase ((ZMod.unitOfCoprime a hcop : (ZMod q)ˣ) : ZMod q) p *
      ex (p * θ) = ∑ p ∈ S, ex (p * ((a : ℝ) / q + θ)) := by
    refine sum_congr rfl fun p _ => ?_
    rw [ZMod.coe_unitOfCoprime, addPhase_natCast, ← ex_mul_ex_eq]
    congr 2
    ring
  rw [hlhs] at hmain
  exact hmain.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hqK hD0))

/-- **The primes of a dyadic interval.** For all large `N`: `N ≤ 4 log N · #{N < p ≤ 2N}`. -/
theorem eventually_card_primes_ge :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ≤ 4 * Real.log N * ((Ioc N (2 * N)).filter Nat.Prime).card := by
  obtain ⟨C, hC0, T, hT3, hθ⟩ := RHTower.PrimeCells.exists_abs_theta_sub_le 1
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop T,
    tendsto_log_nat.eventually_ge_atTop (8 * C), tendsto_log_nat.eventually_ge_atTop 1]
    with N hT hLC hL1
  set L := Real.log N with hL
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNN : (N : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by push_cast; linarith
  have hinc := RHTower.PrimeCells.abs_theta_increment_le hC0.le hT3 hθ hT hNN
  have hsum : Chebyshev.theta ((2 * N : ℕ) : ℝ) - Chebyshev.theta N
      = ∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, Real.log p := by
    rw [← sum_Ioc_primeLog_eq (by omega : N ≤ 2 * N), sum_filter]
  have hc2 : ((2 * N : ℕ) : ℝ) = 2 * N := by push_cast; ring
  have hNpos : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    rw [this, Nat.cast_zero, Real.log_zero] at hL
    linarith
  have hlog2 : Real.log (2 * N) ≤ 2 * L := log_two_mul_le hL1
  have hle : ∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, Real.log p
      ≤ ((Ioc N (2 * N)).filter Nat.Prime).card * (2 * L) := by
    have h := Finset.sum_le_card_nsmul ((Ioc N (2 * N)).filter Nat.Prime)
      (fun p => Real.log (p : ℝ)) (2 * L) (fun p hp => by
        obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
        have hp2 : (p : ℝ) ≤ 2 * N := by exact_mod_cast (mem_Ioc.mp hpI).2
        exact (Real.log_le_log (by exact_mod_cast hpp.pos) hp2).trans hlog2)
    rwa [nsmul_eq_mul] at h
  rw [hsum, pow_one, hc2] at hinc
  have hlow : (N : ℝ) / 2 ≤ ∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, Real.log p := by
    have h1 := (abs_le.mp hinc).1
    have h2 : 2 * C * (2 * N) / L ≤ N / 2 := by
      rw [div_le_iff₀ hL0]
      nlinarith [mul_le_mul_of_nonneg_left hLC hN0]
    linarith
  nlinarith

/-- **The principal oscillation.** For each `A` there is `C ≥ 0` such that for all large `N` and
`0 < |θ| ≤ 1/2`:
`|Σ_{N < p ≤ 2N} e(pθ)| ≤ 4CN/L^A · (2 + 2π|θ|N)/L + 1/(2|θ|) · 1/L`, `L = log N`. -/
theorem exists_principal_dyadic (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ θ : ℝ, θ ≠ 0 → |θ| ≤ 1 / 2 →
      ‖∑ p ∈ (Ioc N (2 * N)).filter Nat.Prime, ex (p * θ)‖
        ≤ 4 * C * N / Real.log N ^ A * ((2 + 2 * Real.pi * |θ| * N) / Real.log N) +
          1 / (2 * |θ|) * (1 / Real.log N) := by
  obtain ⟨C, hC0, T, hT3, hθ⟩ := RHTower.PrimeCells.exists_abs_theta_sub_le A
  refine ⟨C, hC0.le, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop T, eventually_ge_atTop 2]
    with N hT hN2
  intro θ hθ0 hθ2
  have hL0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hE : ∀ t : ℕ, N ≤ t → t ≤ 2 * N →
      |Chebyshev.theta t - Chebyshev.theta N - ((t : ℝ) - N)|
        ≤ 4 * C * N / Real.log N ^ A := by
    intro t hNt ht2
    have h := RHTower.PrimeCells.abs_theta_increment_le hC0.le hT3 hθ (b := t) hT
      (by exact_mod_cast hNt)
    refine h.trans ?_
    have ht2r : (t : ℝ) ≤ 2 * N := by exact_mod_cast ht2
    have hLA : 0 < Real.log N ^ A := pow_pos hL0 A
    rw [div_le_div_iff_of_pos_right hLA]
    nlinarith
  have h := norm_sum_primes_ex_le hN2 (by omega : N ≤ 2 * N) hθ0 hθ2 hE
  have hc : ((2 * N : ℕ) : ℝ) - N = N := by push_cast; ring
  rwa [hc] at h

end

end GaloisForLFunctions.PrimeExponentialSums
