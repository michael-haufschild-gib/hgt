import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralGramSimplification
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.UpwardCentering
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FiniteHorizonPrimeCharge
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimeHarmonicMean
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# Uniform scale domination of the literal channel norms

The literal upward prime channel of a prime band has five finite costs: short rows, middle rows,
terminal rows, own-prime towers and periodic covariance. One choice of row cutoffs,

`A = M Q² ⌈log N⌉`,  `J = ⌊N / (c e Q²)⌋`,

dominates all five at once on the whole range `c e M Q⁵ ⌈log N⌉ ≤ N`, with `B` the offset count, `W` the
logarithmic width, `S = Σ 1/p`, `A_P = Σ log p / p`:

`‖U‖² ≤ K (B V W)² (s²(1+S)² + (s A_P)²/R²)`.

Primes at most `R`, and primes dividing the period, leave the covariance range. They pay by the
absolute size of their profile, which is what the small amplitude `s` affords. For the coherent amplitude
`s = t / Σ_{p≤Q} log p / p`, the choice `R ≈ √log Q` gives the law

`‖U‖ ≤ K B V W |t| (1/√log Q + ω_Q(M)/log Q)`,

uniform in the horizon, the period, the offsets and the amplitude. It holds for the literal harmonically
centered coherent charge too (`exists_literal_harmonicPrimeCharge_channel_law`).
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open MeasureTheory Finset
open GaloisForLFunctions.ArithmeticCouplingTheory
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open GaloisForLFunctions.CriticalScaleArithmeticRigidity
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- The row cutoff separating short rows from middle rows. -/
def literalScaleLow (N M Q : ℕ) : ℕ := M * Q ^ 2 * ⌈Real.log N⌉₊

/-- The row cutoff separating middle rows from terminal rows. -/
def literalScaleHigh (c : ℝ) (N Q : ℕ) : ℕ := ⌊(N : ℝ) / (c * Real.exp 1 * (Q : ℝ) ^ 2)⌋₊

/-- The number of band primes dividing the period. -/
def periodBandDivisors (Q M : ℕ) : ℕ := ((Icc 1 Q).filter fun p => p.Prime ∧ p ∣ M).card

/-- The five literal costs collapse to one scale law once each is compared with its cutoff. -/
private theorem literal_cost_algebra {B s V W S AP R μ K L logA logD Y m A C Q2 q0 h0 : ℝ}
    (hμ : 0 < μ) (hK : 0 ≤ K) (hL : 1 ≤ L) (hW : 1 ≤ W) (hS : 0 ≤ S) (hR : 1 ≤ R)
    (hlogA : 1 + logA ≤ 2 * L) (hlogD : logD ≤ 2 * L) (hY0 : 0 ≤ Y) (hY : Y ≤ 3 * W * L)
    (hm : 0 ≤ m) (hQ2 : 0 < Q2) (hA : m * Q2 * L ≤ A) (hA0 : 0 < A) (hC : C ^ 2 ≤ Q2)
    (hq1 : q0 ≤ 1) (hh0 : 0 ≤ h0) (hCh : C ^ 2 * h0 ≤ 1) :
    (32 * B ^ 2 * s ^ 2 * V ^ 2 * (1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2 * C ^ 2 * h0)) *
        (1 + logA) / L +
      64 * B ^ 2 * s ^ 2 * V ^ 2 * (1027 * W ^ 2 / R + 576 * W * S * q0) +
      64 * B ^ 2 * s ^ 2 * V ^ 2 * W ^ 2 * S * logD / L +
      256 * B ^ 2 * V ^ 2 * (s * AP) ^ 2 / R ^ 2 +
      (64 * m * V ^ 2 * (2 * (2 * μ) ^ 2 + 2 * (2 * μ) * K) / μ ^ 2) *
        (s ^ 2 * C ^ 2 * B ^ 2 * Y ^ 2) / (A * L) ≤
      (10 ^ 8 + 2304 * (K / μ)) *
        ((B * V * W) ^ 2 * (s ^ 2 * (1 + S) ^ 2 + (s * AP) ^ 2 / R ^ 2)) := by
  have hL0 : 0 < L := by linarith only [hL]
  have hR0 : 0 < R := by linarith only [hR]
  have hκ : (2 * (2 * μ) ^ 2 + 2 * (2 * μ) * K) / μ ^ 2 = 8 + 4 * (K / μ) := by
    field_simp
    ring
  have hk : 0 ≤ K / μ := div_nonneg hK hμ.le
  obtain ⟨k, hkd⟩ : ∃ k, k = K / μ := ⟨_, rfl⟩
  rw [← hkd] at hk hκ ⊢
  obtain ⟨t, ht⟩ : ∃ t, t = B ^ 2 * s ^ 2 * V ^ 2 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = B ^ 2 * V ^ 2 * ((s * AP) ^ 2 / R ^ 2) := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hw1 : 1 ≤ W ^ 2 := by nlinarith only [hW]
  have hww : W ≤ W ^ 2 := by nlinarith only [hW]
  have hW0 : 0 ≤ W := by linarith only [hW]
  -- Short rows.
  have hc1 : (1 + logA) / L ≤ 2 := (div_le_iff₀ hL0).mpr hlogA
  have hX1 : 0 ≤ 1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2 * C ^ 2 * h0 := by positivity
  have hX2 : 1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2 * C ^ 2 * h0 ≤
      1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2 := by
    nlinarith only [hCh]
  have hT1 : (32 * B ^ 2 * s ^ 2 * V ^ 2 * (1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2 * C ^ 2 * h0)) *
      (1 + logA) / L ≤ t * (64 * (1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2)) := by
    calc _ = 32 * t * (1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2 * C ^ 2 * h0) * ((1 + logA) / L) := by
            rw [ht]; ring
      _ ≤ 32 * t * (1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2 * C ^ 2 * h0) * 2 :=
          mul_le_mul_of_nonneg_left hc1 (mul_nonneg (mul_nonneg (by norm_num) ht0) hX1)
      _ ≤ 32 * t * (1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2) * 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hX2 (mul_nonneg (by norm_num) ht0)) (by norm_num)
      _ = _ := by ring
  -- Middle rows.
  have hm1 : 1027 * W ^ 2 / R ≤ 1027 * W ^ 2 := div_le_self (by positivity) hR
  have hm2 : 576 * W * S * q0 ≤ 576 * W * S :=
    mul_le_of_le_one_right (mul_nonneg (mul_nonneg (by norm_num) hW0) hS) hq1
  have hT2 : 64 * B ^ 2 * s ^ 2 * V ^ 2 * (1027 * W ^ 2 / R + 576 * W * S * q0) ≤
      t * (64 * (1027 * W ^ 2 + 576 * W * S)) := by
    calc _ = t * (64 * (1027 * W ^ 2 / R + 576 * W * S * q0)) := by rw [ht]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hm1, hm2]) ht0
  -- Terminal rows.
  have hc3 : logD / L ≤ 2 := (div_le_iff₀ hL0).mpr hlogD
  have hT3 : 64 * B ^ 2 * s ^ 2 * V ^ 2 * W ^ 2 * S * logD / L ≤ t * (128 * W ^ 2 * S) := by
    calc _ = t * (64 * W ^ 2 * S) * (logD / L) := by rw [ht]; ring
      _ ≤ t * (64 * W ^ 2 * S) * 2 :=
          mul_le_mul_of_nonneg_left hc3 (mul_nonneg ht0 (by positivity))
      _ = _ := by ring
  -- Own towers.
  have hT4 : 256 * B ^ 2 * V ^ 2 * (s * AP) ^ 2 / R ^ 2 = 256 * Z := by rw [hZ]; ring
  -- Covariance.
  have hAL : 0 < A * L := mul_pos hA0 hL0
  have hY2 : Y ^ 2 ≤ 9 * W ^ 2 * L ^ 2 :=
    (pow_le_pow_left₀ hY0 hY 2).trans_eq (by ring)
  have hmain : m * C ^ 2 * Y ^ 2 ≤ 9 * W ^ 2 * (A * L) := by
    calc m * C ^ 2 * Y ^ 2 ≤ m * Q2 * (9 * W ^ 2 * L ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hC hm) hY2 (sq_nonneg _) (mul_nonneg hm hQ2.le)
      _ = 9 * W ^ 2 * ((m * Q2 * L) * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hL0.le) (by positivity)
  have hq : m * C ^ 2 * Y ^ 2 / (A * L) ≤ 9 * W ^ 2 := (div_le_iff₀ hAL).mpr hmain
  have hT5 : (64 * m * V ^ 2 * (2 * (2 * μ) ^ 2 + 2 * (2 * μ) * K) / μ ^ 2) *
      (s ^ 2 * C ^ 2 * B ^ 2 * Y ^ 2) / (A * L) ≤ t * (576 * (8 + 4 * k) * W ^ 2) := by
    calc _ = 64 * V ^ 2 * ((2 * (2 * μ) ^ 2 + 2 * (2 * μ) * K) / μ ^ 2) * (s ^ 2 * B ^ 2) *
            (m * C ^ 2 * Y ^ 2 / (A * L)) := by ring
      _ = 64 * V ^ 2 * (8 + 4 * k) * (s ^ 2 * B ^ 2) * (m * C ^ 2 * Y ^ 2 / (A * L)) := by rw [hκ]
      _ ≤ 64 * V ^ 2 * (8 + 4 * k) * (s ^ 2 * B ^ 2) * (9 * W ^ 2) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by rw [ht]; ring
  -- The constants.
  have hinner : 64 * (1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2) + 64 * (1027 * W ^ 2 + 576 * W * S) +
      128 * W ^ 2 * S + 576 * (8 + 4 * k) * W ^ 2 ≤
      (10 ^ 8 + 2304 * k) * (W ^ 2 * (1 + S) ^ 2) := by
    have ha : 0 ≤ W ^ 2 * S ^ 2 := by positivity
    have hb : 0 ≤ k * (W ^ 2 * S ^ 2) := mul_nonneg hk ha
    have he : 0 ≤ W ^ 2 * S := by positivity
    have hc : 0 ≤ k * (W ^ 2 * S) := mul_nonneg hk he
    have hd : 0 ≤ (W ^ 2 - W) * S := mul_nonneg (sub_nonneg.mpr hww) hS
    linarith only [ha, hb, hc, hd, he, hw1]
  have hZ2 : 256 * Z ≤ (10 ^ 8 + 2304 * k) * (W ^ 2 * Z) := by
    have h256 : 256 ≤ (10 ^ 8 + 2304 * k) * W ^ 2 := by
      have : 0 ≤ k * W ^ 2 := mul_nonneg hk (by positivity)
      linarith only [this, hw1]
    calc 256 * Z ≤ ((10 ^ 8 + 2304 * k) * W ^ 2) * Z := mul_le_mul_of_nonneg_right h256 hZ0
      _ = _ := by ring
  have hRHS : (10 ^ 8 + 2304 * k) *
      ((B * V * W) ^ 2 * (s ^ 2 * (1 + S) ^ 2 + (s * AP) ^ 2 / R ^ 2)) =
      t * ((10 ^ 8 + 2304 * k) * (W ^ 2 * (1 + S) ^ 2)) +
        (10 ^ 8 + 2304 * k) * (W ^ 2 * Z) := by
    rw [ht, hZ]; ring
  rw [hRHS]
  calc _ ≤ t * (64 * (1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2)) +
        t * (64 * (1027 * W ^ 2 + 576 * W * S)) + t * (128 * W ^ 2 * S) + 256 * Z +
        t * (576 * (8 + 4 * k) * W ^ 2) :=
        add_le_add (add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4.le) hT5
    _ = t * (64 * (1027 ^ 2 * W ^ 2 * S ^ 2 + 576 ^ 2) + 64 * (1027 * W ^ 2 + 576 * W * S) +
          128 * W ^ 2 * S + 576 * (8 + 4 * k) * W ^ 2) + 256 * Z := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hinner ht0) hZ2

/-- The cutoff geometry of the admissible range. -/
private theorem literal_scale_geometry {c : ℝ} (hc : 1 ≤ c) {N M Q : ℕ} (hQ : 8 ≤ Q) (hM : 0 < M)
    (hlog : 1 ≤ Real.log N)
    (hscale : c * Real.exp 1 * M * (Q : ℝ) ^ 5 * ⌈Real.log N⌉₊ ≤ N) :
    Q * Q ≤ literalScaleLow N M Q ∧ literalScaleLow N M Q ≤ literalScaleHigh c N Q ∧
      literalScaleHigh c N Q < N ∧
      (N : ℝ) ≤ (2 * (c * Real.exp 1 * (Q : ℝ) ^ 2)) * literalScaleHigh c N Q ∧
      Q ^ 2 ≤ literalMultiplierLower c N (literalScaleHigh c N Q) ∧
      Q ^ 3 ≤ literalMultiplierLower c N (literalScaleLow N M Q) ∧
      c * Real.exp 1 * (Q : ℝ) ^ 2 ≤ N ∧ c ≤ N ∧
      (M : ℝ) * (Q : ℝ) ^ 2 * Real.log N ≤ literalScaleLow N M Q := by
  have hc0 : 0 < c := by linarith only [hc]
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  obtain ⟨X, hX⟩ : ∃ X, X = c * Real.exp 1 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith only [hc, he1]
  have hX0 : 0 < X := by linarith only [hX1]
  have hcX : c ≤ X := by rw [hX]; nlinarith only [hc, he1]
  have hQ1 : 1 ≤ Q := by omega
  have hq8 : (8 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq1 : (1 : ℝ) ≤ Q := by linarith only [hq8]
  have hq0 : (0 : ℝ) < Q := by linarith only [hq8]
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hL0 : 0 < Real.log N := by linarith only [hlog]
  have hl : Real.log N ≤ (⌈Real.log N⌉₊ : ℝ) := Nat.le_ceil _
  have hl1 : (1 : ℝ) ≤ (⌈Real.log N⌉₊ : ℝ) := hlog.trans hl
  have hLn : 1 ≤ ⌈Real.log N⌉₊ := by exact_mod_cast hl1
  rw [← hX] at hscale
  obtain ⟨l, hld⟩ : ∃ l : ℝ, l = (⌈Real.log N⌉₊ : ℝ) := ⟨_, rfl⟩
  rw [← hld] at hscale hl hl1
  have hA : (literalScaleLow N M Q : ℝ) = (M : ℝ) * (Q : ℝ) ^ 2 * l := by
    rw [literalScaleLow, hld]
    push_cast
    ring
  have hq45 : (Q : ℝ) ^ 4 ≤ (Q : ℝ) ^ 5 := pow_le_pow_right₀ hq1 (by norm_num)
  have hq25 : (Q : ℝ) ^ 2 ≤ (Q : ℝ) ^ 5 := pow_le_pow_right₀ hq1 (by norm_num)
  have h4 : X * M * (Q : ℝ) ^ 4 * l ≤ N :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq45
      (mul_nonneg hX0.le (by positivity))) (by linarith only [hl1])).trans hscale
  have hXQ : X * (Q : ℝ) ^ 2 ≤ N := by
    have h1 : X * (Q : ℝ) ^ 2 * 1 * 1 ≤ X * (Q : ℝ) ^ 5 * M * l := by
      have hq' : X * (Q : ℝ) ^ 2 ≤ X * (Q : ℝ) ^ 5 := mul_le_mul_of_nonneg_left hq25 hX0.le
      exact mul_le_mul (mul_le_mul hq' hm1 zero_le_one (by positivity)) hl1 zero_le_one
        (by positivity)
    have h2 : X * (Q : ℝ) ^ 5 * M * l = X * M * (Q : ℝ) ^ 5 * l := by ring
    linarith only [h1, h2, hscale]
  have hbig : (1 : ℝ) < X * (Q : ℝ) ^ 2 := by nlinarith only [hX1, hq8]
  have hden : 0 < X * (Q : ℝ) ^ 2 := by linarith only [hbig]
  have hn0 : (0 : ℝ) < N := by linarith only [hXQ, hbig]
  have hAle : (literalScaleLow N M Q : ℝ) ≤ (N : ℝ) / (X * (Q : ℝ) ^ 2) := by
    rw [hA, le_div_iff₀ hden]
    calc (M : ℝ) * (Q : ℝ) ^ 2 * l * (X * (Q : ℝ) ^ 2) = X * M * (Q : ℝ) ^ 4 * l := by ring
      _ ≤ (N : ℝ) := h4
  have hJd : literalScaleHigh c N Q = ⌊(N : ℝ) / (X * (Q : ℝ) ^ 2)⌋₊ := by
    rw [literalScaleHigh, hX]
  have hAJ : literalScaleLow N M Q ≤ literalScaleHigh c N Q := by
    rw [hJd]; exact Nat.le_floor hAle
  have hJle : (literalScaleHigh c N Q : ℝ) ≤ (N : ℝ) / (X * (Q : ℝ) ^ 2) := by
    rw [hJd]; exact Nat.floor_le (div_nonneg hn0.le hden.le)
  have hA1 : 1 ≤ literalScaleLow N M Q := by
    rw [literalScaleLow]
    have := Nat.mul_pos (Nat.mul_pos hM (pow_pos hQ1 2)) hLn
    omega
  have hJ1 : 1 ≤ literalScaleHigh c N Q := hA1.trans hAJ
  have hJr : (1 : ℝ) ≤ literalScaleHigh c N Q := by exact_mod_cast hJ1
  have hJN : literalScaleHigh c N Q < N := by
    have : (literalScaleHigh c N Q : ℝ) < N := hJle.trans_lt (div_lt_self hn0 hbig)
    exact_mod_cast this
  have hDJ : (N : ℝ) ≤ (2 * (c * Real.exp 1 * (Q : ℝ) ^ 2)) * literalScaleHigh c N Q := by
    rw [← hX]
    have hlt : (N : ℝ) / (X * (Q : ℝ) ^ 2) < (literalScaleHigh c N Q : ℝ) + 1 := by
      rw [hJd]; exact Nat.lt_floor_add_one _
    have h2 : (N : ℝ) / (X * (Q : ℝ) ^ 2) ≤ 2 * (literalScaleHigh c N Q : ℝ) := by
      linarith only [hlt, hJr]
    have h3 := (div_le_iff₀ hden).mp h2
    calc (N : ℝ) ≤ 2 * (literalScaleHigh c N Q : ℝ) * (X * (Q : ℝ) ^ 2) := h3
      _ = _ := by ring
  have hH : Q ^ 2 ≤ literalMultiplierLower c N (literalScaleHigh c N Q) := by
    apply literalMultiplierLower_ge_sq hc0 hJ1
    rw [← hX]
    have h3 := (le_div_iff₀ hden).mp hJle
    calc X * (literalScaleHigh c N Q : ℝ) * (Q : ℝ) ^ 2 =
          (literalScaleHigh c N Q : ℝ) * (X * (Q : ℝ) ^ 2) := by ring
      _ ≤ (N : ℝ) := h3
  have hH3 : Q ^ 3 ≤ literalMultiplierLower c N (literalScaleLow N M Q) := by
    have hAr : (0 : ℝ) < literalScaleLow N M Q := by exact_mod_cast hA1
    have hd : 0 < c * Real.exp 1 * (literalScaleLow N M Q : ℝ) := by
      rw [← hX]; exact mul_pos hX0 hAr
    have h1 : (Q : ℝ) ^ 3 ≤ (N : ℝ) / (c * Real.exp 1 * (literalScaleLow N M Q : ℝ)) := by
      rw [le_div_iff₀ hd, ← hX, hA]
      calc (Q : ℝ) ^ 3 * (X * ((M : ℝ) * (Q : ℝ) ^ 2 * l)) = X * M * (Q : ℝ) ^ 5 * l := by ring
        _ ≤ (N : ℝ) := hscale
    have h2 := h1.trans (Nat.le_ceil _)
    change (Q : ℝ) ^ 3 ≤ (literalMultiplierLower c N (literalScaleLow N M Q) : ℝ) at h2
    exact_mod_cast h2
  have hQQ : Q * Q ≤ literalScaleLow N M Q := by
    rw [literalScaleLow]
    calc Q * Q = 1 * Q ^ 2 * 1 := by ring
      _ ≤ M * Q ^ 2 * ⌈Real.log N⌉₊ := Nat.mul_le_mul (Nat.mul_le_mul hM le_rfl) hLn
  refine ⟨hQQ, hAJ, hJN, hDJ, hH, hH3, ?_, ?_, ?_⟩
  · rw [← hX]; exact hXQ
  · exact (hcX.trans (le_mul_of_one_le_right hX0.le (by nlinarith only [hq8]))).trans hXQ
  · rw [hA]
    exact mul_le_mul_of_nonneg_left hl (by positivity)

/-- The size conditions of the literal rows in the admissible range. -/
private theorem literal_scale_basic {c : ℝ} (hc : 1 ≤ c) {N Q : ℕ} (hQ : 8 ≤ Q)
    (hXQ : c * Real.exp 1 * (Q : ℝ) ^ 2 ≤ N) (hBQ : linearPrimeStrip c ≤ Q) :
    linearPrimeStrip c ≤ N ∧ 2 * c * Real.exp 1 * linearPrimeStrip c ≤ N := by
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hX : 1 ≤ c * Real.exp 1 := by nlinarith only [hc, he1]
  have hq8 : (8 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : (linearPrimeStrip c : ℝ) ≤ Q := by exact_mod_cast hBQ
  have hB0 : (0 : ℝ) ≤ linearPrimeStrip c := Nat.cast_nonneg _
  have hqq : (Q : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith only [hq8]
  have h2B : 2 * (linearPrimeStrip c : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith only [hq8, hB]
  constructor
  · have : (linearPrimeStrip c : ℝ) ≤ N := by
      refine (hB.trans hqq).trans (le_trans ?_ hXQ)
      nlinarith only [hX, sq_nonneg (Q : ℝ)]
    exact_mod_cast this
  · calc 2 * c * Real.exp 1 * (linearPrimeStrip c : ℝ) =
          (c * Real.exp 1) * (2 * (linearPrimeStrip c : ℝ)) := by ring
      _ ≤ (c * Real.exp 1) * (Q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h2B (by linarith only [hX])
      _ ≤ N := hXQ

/-- **The scale law of the three ranges.** With the cutoffs `literalScaleLow`, `literalScaleHigh`, the
five literal costs are dominated by one expression. -/
theorem literalThreeRangeBound_scale_le {φ : ℝ → ℝ} (hmass : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 1 ≤ c) {N M R Q : ℕ} {P : Finset ℕ} {s V K : ℝ}
    (hK : 0 ≤ K) (hQ : 8 ≤ Q) (hM : 0 < M) (hR : 1 ≤ R) (hlog : 1 ≤ Real.log N)
    (hscale : c * Real.exp 1 * M * (Q : ℝ) ^ 5 * ⌈Real.log N⌉₊ ≤ N)
    (hBQ : linearPrimeStrip c ≤ Q) (hRP : ∀ p ∈ P, R < p) (hPQ : P.card ≤ Q) :
    literalThreeRangeBound φ c N M R (literalScaleLow N M Q) (literalScaleHigh c N Q) P s V K ≤
      (10 ^ 8 + 2304 * (K / ∫ u, φ u ^ 2)) *
        (((linearPrimeStrip c : ℝ) * V * literalMultiplierWidth c) ^ 2 *
          (s ^ 2 * (1 + ∑ p ∈ P, 1 / (p : ℝ)) ^ 2 +
            (s * ∑ p ∈ P, Real.log p / (p : ℝ)) ^ 2 / (R : ℝ) ^ 2)) := by
  have hc0 : 0 < c := by linarith only [hc]
  obtain ⟨hQQ, hAJ, hJN, hDJ, hH, hH3, hXQ, -, hAbig⟩ :=
    literal_scale_geometry hc hQ hM hlog hscale
  obtain ⟨hBN, -⟩ := literal_scale_basic hc hQ hXQ hBQ
  have hL0 : 0 < Real.log N := by linarith only [hlog]
  have hQ1 : 1 ≤ Q := by omega
  have hq8 : (8 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq1 : (1 : ℝ) ≤ Q := by linarith only [hq8]
  have hq0 : (0 : ℝ) < Q := by linarith only [hq8]
  have hA1 : 1 ≤ literalScaleLow N M Q := by
    have : 1 ≤ Q * Q := Nat.mul_pos hQ1 hQ1
    omega
  have hAr : (0 : ℝ) < literalScaleLow N M Q := by exact_mod_cast hA1
  have hN1 : 1 ≤ N := hA1.trans (hAJ.trans hJN.le)
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith only [this]
  have hlog2n : Real.log (2 * (N : ℝ)) ≤ 1 + Real.log N := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    linarith only [hlog2]
  have hexp := literalThreeRangeBound_explicit_le (M := M) (s := s) (V := V) hmass hc0 hK hA1 hAJ
    hJN.le hlog hR hQ1 hRP hH hDJ
  refine hexp.trans ?_
  have hW : 1 ≤ literalMultiplierWidth c := by
    have h1 := abs_nonneg (Real.log (2 * c * Real.exp 1))
    have h2 := mertensWindowConstant_nonneg
    unfold literalMultiplierWidth
    linarith only [h1, h2]
  have hS : 0 ≤ ∑ p ∈ P, 1 / (p : ℝ) := sum_nonneg fun p _ => by positivity
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hlogA : 1 + Real.log (literalScaleLow N M Q) ≤ 2 * Real.log N := by
    have hAN : (literalScaleLow N M Q : ℝ) ≤ N := by exact_mod_cast hAJ.trans hJN.le
    have := Real.log_le_log hAr hAN
    linarith only [this, hlog]
  have hd0 : 0 < 2 * (c * Real.exp 1 * (Q : ℝ) ^ 2) := by positivity
  have hlogD : Real.log (2 * (c * Real.exp 1 * (Q : ℝ) ^ 2)) ≤ 2 * Real.log N := by
    have h1 := Real.log_le_log hd0 (mul_le_mul_of_nonneg_left hXQ (by norm_num : (0 : ℝ) ≤ 2))
    linarith only [h1, hlog2n, hlog]
  have hNB : (0 : ℝ) < ((N + linearPrimeStrip c : ℕ) : ℝ) := by
    have : 0 < N + linearPrimeStrip c := by omega
    exact_mod_cast this
  have hNB2 : ((N + linearPrimeStrip c : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have : N + linearPrimeStrip c ≤ 2 * N := by omega
    exact_mod_cast this
  have hNB1 : (1 : ℝ) ≤ ((N + linearPrimeStrip c : ℕ) : ℝ) := by
    have : 1 ≤ N + linearPrimeStrip c := by omega
    exact_mod_cast this
  have hC0 := mertensWindowConstant_nonneg
  have hY0 : 0 ≤ Real.log (N + linearPrimeStrip c : ℕ) + mertensWindowConstant + 1 := by
    have := Real.log_nonneg hNB1
    linarith only [this, hC0]
  have hY : Real.log (N + linearPrimeStrip c : ℕ) + mertensWindowConstant + 1 ≤
      3 * literalMultiplierWidth c * Real.log N := by
    have h1 := (Real.log_le_log hNB hNB2).trans hlog2n
    have hWC : mertensWindowConstant + 1 ≤ literalMultiplierWidth c := by
      have h3 := abs_nonneg (Real.log (2 * c * Real.exp 1))
      unfold literalMultiplierWidth
      linarith only [h3]
    have h4 := mul_nonneg (sub_nonneg.mpr hW) (sub_nonneg.mpr hlog)
    nlinarith only [h1, hWC, h4, hW, hlog]
  have hC : (P.card : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hPQ) 2
  have hq1' : (Q : ℝ) ^ (-(7 / 8 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq1 (by norm_num)
  have hH3r : (Q : ℝ) ^ 3 ≤ (literalMultiplierLower c N (literalScaleLow N M Q) : ℝ) := by
    exact_mod_cast hH3
  have hq3 : (0 : ℝ) < (Q : ℝ) ^ 3 := by positivity
  have hlow : (0 : ℝ) < (literalMultiplierLower c N (literalScaleLow N M Q) : ℝ) :=
    hq3.trans_le hH3r
  have hCh : (P.card : ℝ) ^ 2 *
      (literalMultiplierLower c N (literalScaleLow N M Q) : ℝ) ^ (-(7 / 8 : ℝ)) ≤ 1 := by
    have h1 := Real.rpow_le_rpow_of_nonpos hq3 hH3r (by norm_num : -(7 / 8 : ℝ) ≤ 0)
    have h2 : ((Q : ℝ) ^ 3) ^ (-(7 / 8 : ℝ)) = (Q : ℝ) ^ (-(21 / 8 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
      norm_num
    have h3 : (Q : ℝ) ^ (-(21 / 8 : ℝ)) ≤ (Q : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    have h4 : (Q : ℝ) ^ (-(2 : ℝ)) = ((Q : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hq0.le, Real.rpow_two]
    have h5 : (literalMultiplierLower c N (literalScaleLow N M Q) : ℝ) ^ (-(7 / 8 : ℝ)) ≤
        ((Q : ℝ) ^ 2)⁻¹ := by
      rw [← h4]
      exact (h1.trans_eq h2).trans h3
    calc _ ≤ (Q : ℝ) ^ 2 * ((Q : ℝ) ^ 2)⁻¹ :=
          mul_le_mul hC h5 (Real.rpow_nonneg hlow.le _) (sq_nonneg _)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  exact literal_cost_algebra (Q2 := (Q : ℝ) ^ 2) hmass hK hlog hW hS hR1 hlogA hlogD hY0 hY
    (Nat.cast_nonneg M) (by positivity) hAbig hAr hC hq1'
    (Real.rpow_nonneg hlow.le _) hCh

/-- **Uniform scale domination.** The literal upward channel of a prime band, with any period and any
offset count in the admissible range, has the one scale law. -/
theorem exists_literal_upward_scale_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : ∀ u, 0 ≤ φ u) (hmass : 0 < ∫ u, φ u ^ 2) :
    ∃ p₀ : ℕ, ∃ K : ℝ, 8 ≤ p₀ ∧ 1 ≤ K ∧
      ∀ c : ℝ, 1 ≤ c → ∀ N M R Q : ℕ, p₀ ≤ R → linearPrimeStrip c ≤ R → R ≤ Q → 0 < M →
        1 ≤ Real.log N → c * Real.exp 1 * M * (Q : ℝ) ^ 5 * ⌈Real.log N⌉₊ ≤ N →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, R < p) → (∀ p ∈ P, p ≤ Q) →
        (∀ p ∈ P, M.Coprime p) →
        ∀ (G : ℕ → ℝ) (s V : ℝ), Function.Periodic G M → 0 ≤ V → (∀ j, |G j| ≤ V) →
        ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ •
            packetVector (fun j => G j * incidencePacket P (fun _ => s) j) N)‖ ^ 2 ≤
          K * (((linearPrimeStrip c : ℝ) * V * literalMultiplierWidth c) ^ 2 *
            (s ^ 2 * (1 + ∑ p ∈ P, 1 / (p : ℝ)) ^ 2 +
              (s * ∑ p ∈ P, Real.log p / (p : ℝ)) ^ 2 / (R : ℝ) ^ 2)) := by
  obtain ⟨p₀, K₀, hp₀, hK₀, h3⟩ := exists_literal_upward_three_range_bound hφ hsupp hφ0 hmass
  have hk : 0 ≤ K₀ / ∫ u, φ u ^ 2 := div_nonneg hK₀ hmass.le
  refine ⟨p₀, 10 ^ 8 + 2304 * (K₀ / ∫ u, φ u ^ 2), hp₀, by linarith only [hk], ?_⟩
  intro c hc N M R Q hp₀R hBR hRQ hM hlog hscale P hP hRP hPQ hMP G s V hG hV hGV
  have hc0 : 0 < c := by linarith only [hc]
  have hQ : 8 ≤ Q := hp₀.trans (hp₀R.trans hRQ)
  have hBQ : linearPrimeStrip c ≤ Q := hBR.trans hRQ
  have hR1 : 1 ≤ R := by omega
  obtain ⟨hQQ, hAJ, hJN, -, hH, -, hXQ, hcN, -⟩ := literal_scale_geometry hc hQ hM hlog hscale
  obtain ⟨hBN, hsep⟩ := literal_scale_basic hc hQ hXQ hBQ
  have hL0 : 0 < Real.log N := by linarith only [hlog]
  have hA2 : 2 ≤ literalScaleLow N M Q := by nlinarith only [hQQ, hQ]
  have hN1 : 1 ≤ N := by omega
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hwidth : c / N ≤ 1 := (div_le_one hn0).mpr hcN
  have hBA : 2 * linearPrimeStrip c ≤ literalScaleLow N M Q := by
    refine le_trans ?_ hQQ
    exact Nat.mul_le_mul (by omega) hBQ
  have hcard : P.card ≤ Q := by
    have hsub : P ⊆ Icc 1 Q := fun p hp =>
      mem_Icc.mpr ⟨(hP p hp).one_lt.le, hPQ p hp⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  have hpH : ∀ p ∈ P, p ^ 2 ≤ literalMultiplierLower c N (literalScaleHigh c N Q) := fun p hp =>
    (Nat.pow_le_pow_left (hPQ p hp) 2).trans hH
  exact (h3 c hc0 N M R _ _ hp₀R hBR hA2 hAJ hJN hM hL0 hwidth hBN hBA hsep P hP hRP hMP hpH
    G s V hG hV hGV).trans
    (literalThreeRangeBound_scale_le hmass hc hK₀ hQ hM hR1 hlog hscale hBQ hRP hcard)

/-- A prime band profile is bounded by the amplitude times the number of primes. -/
private theorem abs_incidencePacket_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (n : ℕ) :
    |incidencePacket P (fun _ => s) n| ≤ |s| * P.card := by
  unfold incidencePacket
  calc _ ≤ ∑ p ∈ P, |s * ((if p ∣ n then (1 : ℝ) else 0) - 1 / p)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ P, |s| * 1 := by
        refine sum_le_sum fun p hp => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
        have h1 : 1 / (p : ℝ) ≤ 1 := by
          rw [div_le_one (by linarith only [hp1])]
          exact hp1
        have h0 : 0 ≤ 1 / (p : ℝ) := by positivity
        rw [abs_le]
        split_ifs <;> constructor <;> linarith only [h0, h1]
    _ = _ := by
        rw [sum_const, nsmul_eq_mul, mul_one]
        ring

/-- **The whole band.** Every prime up to `Q` contributes: the primes above `R` coprime to the period by
the scale law, the remainder by absolute size. -/
theorem exists_literal_upward_full_band_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : ∀ u, 0 ≤ φ u) (hmass : 0 < ∫ u, φ u ^ 2) :
    ∃ p₀ : ℕ, ∃ K : ℝ, 8 ≤ p₀ ∧ 1 ≤ K ∧
      ∀ c : ℝ, 1 ≤ c → ∀ N M R Q : ℕ, p₀ ≤ R → linearPrimeStrip c ≤ R → R ≤ Q → 0 < M →
        1 ≤ Real.log N → c * Real.exp 1 * M * (Q : ℝ) ^ 5 * ⌈Real.log N⌉₊ ≤ N →
        ∀ (G : ℕ → ℝ) (s V : ℝ), Function.Periodic G M → 0 ≤ V → (∀ j, |G j| ≤ V) →
        ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector
            (fun j => G j * incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => s) j) N)‖ ≤
          K * ((linearPrimeStrip c : ℝ) * V * literalMultiplierWidth c) * |s| *
            (1 + (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + R + periodBandDivisors Q M +
              primePoleScale Q / R) := by
  obtain ⟨p₀, K, hp₀, hK, h⟩ := exists_literal_upward_scale_bound hφ hsupp hφ0 hmass
  refine ⟨p₀, K + 8, hp₀, by linarith only [hK], ?_⟩
  intro c hc N M R Q hp₀R hBR hRQ hM hlog hscale G s V hG hV hGV
  have hc0 : 0 < c := by linarith only [hc]
  have hQ : 8 ≤ Q := hp₀.trans (hp₀R.trans hRQ)
  have hBQ : linearPrimeStrip c ≤ Q := hBR.trans hRQ
  obtain ⟨hQQ, hAJ, hJN, -, -, -, hXQ, hcN, -⟩ := literal_scale_geometry hc hQ hM hlog hscale
  obtain ⟨hBN, hsep⟩ := literal_scale_basic hc hQ hXQ hBQ
  have hN1 : 1 ≤ N := by omega
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hwidth : c / N ≤ 1 := (div_le_one hn0).mpr hcN
  have hR0 : (0 : ℝ) < R := by
    have : 0 < R := by omega
    exact_mod_cast this
  classical
  obtain ⟨P, hPd⟩ : ∃ P, P = (Icc 1 Q).filter Nat.Prime := ⟨_, rfl⟩
  rw [← hPd]
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => by
    rw [hPd] at hp
    exact (mem_filter.mp hp).2
  have hPQ : ∀ p ∈ P, p ≤ Q := fun p hp => by
    rw [hPd] at hp
    exact (mem_Icc.mp (mem_filter.mp hp).1).2
  obtain ⟨P₁, hP₁⟩ : ∃ P₁, P₁ = P.filter fun p => R < p ∧ M.Coprime p := ⟨_, rfl⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, P₀ = P.filter fun p => ¬(R < p ∧ M.Coprime p) := ⟨_, rfl⟩
  have hsub₁ : P₁ ⊆ P := by rw [hP₁]; exact filter_subset _ _
  have hsub₀ : P₀ ⊆ P := by rw [hP₀]; exact filter_subset _ _
  -- The split of the profile.
  have hsplit : ∀ j, G j * incidencePacket P (fun _ => s) j -
      G j * incidencePacket P₀ (fun _ => s) j = G j * incidencePacket P₁ (fun _ => s) j := by
    intro j
    have hs := sum_filter_add_sum_filter_not P (fun p => R < p ∧ M.Coprime p)
      (fun p => s * ((if p ∣ j then (1 : ℝ) else 0) - 1 / p))
    rw [← hP₁, ← hP₀] at hs
    have he : incidencePacket P (fun _ => s) j = incidencePacket P₁ (fun _ => s) j +
        incidencePacket P₀ (fun _ => s) j := by
      unfold incidencePacket
      exact hs.symm
    rw [he]
    ring
  have hfun : (fun j => G j * incidencePacket P (fun _ => s) j -
      G j * incidencePacket P₀ (fun _ => s) j) =
      fun j => G j * incidencePacket P₁ (fun _ => s) j := funext hsplit
  have hsubU := upward_physical_packet_sub hsupp hc0 hwidth
    (fun j => G j * incidencePacket P (fun _ => s) j)
    (fun j => G j * incidencePacket P₀ (fun _ => s) j)
  rw [hfun] at hsubU
  -- The high band pays by the scale law.
  have hhigh := h c hc N M R Q hp₀R hBR hRQ hM hlog hscale P₁
    (fun p hp => hPprime p (hsub₁ hp))
    (fun p hp => by rw [hP₁] at hp; exact (mem_filter.mp hp).2.1)
    (fun p hp => hPQ p (hsub₁ hp))
    (fun p hp => by rw [hP₁] at hp; exact (mem_filter.mp hp).2.2)
    G s V hG hV hGV
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = (linearPrimeStrip c : ℝ) * V * literalMultiplierWidth c := ⟨_, rfl⟩
  have hW0 := literalMultiplierWidth_nonneg c
  have hY0 : 0 ≤ Y := by rw [hYd]; positivity
  rw [← hYd] at hhigh ⊢
  obtain ⟨S, hSd⟩ : ∃ S, S = ∑ p ∈ P, 1 / (p : ℝ) := ⟨_, rfl⟩
  have hS1 : ∑ p ∈ P₁, 1 / (p : ℝ) ≤ S := by
    rw [hSd]
    exact sum_le_sum_of_subset_of_nonneg hsub₁ fun _ _ _ => by positivity
  have hS1' : 0 ≤ ∑ p ∈ P₁, 1 / (p : ℝ) := sum_nonneg fun p _ => by positivity
  have hA1 : ∑ p ∈ P₁, Real.log p / (p : ℝ) ≤ primePoleScale Q := by
    rw [primePoleScale, ← hPd]
    refine sum_le_sum_of_subset_of_nonneg hsub₁ fun p _ _ => ?_
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hA1' : 0 ≤ ∑ p ∈ P₁, Real.log p / (p : ℝ) :=
    sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  obtain ⟨E₁, hE₁⟩ : ∃ E₁, E₁ = 1 + S + primePoleScale Q / R := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hS1'.trans hS1
  have hA0 : 0 ≤ primePoleScale Q := primePoleScale_nonneg Q
  have hE₁0 : 0 ≤ E₁ := by rw [hE₁]; positivity
  have hX : s ^ 2 * (1 + ∑ p ∈ P₁, 1 / (p : ℝ)) ^ 2 +
      (s * ∑ p ∈ P₁, Real.log p / (p : ℝ)) ^ 2 / (R : ℝ) ^ 2 ≤ (|s| * E₁) ^ 2 := by
    obtain ⟨a, ha⟩ : ∃ a, a = 1 + ∑ p ∈ P₁, 1 / (p : ℝ) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = (∑ p ∈ P₁, Real.log p / (p : ℝ)) / R := ⟨_, rfl⟩
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have hb0 : 0 ≤ b := by rw [hb]; positivity
    have hab : a + b ≤ E₁ := by
      have h1 : b ≤ primePoleScale Q / R := by
        rw [hb]; exact div_le_div_of_nonneg_right hA1 hR0.le
      rw [hE₁, ha]
      linarith only [h1, hS1]
    have hsq : a ^ 2 + b ^ 2 ≤ E₁ ^ 2 :=
      (by nlinarith only [mul_nonneg ha0 hb0] : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2).trans
        (pow_le_pow_left₀ (add_nonneg ha0 hb0) hab 2)
    calc _ = s ^ 2 * (a ^ 2 + b ^ 2) := by
          rw [ha, hb]
          field_simp
      _ ≤ s ^ 2 * E₁ ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg s)
      _ = _ := by rw [mul_pow, sq_abs]
  have hU₁ : ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ •
      packetVector (fun j => G j * incidencePacket P₁ (fun _ => s) j) N)‖ ≤ K * Y * (|s| * E₁) := by
    have hK0 : 0 ≤ K := by linarith only [hK]
    have hT0 : 0 ≤ K * Y * (|s| * E₁) := by positivity
    refine (sq_le_sq₀ (norm_nonneg _) hT0).mp ?_
    calc _ ≤ K * (Y ^ 2 * (|s| * E₁) ^ 2) :=
          hhigh.trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hX (sq_nonneg Y)) hK0)
      _ ≤ K * K * (Y ^ 2 * (|s| * E₁) ^ 2) :=
          mul_le_mul_of_nonneg_right (by nlinarith only [hK]) (by positivity)
      _ = _ := by ring
  -- The low band pays by absolute size.
  have hcard₀ : P₀.card ≤ R + periodBandDivisors Q M := by
    have hP0sub : P₀ ⊆ Icc 1 R ∪ (Icc 1 Q).filter fun p => p.Prime ∧ p ∣ M := by
      intro p hp
      rw [hP₀, mem_filter] at hp
      obtain ⟨hpP, hnot⟩ := hp
      have hpp := hPprime p hpP
      rw [mem_union]
      by_cases hpR : R < p
      · right
        have hnc : ¬ M.Coprime p := fun hcop => hnot ⟨hpR, hcop⟩
        rw [mem_filter, mem_Icc]
        refine ⟨⟨hpp.one_lt.le, hPQ p hpP⟩, hpp, ?_⟩
        by_contra hnd
        exact hnc (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hnd))
      · left
        rw [mem_Icc]
        exact ⟨hpp.one_lt.le, not_lt.mp hpR⟩
    calc P₀.card ≤ (Icc 1 R ∪ (Icc 1 Q).filter fun p => p.Prime ∧ p ∣ M).card := card_le_card hP0sub
      _ ≤ (Icc 1 R).card + ((Icc 1 Q).filter fun p => p.Prime ∧ p ∣ M).card := card_union_le _ _
      _ = _ := by rw [Nat.card_Icc, Nat.add_sub_cancel, periodBandDivisors]
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = (R : ℝ) + periodBandDivisors Q M := ⟨_, rfl⟩
  have hE₀0 : 0 ≤ E₀ := by rw [hE₀]; positivity
  have hcard₀r : (P₀.card : ℝ) ≤ E₀ := by
    rw [hE₀]
    exact_mod_cast hcard₀
  have hprofile : ∀ j, |G j * incidencePacket P₀ (fun _ => s) j| ≤ V * (|s| * E₀) := by
    intro j
    rw [abs_mul]
    refine mul_le_mul (hGV j) ?_ (abs_nonneg _) hV
    exact (abs_incidencePacket_le P₀ (fun p hp => hPprime p (hsub₀ hp)) s j).trans
      (mul_le_mul_of_nonneg_left hcard₀r (abs_nonneg s))
  have hU₀ := upward_physical_bounded_profile_norm_le hφ hsupp hmass hc0 hlog hwidth hBN hsep
    (fun j => G j * incidencePacket P₀ (fun _ => s) j)
    (mul_nonneg hV (mul_nonneg (abs_nonneg s) hE₀0)) hprofile
  have hU₀' : ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ •
      packetVector (fun j => G j * incidencePacket P₀ (fun _ => s) j) N)‖ ≤
      8 * Y * (|s| * E₀) := by
    refine hU₀.trans_eq ?_
    rw [hYd]
    unfold literalMultiplierWidth
    ring
  -- Assembly.
  have hsum : upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ •
      packetVector (fun j => G j * incidencePacket P (fun _ => s) j) N) =
      upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ •
        packetVector (fun j => G j * incidencePacket P₁ (fun _ => s) j) N) +
      upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ •
        packetVector (fun j => G j * incidencePacket P₀ (fun _ => s) j) N) := by
    rw [hsubU, sub_add_cancel]
  rw [hsum]
  refine (norm_add_le _ _).trans ((add_le_add hU₁ hU₀').trans ?_)
  have hfinal : (1 + S + (R : ℝ) + periodBandDivisors Q M + primePoleScale Q / R) = E₁ + E₀ := by
    rw [hE₁, hE₀]
    ring
  rw [← hSd, hfinal]
  have hs0 := abs_nonneg s
  have hK0 : 0 ≤ K := by linarith only [hK]
  calc K * Y * (|s| * E₁) + 8 * Y * (|s| * E₀) = Y * |s| * (K * E₁ + 8 * E₀) := by ring
    _ ≤ Y * |s| * ((K + 8) * (E₁ + E₀)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hY0 hs0)
        have h1 := mul_nonneg hK0 hE₀0
        have h2 : 0 ≤ E₁ := hE₁0
        nlinarith only [h1, h2]
    _ = _ := by ring

/-- `Σ_{p ≤ Q} 1/p` in the form of the sieve module. -/
private theorem band_recip_eq_mertensS (Q : ℕ) :
    (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) = _root_.RHTower.Sieve.mertensS Q := by
  unfold _root_.RHTower.Sieve.mertensS
  refine sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [mem_filter, mem_Icc, Nat.primesLE, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨by omega, h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨⟨h3.one_lt.le, by omega⟩, h3⟩

/-- **The channel law of a coherent band.** With amplitude `t / Σ_{p≤Q} log p / p`, the literal upward
channel is at most `K B V W |t| (1/√log Q + ω_Q(M)/log Q)`, uniformly in horizon, period, offsets and
amplitude. -/
theorem exists_literal_coherent_channel_law {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : ∀ u, 0 ≤ φ u) (hmass : 0 < ∫ u, φ u ^ 2) :
    ∃ Q₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ c : ℝ, 1 ≤ c → ∀ N M Q : ℕ, Q₀ ≤ Q →
        (linearPrimeStrip c : ℝ) ≤ Real.sqrt (Real.log Q) → 0 < M → 1 ≤ Real.log N →
        c * Real.exp 1 * M * (Q : ℝ) ^ 5 * ⌈Real.log N⌉₊ ≤ N →
        ∀ (G : ℕ → ℝ) (t V : ℝ), Function.Periodic G M → 0 ≤ V → (∀ j, |G j| ≤ V) →
        ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector
            (fun j => G j * incidencePacket ((Icc 1 Q).filter Nat.Prime)
              (fun _ => t / primePoleScale Q) j) N)‖ ≤
          K * ((linearPrimeStrip c : ℝ) * V * literalMultiplierWidth c) * |t| *
            (1 / Real.sqrt (Real.log Q) + periodBandDivisors Q M / Real.log Q) := by
  obtain ⟨p₀, K, hp₀, hK, h⟩ := exists_literal_upward_full_band_bound hφ hsupp hφ0 hmass
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = (Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail) :=
    ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, C₂ = |_root_.RHTower.Sieve.mertensSecondUpperConst| := ⟨_, rfl⟩
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; exact abs_nonneg _
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * |C₁| + (p₀ : ℝ) ^ 2 + 4 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by linarith only [hK]
  refine ⟨⌈Real.exp T⌉₊, K * (11 + 2 * C₂), by positivity, ?_⟩
  intro c hc N M Q hQ₀ hBy hM hlog hscale G t V hG hV hGV
  have hQexp : Real.exp T ≤ Q := Nat.ceil_le.mp hQ₀
  have hq0 : (0 : ℝ) < Q := (Real.exp_pos T).trans_le hQexp
  have hTlog : T ≤ Real.log Q := (Real.le_log_iff_exp_le hq0).mpr hQexp
  have hp0sq : (0 : ℝ) ≤ (p₀ : ℝ) ^ 2 := sq_nonneg _
  have hCa : 0 ≤ |C₁| := abs_nonneg _
  have hlogQ4 : 4 ≤ Real.log Q := by rw [hT] at hTlog; linarith only [hTlog, hp0sq, hCa]
  have hlogQ0 : 0 ≤ Real.log Q := by linarith only [hlogQ4]
  obtain ⟨y, hyd⟩ : ∃ y, y = Real.sqrt (Real.log Q) := ⟨_, rfl⟩
  rw [← hyd] at hBy ⊢
  have hy2 : y ^ 2 = Real.log Q := by rw [hyd]; exact Real.sq_sqrt hlogQ0
  have hy0 : 0 ≤ y := by rw [hyd]; exact Real.sqrt_nonneg _
  have hy2' : 2 ≤ y := by nlinarith only [hy2, hlogQ4, hy0]
  have hypos : 0 < y := by linarith only [hy2']
  have hp₀y : (p₀ : ℝ) ≤ y := by
    have h1 : (p₀ : ℝ) ^ 2 ≤ Real.log Q := by rw [hT] at hTlog; linarith only [hTlog, hCa]
    rw [hyd]
    exact (le_abs_self _).trans (Real.abs_le_sqrt h1)
  obtain ⟨R, hRd⟩ : ∃ R, R = ⌈y⌉₊ := ⟨_, rfl⟩
  have hRy : y ≤ R := by rw [hRd]; exact Nat.le_ceil y
  have hRy1 : (R : ℝ) < y + 1 := by rw [hRd]; exact Nat.ceil_lt_add_one hy0
  have hR0 : (0 : ℝ) < R := hypos.trans_le hRy
  have hp₀R : p₀ ≤ R := by exact_mod_cast hp₀y.trans hRy
  have hBR : linearPrimeStrip c ≤ R := by exact_mod_cast hBy.trans hRy
  have hRQ : R ≤ Q := by
    have h1 : Real.log Q + 1 ≤ Q := by
      have := Real.add_one_le_exp (Real.log Q)
      rwa [Real.exp_log hq0] at this
    have h2 : y ≤ Real.log Q := by rw [← hy2]; nlinarith only [hy2']
    have h3 : (R : ℝ) ≤ Q := by linarith only [hRy1, h1, h2]
    exact_mod_cast h3
  have hQ2 : 2 ≤ Q := hp₀.trans (hp₀R.trans hRQ) |>.trans' (by norm_num)
  have hband := h c hc N M R Q hp₀R hBR hRQ hM hlog hscale G (t / primePoleScale Q) V hG hV hGV
  refine hband.trans ?_
  -- The Mertens scales.
  have hBQ : y ^ 2 / 2 ≤ primePoleScale Q := by
    have h1 := CriticalScaleArithmeticRigidity.primePoleScale_logarithmic (Q := Q) (by omega)
    rw [← hC₁] at h1
    have h2 := (abs_le.mp h1).1
    have h3 := le_abs_self C₁
    rw [hT] at hTlog
    rw [hy2]
    linarith only [h2, h3, hTlog, hp0sq]
  have hBQ0 : 0 < primePoleScale Q := lt_of_lt_of_le (by positivity) hBQ
  have hS : (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ≤ 2 * y + C₂ := by
    rw [band_recip_eq_mertensS]
    have h1 := _root_.RHTower.Sieve.mertensS_le hQ2
    have h2 : _root_.RHTower.Sieve.logLog Q ≤ 2 * y := by
      have h3 : _root_.RHTower.Sieve.logLog Q = Real.log (Real.log Q) := rfl
      rw [h3, ← hy2, Real.log_pow]
      have h4 := Real.log_le_sub_one_of_pos hypos
      push_cast
      linarith only [h4]
    have h5 : _root_.RHTower.Sieve.mertensSecondUpperConst ≤ C₂ := by
      rw [hC₂]; exact le_abs_self _
    linarith only [h1, h2, h5]
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = periodBandDivisors Q M := ⟨_, rfl⟩
  have hω0 : 0 ≤ ω := by rw [hω]; positivity
  rw [← hω, ← hy2]
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = (linearPrimeStrip c : ℝ) * V * literalMultiplierWidth c := ⟨_, rfl⟩
  rw [← hYd]
  have hW0 := literalMultiplierWidth_nonneg c
  have hY0 : 0 ≤ Y := by rw [hYd]; positivity
  have hE : 1 + (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + (R : ℝ) + ω ≤
      (4 + C₂) * y + ω := by
    have h1 : C₂ ≤ C₂ * y := by nlinarith only [hC₂0, hy2']
    nlinarith only [hS, hRy1, h1, hy2']
  have hkey : (1 / primePoleScale Q) *
      (1 + (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + (R : ℝ) + ω +
        primePoleScale Q / R) ≤ (11 + 2 * C₂) * (1 / y + ω / y ^ 2) := by
    have hsplit : (1 / primePoleScale Q) *
        (1 + (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + (R : ℝ) + ω +
          primePoleScale Q / R) =
        (1 + (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + (R : ℝ) + ω) / primePoleScale Q +
          1 / R := by
      field_simp
    rw [hsplit]
    have hyy : 0 < y ^ 2 / 2 := by positivity
    have hE0 : 0 ≤ (4 + C₂) * y + ω := by positivity
    have h1 : (1 + (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + (R : ℝ) + ω) /
        primePoleScale Q ≤ ((4 + C₂) * y + ω) / (y ^ 2 / 2) :=
      div_le_div₀ hE0 hE hyy hBQ
    have h2 : (1 : ℝ) / R ≤ 1 / y := one_div_le_one_div_of_le hypos hRy
    have h3 : ((4 + C₂) * y + ω) / (y ^ 2 / 2) = (8 + 2 * C₂) * (1 / y) + 2 * (ω / y ^ 2) := by
      field_simp
      ring
    have h4 : 0 ≤ 1 / y := by positivity
    have h5 : 0 ≤ ω / y ^ 2 := by positivity
    have h6 : (11 + 2 * C₂) * (1 / y + ω / y ^ 2) =
        (11 + 2 * C₂) * (1 / y) + (11 + 2 * C₂) * (ω / y ^ 2) := by ring
    rw [h6]
    have h7 := mul_nonneg hC₂0 h4
    have h8 := mul_nonneg hC₂0 h5
    rw [h3] at h1
    nlinarith only [h1, h2, h4, h5, h7, h8]
  have hst : |t / primePoleScale Q| = |t| * (1 / primePoleScale Q) := by
    rw [abs_div, abs_of_pos hBQ0]
    ring
  rw [hst]
  have ht0 := abs_nonneg t
  calc K * Y * (|t| * (1 / primePoleScale Q)) *
        (1 + (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + (R : ℝ) + ω +
          primePoleScale Q / R) =
        K * Y * |t| * ((1 / primePoleScale Q) *
          (1 + (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + (R : ℝ) + ω +
            primePoleScale Q / R)) := by ring
    _ ≤ K * Y * |t| * ((11 + 2 * C₂) * (1 / y + ω / y ^ 2)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by ring

/-- The uncentered coherent packet is the band incidence profile. -/
private theorem coherent_packet_eq_incidence (Q : ℕ) (s : ℝ) (n : ℕ) :
    normalizedConductorPacket Q (primeOnly fun p => s * primePoleWitness p) n =
      incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => s) n := by
  rw [normalizedConductorPacket_primeOnly, incidencePacket]
  refine sum_congr rfl fun p hp => ?_
  rw [mul_assoc, primePoleWitness_mul_mode (mem_filter.mp hp).2]

/-- **The literal coherent charge.** The harmonically centered coherent charge has upward channel at most
`K B W |t| / √log Q`, at every horizon with `c e Q⁵ ⌈log N⌉ ≤ N` and every offset count `B ≤ √log Q`.
Harmonic centering costs `8 B W |η|` with `|η| ≤ 13 |t| / log N`. -/
theorem exists_literal_harmonicPrimeCharge_channel_law {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : ∀ u, 0 ≤ φ u) (hmass : 0 < ∫ u, φ u ^ 2) :
    ∃ Q₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ c : ℝ, 1 ≤ c → ∀ N Q : ℕ, Q₀ ≤ Q →
        (linearPrimeStrip c : ℝ) ≤ Real.sqrt (Real.log Q) → 1 ≤ Real.log N →
        c * Real.exp 1 * (Q : ℝ) ^ 5 * ⌈Real.log N⌉₊ ≤ N → ∀ t : ℝ,
        ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector
            (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) N)‖ ≤
          K * ((linearPrimeStrip c : ℝ) * literalMultiplierWidth c) * |t| /
            Real.sqrt (Real.log Q) := by
  obtain ⟨Q₀, K, hK, h⟩ := exists_literal_coherent_channel_law hφ hsupp hφ0 hmass
  refine ⟨max Q₀ 8, K + 104, by linarith only [hK], ?_⟩
  intro c hc N Q hQ₀ hBy hlog hscale t
  have hc0 : 0 < c := by linarith only [hc]
  have hQ8 : 8 ≤ Q := (le_max_right _ _).trans hQ₀
  have hQ1 : 1 ≤ Q := by omega
  have hq8 : (8 : ℝ) ≤ Q := by exact_mod_cast hQ8
  have hq0 : (0 : ℝ) < Q := by linarith only [hq8]
  have hlogQ1 : 1 ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le hq0]
    have := Real.exp_one_lt_d9
    linarith only [this, hq8]
  have hscale1 : c * Real.exp 1 * ((1 : ℕ) : ℝ) * (Q : ℝ) ^ 5 * ⌈Real.log N⌉₊ ≤ N := by
    simpa only [Nat.cast_one, mul_one] using hscale
  have hlaw := h c hc N 1 Q ((le_max_left _ _).trans hQ₀) hBy one_pos hlog hscale1
    (fun _ => 1) t 1 (fun _ => rfl) zero_le_one (fun _ => by simp)
  obtain ⟨y, hyd⟩ : ∃ y, y = Real.sqrt (Real.log Q) := ⟨_, rfl⟩
  rw [← hyd] at hBy hlaw ⊢
  have hy2 : y ^ 2 = Real.log Q := by
    rw [hyd]; exact Real.sq_sqrt (by linarith only [hlogQ1])
  have hy0 : 0 ≤ y := by rw [hyd]; exact Real.sqrt_nonneg _
  have hy1 : 1 ≤ y := by nlinarith only [hy2, hlogQ1, hy0]
  have hypos : 0 < y := by linarith only [hy1]
  have hyQ : y ≤ Real.log Q := by rw [← hy2]; nlinarith only [hy1]
  have hBQ : linearPrimeStrip c ≤ Q := by
    have h1 : (linearPrimeStrip c : ℝ) ≤ Q :=
      (hBy.trans hyQ).trans (Real.log_le_self hq0.le)
    exact_mod_cast h1
  obtain ⟨hQQ, hAJ, hJN, -, -, -, hXQ, hcN, -⟩ :=
    literal_scale_geometry hc hQ8 one_pos hlog hscale1
  obtain ⟨hBN, hsep⟩ := literal_scale_basic hc hQ8 hXQ hBQ
  have hN1 : 1 ≤ N := by omega
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hwidth : c / N ≤ 1 := (div_le_one hn0).mpr hcN
  have hL0 : 0 < Real.log N := by linarith only [hlog]
  have hLy : y ≤ Real.log N := by
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hX : 1 ≤ c * Real.exp 1 := by nlinarith only [hc, he1]
    have hqq : (Q : ℝ) ≤ c * Real.exp 1 * (Q : ℝ) ^ 2 := by nlinarith only [hX, hq8]
    exact hyQ.trans (Real.log_le_log hq0 (hqq.trans hXQ))
  have hBQ0 : 0 < primePoleScale Q := primePoleScale_pos (by omega)
  obtain ⟨s, hsd⟩ : ∃ s, s = t / primePoleScale Q := ⟨_, rfl⟩
  have hω : periodBandDivisors Q 1 = 0 := by
    rw [periodBandDivisors, card_eq_zero, filter_eq_empty_iff]
    rintro p - ⟨hp, hd⟩
    exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
  rw [hω, ← hsd] at hlaw
  simp only [one_mul, Nat.cast_zero, zero_div, add_zero, mul_one] at hlaw
  obtain ⟨η, hηd⟩ : ∃ η, η = SelectiveMultiscaleArithmeticPositivity.harmonicSum N
      (conductorHorizonProfile Q (primeOnly fun p => s * primePoleWitness p)) /
        SelectiveMultiscaleArithmeticPositivity.harmonicMass N := ⟨_, rfl⟩
  have hpack : normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) = fun n =>
      incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => s) n - η := by
    funext n
    rw [harmonicPrimeCharge_packet hQ1 N t n, hηd, hsd]
  have hsA : |s| * primePoleScale Q = |t| := by
    rw [hsd, abs_div, abs_of_pos hBQ0]
    field_simp
  have hlog2 : 1 + 8 / Real.log 2 ≤ 13 := by
    have h1 := Real.log_two_gt_d9
    have h2 : 0 < Real.log 2 := by linarith only [h1]
    have h3 : 8 / Real.log 2 ≤ 12 := by
      rw [div_le_iff₀ h2]
      linarith only [h1]
    linarith only [h3]
  have hη : |η| ≤ 13 * |t| / y := by
    have hsum : SelectiveMultiscaleArithmeticPositivity.harmonicSum N
        (conductorHorizonProfile Q (primeOnly fun p => s * primePoleWitness p)) =
        ∑ n ∈ Icc 1 N, (fun _ : ℕ => (1 : ℝ)) n *
          incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => s) n / (n : ℝ) := by
      unfold SelectiveMultiscaleArithmeticPositivity.harmonicSum conductorHorizonProfile
      refine sum_congr rfl fun n hn => ?_
      have hn0' : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [coherent_packet_eq_incidence, div_div, Real.mul_self_sqrt hn0'.le, one_mul]
    have hcenter := abs_unit_invariant_prime_band_center_le hN1 hL0 ((Icc 1 Q).filter Nat.Prime)
      (fun p hp => (mem_filter.mp hp).2) (fun _ => (1 : ℝ)) (fun _ _ _ => rfl) s zero_le_one
      (fun _ => by simp)
    rw [hηd, hsum]
    refine hcenter.trans ?_
    have ht0 := abs_nonneg t
    calc 1 * |s| * (1 + 8 / Real.log 2) *
          (∑ p ∈ (Icc 1 Q).filter Nat.Prime, Real.log p / (p : ℝ)) / Real.log N =
          (|s| * primePoleScale Q) * (1 + 8 / Real.log 2) / Real.log N := by
            rw [primePoleScale]; ring
      _ = |t| * (1 + 8 / Real.log 2) / Real.log N := by rw [hsA]
      _ ≤ |t| * 13 / Real.log N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog2 ht0) hL0.le
      _ ≤ |t| * 13 / y := div_le_div_of_nonneg_left (by positivity) hypos hLy
      _ = _ := by ring
  have hcenter := upward_physical_centering_error_le hφ hsupp hmass hc0 hlog hwidth hBN hsep
    (fun j => incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => s) j) η
  have hWd : |Real.log (2 * c * Real.exp 1)| + mertensWindowConstant + 1 =
      literalMultiplierWidth c := rfl
  rw [hWd] at hcenter
  rw [hpack]
  have hW0 := literalMultiplierWidth_nonneg c
  have hB0 : (0 : ℝ) ≤ linearPrimeStrip c := Nat.cast_nonneg _
  have ht0 := abs_nonneg t
  have hηcost : 8 * (linearPrimeStrip c : ℝ) * |η| * literalMultiplierWidth c ≤
      8 * (linearPrimeStrip c : ℝ) * (13 * |t| / y) * literalMultiplierWidth c :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη (by positivity)) hW0
  calc _ ≤ ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector
          (fun n => incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => s) n - η) N) -
        upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector
          (fun j => incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => s) j) N)‖ +
        ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector
          (fun j => incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => s) j) N)‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ 8 * (linearPrimeStrip c : ℝ) * (13 * |t| / y) * literalMultiplierWidth c +
        K * ((linearPrimeStrip c : ℝ) * literalMultiplierWidth c) * |t| * (1 / y) :=
        add_le_add (hcenter.trans hηcost) hlaw
    _ = _ := by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
